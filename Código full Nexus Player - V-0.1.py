#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Nexus Player - Versão 0.5
Otimização do Gerenciador de Duplicatas usando cache SQLite e agrupamento.
"""

import sys
import os
import re
import shutil
import logging
import random
import threading
import time
import sqlite3
import json
from pathlib import Path
from datetime import datetime
from difflib import SequenceMatcher
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial
from typing import Optional, List, Tuple, Dict, Any, Set

import yt_dlp
import mutagen.mp3

# ============================================================================
# PySide6 imports
# ============================================================================
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QTabWidget, QWidget, QVBoxLayout,
    QHBoxLayout, QLabel, QLineEdit, QPushButton, QListWidget,
    QListWidgetItem, QSlider, QFileDialog, QMessageBox,
    QTextEdit, QGroupBox, QSplitter, QProgressDialog, QDialog,
    QCheckBox, QDialogButtonBox, QTableWidget, QTableWidgetItem,
    QHeaderView
)
from PySide6.QtCore import Qt, QUrl, Slot, QTimer, QThread, Signal
from PySide6.QtMultimedia import QMediaPlayer, QAudioOutput
from PySide6.QtGui import QFont

# ============================================================================
# Configuração de Logging
# ============================================================================
LOG_FILE = Path(__file__).parent / "musica_app.log"
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(str(LOG_FILE), encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# ============================================================================
# PERSISTÊNCIA DE CONFIGURAÇÃO
# ============================================================================

CONFIG_FILE = Path(__file__).parent / "config.json"

def carregar_config() -> Dict[str, Any]:
    if CONFIG_FILE.exists():
        try:
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def salvar_config(config: Dict[str, Any]) -> None:
    try:
        with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=2)
    except Exception as e:
        logger.error(f"Erro ao salvar configuração: {e}")

# ============================================================================
# SISTEMA DE CACHE DE METADADOS
# ============================================================================

class MetadataCache:
    def __init__(self) -> None:
        self.db_path = Path(__file__).parent / "nexus_cache.db"
        self._lock = threading.Lock()
        self._init_db()

    def _init_db(self) -> None:
        with self._get_connection() as conn:
            conn.execute('''
                CREATE TABLE IF NOT EXISTS music_cache (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    path TEXT UNIQUE NOT NULL,
                    filename TEXT,
                    title TEXT,
                    artist TEXT,
                    album TEXT,
                    album_artist TEXT,
                    genre TEXT,
                    year TEXT,
                    track TEXT,
                    duration REAL,
                    bitrate INTEGER,
                    sample_rate INTEGER,
                    size INTEGER,
                    mtime REAL,
                    cover_path TEXT,
                    last_scan TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    favorite INTEGER DEFAULT 0,
                    play_count INTEGER DEFAULT 0,
                    last_played TIMESTAMP,
                    rating REAL DEFAULT 0.0
                )
            ''')
            colunas_existentes = [row[1] for row in conn.execute("PRAGMA table_info(music_cache)")]
            colunas_necessarias = {
                'album_artist': 'TEXT',
                'cover_path': 'TEXT',
                'last_scan': 'TIMESTAMP DEFAULT CURRENT_TIMESTAMP',
                'favorite': 'INTEGER DEFAULT 0',
                'play_count': 'INTEGER DEFAULT 0',
                'last_played': 'TIMESTAMP',
                'rating': 'REAL DEFAULT 0.0'
            }
            for col, tipo in colunas_necessarias.items():
                if col not in colunas_existentes:
                    logger.info(f"[Cache] Migração: adicionando coluna '{col}'")
                    try:
                        conn.execute(f"ALTER TABLE music_cache ADD COLUMN {col} {tipo}")
                    except sqlite3.OperationalError as e:
                        logger.warning(f"[Cache] Erro na migração da coluna '{col}': {e}")
            conn.commit()
            logger.info("[Cache] Banco de dados inicializado/migrado.")

    def _get_connection(self) -> sqlite3.Connection:
        conn = sqlite3.connect(str(self.db_path), timeout=10)
        conn.row_factory = sqlite3.Row
        return conn

    def _read_file_metadata(self, file_path: Path) -> Dict[str, Any]:
        try:
            stat = file_path.stat()
            size = stat.st_size
            mtime = stat.st_mtime
        except OSError as e:
            logger.error(f"[Cache] Erro ao ler stat de {file_path}: {e}")
            return {'duration': 0.0, 'size': 0, 'mtime': 0}

        metadata = {
            'title': '', 'artist': '', 'album': '', 'album_artist': '',
            'genre': '', 'year': '', 'track': '',
            'duration': 0.0, 'bitrate': 0, 'sample_rate': 0,
            'size': size, 'mtime': mtime
        }

        try:
            audio = mutagen.mp3.MP3(str(file_path))

            try:
                metadata['duration'] = audio.info.length
                metadata['bitrate'] = audio.info.bitrate
                metadata['sample_rate'] = audio.info.sample_rate
            except Exception as e:
                logger.warning(f"[Cache] Erro ao ler info de áudio de {file_path.name}: {e}")
                metadata['duration'] = 0.0

            def get_tag(frame_id: str) -> str:
                try:
                    frame = audio.get(frame_id)
                    if frame is None:
                        return ""
                    if hasattr(frame, 'text') and frame.text:
                        if isinstance(frame.text, list):
                            return '; '.join(str(t) for t in frame.text if t)
                        return str(frame.text)
                    return str(frame)
                except Exception:
                    return ""

            metadata['title'] = get_tag('TIT2')
            metadata['artist'] = get_tag('TPE1')
            metadata['album'] = get_tag('TALB')
            metadata['album_artist'] = get_tag('TPE2')
            metadata['genre'] = get_tag('TCON')
            metadata['year'] = get_tag('TDRC')
            track_raw = get_tag('TRCK')
            if track_raw and '/' in track_raw:
                metadata['track'] = track_raw.split('/')[0].strip()
            else:
                metadata['track'] = track_raw

            if metadata['duration'] <= 0:
                logger.warning(f"[Cache] Duração zero ou inválida: {file_path.name}")

        except mutagen.MutagenError as e:
            logger.error(f"[Cache] Erro Mutagen ao ler {file_path.name}: {e}")
            metadata['duration'] = 0.0
        except Exception as e:
            logger.error(f"[Cache] Erro inesperado ao ler {file_path.name}: {e}")
            metadata['duration'] = 0.0

        return metadata

    def get_or_update(self, file_path: Path, force: bool = False) -> Dict[str, Any]:
        with self._lock:
            str_path = str(file_path)
            with self._get_connection() as conn:
                if not force:
                    row = conn.execute("SELECT * FROM music_cache WHERE path = ?", (str_path,)).fetchone()
                else:
                    row = None

                if row:
                    try:
                        stat = file_path.stat()
                        mtime_atual = stat.st_mtime
                        size_atual = stat.st_size
                    except FileNotFoundError:
                        conn.execute("DELETE FROM music_cache WHERE path = ?", (str_path,))
                        conn.commit()
                        logger.info(f"[Cache] Arquivo removido detectado: {file_path.name}")
                        metadata = self._read_file_metadata(file_path)
                        self._save_metadata(conn, str_path, metadata)
                        return metadata

                    if row['mtime'] == mtime_atual and row['size'] == size_atual and not force:
                        logger.info(f"[Cache] HIT: {file_path.name}")
                        return dict(row)
                    else:
                        logger.info(f"[Cache] MISMATCH (alterado ou force): {file_path.name}")
                        metadata = self._read_file_metadata(file_path)
                        self._save_metadata(conn, str_path, metadata)
                        return metadata
                else:
                    logger.info(f"[Cache] MISS (novo): {file_path.name}")
                    metadata = self._read_file_metadata(file_path)
                    self._save_metadata(conn, str_path, metadata)
                    return metadata

    def _save_metadata(self, conn: sqlite3.Connection, path: str, metadata: Dict[str, Any]) -> None:
        now = datetime.now().isoformat()
        conn.execute('''
            INSERT OR REPLACE INTO music_cache (
                path, filename, title, artist, album, album_artist, genre, year, track,
                duration, bitrate, sample_rate, size, mtime, last_scan
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ''', (
            path,
            Path(path).name,
            metadata.get('title', ''),
            metadata.get('artist', ''),
            metadata.get('album', ''),
            metadata.get('album_artist', ''),
            metadata.get('genre', ''),
            metadata.get('year', ''),
            metadata.get('track', ''),
            metadata.get('duration', 0.0),
            metadata.get('bitrate', 0),
            metadata.get('sample_rate', 0),
            metadata.get('size', 0),
            metadata.get('mtime', 0),
            now
        ))
        conn.commit()
        logger.debug(f"[Cache] Salvo: {Path(path).name}")

    def cleanup(self, pasta: Path, arquivos_existentes: set) -> None:
        pasta_str = str(pasta)
        with self._lock:
            with self._get_connection() as conn:
                rows = conn.execute("SELECT path FROM music_cache WHERE path LIKE ?", (pasta_str + '%',)).fetchall()
                removidos = 0
                for row in rows:
                    file_path = Path(row['path'])
                    if file_path.name not in arquivos_existentes and not file_path.exists():
                        conn.execute("DELETE FROM music_cache WHERE path = ?", (row['path'],))
                        logger.info(f"[Cache] Removido (arquivo deletado): {file_path.name}")
                        removidos += 1
                if removidos:
                    conn.commit()
                    logger.info(f"[Cache] {removidos} registros removidos por arquivo inexistente.")

    def update_play_count(self, path: Path) -> None:
        with self._lock:
            with self._get_connection() as conn:
                conn.execute(
                    "UPDATE music_cache SET play_count = play_count + 1, last_played = ? WHERE path = ?",
                    (datetime.now().isoformat(), str(path))
                )
                conn.commit()

    # ========================================================================
    # MÉTODO OTIMIZADO PARA BUSCAR DADOS DO CACHE POR PASTA
    # ========================================================================
    def get_all_metadata_for_folder(self, pasta: Path) -> List[Dict[str, Any]]:
        """
        Retorna todos os registros do cache para uma determinada pasta.
        Útil para escaneamento de duplicatas.
        """
        pasta_str = str(pasta)
        with self._lock:
            with self._get_connection() as conn:
                rows = conn.execute(
                    "SELECT * FROM music_cache WHERE path LIKE ?",
                    (pasta_str + '%',)
                ).fetchall()
                return [dict(row) for row in rows]

# ============================================================================
# UTILITÁRIOS
# ============================================================================

PALAVRAS_VERSAO: List[str] = [
    'remix', 'live', 'acoustic', 'unplugged', 'version', 'edit', 'radio edit',
    'instrumental', 'a cappella', 'cover', 'medley', 'megamix', 'club mix',
    'extended', 'dub', 'reprise', 'intro', 'outro', 'interlude',
    'part', 'pt', 'chapter', 'act', 'movement', 'mov',
    'spring', 'summer', 'autumn', 'fall', 'winter',
    'i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x',
    '1', '2', '3', '4', '5', '6', '7', '8', '9', '10'
]

PALAVRAS_REMOVER: List[str] = [
    'official', 'music', 'video', 'audio', 'oficial', 'lyric', 'lyrics',
    'hd', 'hq', '4k', '1080p', '720p', 'vevo', 'ft', 'feat', 'featuring',
    'clipe', 'lançamento', 'release', 'new', 'exclusive', 'premiere',
    'ao vivo', 'live', 'dvd', 'cd', 'album', 'single', 'ep',
    'youtube', 'youtu', 'topic', 'pseudo', 'video'
]

def limpar_nome(nome: str) -> str:
    try:
        nome = Path(nome).stem
        for palavra in PALAVRAS_REMOVER:
            nome = re.sub(r'\b' + palavra + r'\b', '', nome, flags=re.IGNORECASE)
        nome = re.sub(r'\([^)]*\)', ' ', nome)
        nome = re.sub(r'\[[^\]]*\]', ' ', nome)
        nome = re.sub(r'[^a-zA-Z0-9\u00C0-\u024F\u0400-\u04FF\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF\s]', ' ', nome)
        nome = ' '.join(nome.lower().split())
        return nome
    except Exception as e:
        logger.error(f"Erro em limpar_nome('{nome}'): {e}")
        return nome

def extrair_artista_musica(nome_arquivo: str) -> Tuple[Optional[str], Optional[str]]:
    try:
        nome = Path(nome_arquivo).stem
        separadores = [' - ', ' – ', ' — ', ' | ', ' › ', ' : ', '; ']
        for sep in separadores:
            if sep in nome:
                partes = nome.split(sep, 1)
                if len(partes) == 2:
                    artista = limpar_nome(partes[0].strip())
                    musica = limpar_nome(partes[1].strip())
                    if not musica:
                        musica = limpar_nome(partes[0].strip())
                        artista = limpar_nome(partes[1].strip())
                    if artista and musica:
                        return artista, musica
        # Fallback: lista de artistas conhecidos
        artistas_conhecidos = [
            'metallica', 'engenheiros', 'vivaldi', 'djavan',
            'twenty one pilots', 'queen', 'beatles', 'rolling stones',
            'chico buarque', 'tim maia', 'legião urbana', 'exaltasamba',
            'calcinha preta', 'mastruz com leite', 'limão com mel',
            'forró da brucelose', 'cavalo de pau', 'desejo de menina',
            'charlie brown', 'guilherme arantes', 'reginaldo rossi',
            'molejo', 'art popular', 'leandro e leonardo', 'pantera',
            'avenged sevenfold', 'radio taxi', 'fernandinho', 'msm',
            'iwakura', 'lomaji', 'fabio lima', 'ulisses rocha',
            'metropolitan opera', 'antonio carlos jobim', 'tony jobim'
        ]
        nome_lower = nome.lower()
        for artista in artistas_conhecidos:
            if nome_lower.startswith(artista.lower()):
                resto = nome[len(artista):].strip()
                if resto:
                    return artista, resto
                else:
                    return artista, nome
        return None, None
    except Exception as e:
        logger.error(f"Erro em extrair_artista_musica('{nome_arquivo}'): {e}")
        return None, None

def extrair_palavras_chave(nome: str) -> List[str]:
    try:
        palavras = []
        nome_lower = nome.lower()
        for palavra in PALAVRAS_VERSAO:
            if palavra in nome_lower:
                palavras.append(palavra)
        return palavras
    except Exception as e:
        logger.error(f"Erro em extrair_palavras_chave('{nome}'): {e}")
        return []

def nomes_sao_parecidos(nome1: str, nome2: str) -> bool:
    try:
        artista1, musica1 = extrair_artista_musica(nome1)
        artista2, musica2 = extrair_artista_musica(nome2)
        if not artista1 or not musica1 or not artista2 or not musica2:
            nome1_limpo = limpar_nome(nome1)
            nome2_limpo = limpar_nome(nome2)
            similaridade = SequenceMatcher(None, nome1_limpo, nome2_limpo).ratio()
            if similaridade >= 0.95 and abs(len(nome1_limpo) - len(nome2_limpo)) <= 5:
                return True
            return False
        sim_artista = SequenceMatcher(None, artista1, artista2).ratio()
        sim_musica = SequenceMatcher(None, musica1, musica2).ratio()
        if sim_artista < 0.80 or sim_musica < 0.85:
            return False
        palavras1 = extrair_palavras_chave(musica1)
        palavras2 = extrair_palavras_chave(musica2)
        if set(palavras1) ^ set(palavras2):
            return False
        return True
    except Exception as e:
        logger.error(f"Erro em nomes_sao_parecidos: {e}")
        return False

def obter_tamanho_arquivo(caminho: Path) -> float:
    try:
        return caminho.stat().st_size / (1024 * 1024)
    except Exception as e:
        logger.error(f"Erro ao obter tamanho de '{caminho}': {e}")
        return 0.0

def verificar_duplicatas_avancado(pasta: Path, artista: str, musica: str) -> Tuple[bool, Optional[str]]:
    try:
        arquivos = [f.name for f in pasta.glob("*.mp3") if f.is_file()]
        nome_base = f"{artista} - {musica}"
        for arquivo in arquivos:
            if nomes_sao_parecidos(nome_base, arquivo):
                return True, arquivo
        return False, None
    except Exception as e:
        logger.error(f"Erro em verificar_duplicatas_avancado: {e}")
        return False, None

def localizar_ffmpeg() -> Optional[Path]:
    base_dir = Path(__file__).parent
    candidatos = [
        base_dir / "resources" / "ffmpeg" / "ffmpeg.exe",
        base_dir / "ffmpeg" / "ffmpeg.exe",
        base_dir / "ffmpeg" / "bin" / "ffmpeg.exe",
        base_dir / "ffmpeg.exe",
    ]
    for caminho in candidatos:
        if caminho.is_file() and os.access(str(caminho), os.X_OK):
            ffprobe = caminho.parent / "ffprobe.exe"
            if ffprobe.is_file() and os.access(str(ffprobe), os.X_OK):
                logger.info(f"FFmpeg encontrado na pasta local: {caminho}")
                return caminho
            else:
                logger.warning(f"FFmpeg encontrado, mas ffprobe.exe ausente em {caminho.parent}")
    ffmpeg_path = shutil.which('ffmpeg')
    if ffmpeg_path:
        ffprobe_path = shutil.which('ffprobe')
        if ffprobe_path:
            logger.info(f"FFmpeg encontrado no PATH: {ffmpeg_path}")
            return Path(ffmpeg_path)
        else:
            logger.warning("FFmpeg no PATH, mas ffprobe.exe não disponível.")
    logger.error("FFmpeg não encontrado.")
    return None

# ============================================================================
# JANELA DE CONFIRMAÇÃO DE DUPLICATAS
# ============================================================================

class DuplicateConfirmDialog(QDialog):
    def __init__(self, duplicatas: List[Tuple[str, str]], parent=None):
        super().__init__(parent)
        self.setWindowTitle("Arquivos duplicados encontrados")
        self.setMinimumSize(700, 400)
        self.setModal(True)

        layout = QVBoxLayout(self)

        lbl = QLabel(f"{len(duplicatas)} arquivo(s) já existe(m) na pasta destino. Deseja substituí-los?")
        layout.addWidget(lbl)

        self.table = QTableWidget()
        self.table.setColumnCount(2)
        self.table.setHorizontalHeaderLabels(["Arquivo origem", "Arquivo destino (existente)"])
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.table.setRowCount(len(duplicatas))

        self.checkboxes = []
        for i, (origem, destino) in enumerate(duplicatas):
            cb = QCheckBox()
            cb.setChecked(True)
            self.table.setCellWidget(i, 0, cb)
            self.table.setItem(i, 1, QTableWidgetItem(str(Path(destino).name)))
            self.checkboxes.append(cb)

        layout.addWidget(self.table)

        btn_box = QDialogButtonBox()
        btn_substituir = QPushButton("Substituir selecionados")
        btn_substituir.clicked.connect(lambda: self.done(QDialog.Accepted))
        btn_ignorar = QPushButton("Ignorar selecionados")
        btn_ignorar.clicked.connect(lambda: self.done(QDialog.Rejected))
        btn_substituir_todos = QPushButton("Substituir todos")
        btn_substituir_todos.clicked.connect(self._substituir_todos)
        btn_ignorar_todos = QPushButton("Ignorar todos")
        btn_ignorar_todos.clicked.connect(self._ignorar_todos)

        btn_box.addButton(btn_substituir_todos, QDialogButtonBox.ActionRole)
        btn_box.addButton(btn_ignorar_todos, QDialogButtonBox.ActionRole)
        btn_box.addButton(btn_substituir, QDialogButtonBox.ActionRole)
        btn_box.addButton(btn_ignorar, QDialogButtonBox.ActionRole)
        layout.addWidget(btn_box)

    def _substituir_todos(self):
        for cb in self.checkboxes:
            cb.setChecked(True)
        self.done(QDialog.Accepted)

    def _ignorar_todos(self):
        for cb in self.checkboxes:
            cb.setChecked(False)
        self.done(QDialog.Rejected)

    def get_selecao(self) -> List[bool]:
        return [cb.isChecked() for cb in self.checkboxes]

# ============================================================================
# THREAD PARA IMPORTAÇÃO
# ============================================================================

class ImportThread(QThread):
    progress = Signal(int, int)
    file_copied = Signal(str)
    error = Signal(str)
    finished = Signal(int)

    def __init__(self, origem_lista: List[Path], destino: Path):
        super().__init__()
        self.origem_lista = origem_lista
        self.destino = destino
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self) -> None:
        try:
            self.destino.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.error.emit(f"Erro ao criar pasta destino: {e}")
            self.finished.emit(0)
            return

        total = len(self.origem_lista)
        count = 0
        for i, origem in enumerate(self.origem_lista, 1):
            if self._cancel:
                break

            destino = self.destino / origem.name
            sucesso = False
            for tentativa in range(3):
                try:
                    shutil.copy2(str(origem), str(destino))
                    count += 1
                    self.file_copied.emit(origem.name)
                    sucesso = True
                    break
                except OSError as e:
                    if "WinError 32" in str(e) or "sendo usado" in str(e):
                        time.sleep(0.5)
                        continue
                    else:
                        self.error.emit(f"Erro ao copiar {origem.name}: {e}")
                        break
                except Exception as e:
                    self.error.emit(f"Erro ao copiar {origem.name}: {e}")
                    break
            if not sucesso:
                self.error.emit(f"❌ Falha ao copiar {origem.name} após 3 tentativas.")
            self.progress.emit(i, total)

        self.finished.emit(count)

# ============================================================================
# CLASSE PRINCIPAL
# ============================================================================

class MusicApp(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle("🎵 Nexus Player")
        self.setGeometry(100, 100, 1050, 750)
        self._running: bool = True

        self.cache = MetadataCache()
        logger.info("[Cache] Sistema de cache inicializado.")

        self.playlist: List[str] = []
        self.current_index: int = -1
        self.random_mode: bool = False
        self.loop_mode: bool = False
        self.historico: List[str] = []

        self.player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        self.player.setAudioOutput(self.audio_output)
        self.audio_output.setVolume(0.7)

        self.player.positionChanged.connect(self.on_position_changed)
        self.player.durationChanged.connect(self.on_duration_changed)
        self.player.playbackStateChanged.connect(self.on_playback_state_changed)
        self.player.mediaStatusChanged.connect(self.on_media_status_changed)
        self.player.errorOccurred.connect(self.on_player_error)

        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QVBoxLayout(central)

        self.tabs = QTabWidget()
        main_layout.addWidget(self.tabs)

        self.criar_aba_baixador()
        self.criar_aba_player()
        self.criar_aba_duplicatas()

        self.config = carregar_config()
        pasta_player = self.config.get("last_player_folder", str(Path.home() / "Músicas" / "Nexus"))
        self.player_folder_line.setText(pasta_player)

        Path(pasta_player).mkdir(parents=True, exist_ok=True)
        self.carregar_playlist(Path(pasta_player))

        self._pending_play = False

    # ========================================================================
    # TRATAMENTO DE ERRO DO PLAYER
    # ========================================================================

    @Slot(QMediaPlayer.Error)
    def on_player_error(self, error: QMediaPlayer.Error) -> None:
        if not self._running:
            return
        erro_msg = self.player.errorString()
        logger.error(f"Erro no player: {erro_msg} (código {error})")
        self.append_log(f"⚠️ Erro ao reproduzir: {erro_msg}")
        if self.current_index >= 0 and self.current_index < len(self.playlist):
            self.musica_proxima()

    # ========================================================================
    # MÉTODOS SEGUROS PARA THREADS
    # ========================================================================

    def append_log(self, texto: str) -> None:
        if not self._running:
            return
        QTimer.singleShot(0, partial(self._append_log_impl, texto))

    def _append_log_impl(self, texto: str) -> None:
        if self._running:
            self.log_text.append(texto)

    def append_log_dup(self, texto: str) -> None:
        if not self._running:
            return
        QTimer.singleShot(0, partial(self._append_log_dup_impl, texto))

    def _append_log_dup_impl(self, texto: str) -> None:
        if self._running:
            self.log_dup_text.append(texto)

    def show_message(self, tipo: str, titulo: str, mensagem: str) -> None:
        if not self._running:
            return
        QTimer.singleShot(0, partial(self._show_message_impl, tipo, titulo, mensagem))

    def _show_message_impl(self, tipo: str, titulo: str, mensagem: str) -> None:
        if not self._running:
            return
        if tipo == "info":
            QMessageBox.information(self, titulo, mensagem)
        elif tipo == "warning":
            QMessageBox.warning(self, titulo, mensagem)
        elif tipo == "critical":
            QMessageBox.critical(self, titulo, mensagem)
        elif tipo == "question":
            QMessageBox.question(self, titulo, mensagem)

    def atualizar_historico_ui(self) -> None:
        if not self._running:
            return
        QTimer.singleShot(0, self._atualizar_historico_impl)

    def _atualizar_historico_impl(self) -> None:
        if not self._running:
            return
        self.historico_list.clear()
        for item in reversed(self.historico):
            self.historico_list.addItem(item)

    # ========================================================================
    # CRIAÇÃO DAS ABAS
    # ========================================================================

    def criar_aba_baixador(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "🎵 Baixador")
        layout = QVBoxLayout(tab)

        lbl = QLabel("🎵 Baixador de Músicas")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout.addWidget(lbl)

        row = QHBoxLayout()
        row.addWidget(QLabel("🔗 URL do YouTube:"))
        self.url_entry = QLineEdit()
        self.url_entry.setText("https://youtu.be/MkEVPjwZbrY")
        row.addWidget(self.url_entry)
        layout.addLayout(row)

        row2 = QHBoxLayout()
        row2.addWidget(QLabel("📁 Pasta de destino:"))
        self.dest_folder_entry = QLineEdit()
        self.dest_folder_entry.setText(str(Path.home() / "Músicas" / "Nexus"))
        row2.addWidget(self.dest_folder_entry)
        btn_pasta = QPushButton("📂 Escolher")
        btn_pasta.clicked.connect(self.escolher_pasta_destino)
        row2.addWidget(btn_pasta)
        layout.addLayout(row2)

        row3 = QHBoxLayout()
        self.btn_baixar = QPushButton("⬇️ Baixar Música")
        self.btn_baixar.clicked.connect(self.baixar_musica_unica)
        row3.addWidget(self.btn_baixar)
        self.btn_baixar_lote = QPushButton("📂 Baixar Lote (Arquivo .txt)")
        self.btn_baixar_lote.clicked.connect(self.baixar_lote)
        row3.addWidget(self.btn_baixar_lote)
        layout.addLayout(row3)

        layout.addWidget(QLabel("📋 Log do download:"))
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        self.log_text.setFont(QFont("Consolas", 9))
        layout.addWidget(self.log_text)

        layout.addWidget(QLabel("📜 Histórico de downloads:"))
        row_hist = QHBoxLayout()
        self.historico_list = QListWidget()
        row_hist.addWidget(self.historico_list)
        btn_limpar = QPushButton("🗑️ Limpar")
        btn_limpar.clicked.connect(self.limpar_historico)
        row_hist.addWidget(btn_limpar)
        layout.addLayout(row_hist)

        footer = QLabel("⚡ Powered by yt-dlp | MP3 192 kbps | v0.5")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)

    def criar_aba_player(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "🎧 Player")
        layout = QVBoxLayout(tab)

        row1 = QHBoxLayout()
        row1.addWidget(QLabel("📁 Pasta:"))
        self.player_folder_line = QLineEdit()
        self.player_folder_line.setText(str(Path.home() / "Músicas" / "Nexus"))
        row1.addWidget(self.player_folder_line)
        btn_sel = QPushButton("📂")
        btn_sel.setFixedWidth(30)
        btn_sel.clicked.connect(self.escolher_pasta_player)
        row1.addWidget(btn_sel)
        btn_import = QPushButton("📥 Importar")
        btn_import.clicked.connect(self.importar_musicas)
        row1.addWidget(btn_import)
        btn_baixar_player = QPushButton("⬇️ Baixar")
        btn_baixar_player.clicked.connect(lambda: self.tabs.setCurrentIndex(0))
        row1.addWidget(btn_baixar_player)
        btn_recarregar = QPushButton("🔄 Recarregar")
        btn_recarregar.clicked.connect(self.recarregar_playlist)
        row1.addWidget(btn_recarregar)
        layout.addLayout(row1)

        row2 = QHBoxLayout()
        row2.addWidget(QLabel("🔍 Buscar:"))
        self.busca_entry = QLineEdit()
        self.busca_entry.textChanged.connect(self.buscar_musicas_player)
        row2.addWidget(self.busca_entry)
        layout.addLayout(row2)

        body = QHBoxLayout()
        group_lista = QGroupBox("📋 Playlist")
        vbox_lista = QVBoxLayout()
        self.playlist_widget = QListWidget()
        self.playlist_widget.itemDoubleClicked.connect(self.on_playlist_double_click)
        vbox_lista.addWidget(self.playlist_widget)
        group_lista.setLayout(vbox_lista)
        body.addWidget(group_lista, 1)

        group_ctrl = QGroupBox("🎛️ Controles")
        vbox_ctrl = QVBoxLayout()

        self.musica_atual_label = QLabel("⏹️ Nenhuma música")
        self.musica_atual_label.setFont(QFont("Arial", 11))
        vbox_ctrl.addWidget(self.musica_atual_label)

        row_btns = QHBoxLayout()
        self.btn_anterior = QPushButton("⏪")
        self.btn_anterior.clicked.connect(self.musica_anterior)
        row_btns.addWidget(self.btn_anterior)
        self.btn_play_pause = QPushButton("▶ Play")
        self.btn_play_pause.clicked.connect(self.play_pause)
        row_btns.addWidget(self.btn_play_pause)
        self.btn_stop = QPushButton("⏹️")
        self.btn_stop.clicked.connect(self.parar_musica)
        row_btns.addWidget(self.btn_stop)
        self.btn_proximo = QPushButton("⏩")
        self.btn_proximo.clicked.connect(self.musica_proxima)
        row_btns.addWidget(self.btn_proximo)
        vbox_ctrl.addLayout(row_btns)

        row_progress = QHBoxLayout()
        self.slider_progresso = QSlider(Qt.Horizontal)
        self.slider_progresso.setRange(0, 1000)
        self.slider_progresso.sliderMoved.connect(self.slider_moved)
        self.slider_progresso.sliderReleased.connect(self.slider_released)
        self.slider_progresso.setTracking(False)
        row_progress.addWidget(self.slider_progresso)
        self.tempo_label = QLabel("00:00 / 00:00")
        row_progress.addWidget(self.tempo_label)
        vbox_ctrl.addLayout(row_progress)

        row_vol = QHBoxLayout()
        row_vol.addWidget(QLabel("🔊"))
        self.slider_volume = QSlider(Qt.Horizontal)
        self.slider_volume.setRange(0, 100)
        self.slider_volume.setValue(70)
        self.slider_volume.valueChanged.connect(self.alterar_volume)
        row_vol.addWidget(self.slider_volume)
        row_vol.addWidget(QLabel("🔊"))
        vbox_ctrl.addLayout(row_vol)

        row_modos = QHBoxLayout()
        self.btn_aleatorio = QPushButton("🔀 Aleatório OFF")
        self.btn_aleatorio.setCheckable(True)
        self.btn_aleatorio.toggled.connect(self.toggle_aleatorio)
        row_modos.addWidget(self.btn_aleatorio)
        self.btn_continuo = QPushButton("🔁 Contínuo OFF")
        self.btn_continuo.setCheckable(True)
        self.btn_continuo.toggled.connect(self.toggle_continuo)
        row_modos.addWidget(self.btn_continuo)
        vbox_ctrl.addLayout(row_modos)

        vbox_ctrl.addStretch()
        group_ctrl.setLayout(vbox_ctrl)
        body.addWidget(group_ctrl, 1)

        layout.addLayout(body)
        self.slider_progresso.setEnabled(False)

    def criar_aba_duplicatas(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "🔍 Gerenciador de Duplicatas")
        layout = QVBoxLayout(tab)

        lbl = QLabel("🔍 Gerenciador de Duplicatas")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout.addWidget(lbl)

        row = QHBoxLayout()
        row.addWidget(QLabel("📁 Selecione a pasta:"))
        self.dup_folder_entry = QLineEdit()
        self.dup_folder_entry.setText(str(Path.home() / "Músicas" / "Nexus"))
        row.addWidget(self.dup_folder_entry)
        btn_dup_folder = QPushButton("📂")
        btn_dup_folder.clicked.connect(self.escolher_pasta_dup)
        row.addWidget(btn_dup_folder)
        self.btn_escanear = QPushButton("🔍 Escanear Duplicatas")
        self.btn_escanear.clicked.connect(self.escanear_duplicatas)
        row.addWidget(self.btn_escanear)
        layout.addLayout(row)

        splitter = QSplitter(Qt.Horizontal)
        self.log_dup_text = QTextEdit()
        self.log_dup_text.setReadOnly(True)
        self.log_dup_text.setFont(QFont("Consolas", 9))
        splitter.addWidget(self.log_dup_text)

        self.dup_list = QListWidget()
        splitter.addWidget(self.dup_list)
        layout.addWidget(splitter)

        btn_delete = QPushButton("🗑️ Deletar Selecionado")
        btn_delete.clicked.connect(self.deletar_duplicata_selecionada)
        layout.addWidget(btn_delete)

        footer = QLabel("⚡ Selecione um arquivo duplicado (com \"╰─\") e clique em Deletar")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)

    # ========================================================================
    # GERENCIAMENTO DA PLAYLIST
    # ========================================================================

    def recarregar_playlist(self) -> None:
        pasta = Path(self.player_folder_line.text().strip())
        if not pasta.is_dir():
            self.show_message("warning", "Aviso", "Pasta inválida ou não encontrada.")
            return
        self.carregar_playlist(pasta, force=True)

    def carregar_playlist(self, pasta: Path, force: bool = False) -> int:
        try:
            if not pasta.is_dir():
                logger.warning(f"Pasta inválida: {pasta}")
                self.playlist = []
                self.current_index = -1
                self._atualizar_lista_player_ui()
                self.slider_progresso.setEnabled(False)
                self.musica_atual_label.setText("⏹️ Nenhuma música")
                self.tempo_label.setText("00:00 / 00:00")
                return 0

            arquivos_validos = []
            arquivos_ignorados = []
            arquivos_nomes = set()

            for arquivo in pasta.glob("*.mp3"):
                if not arquivo.is_file():
                    continue
                if not os.access(str(arquivo), os.R_OK):
                    logger.warning(f"Sem permissão de leitura: {arquivo.name}")
                    arquivos_ignorados.append(arquivo.name)
                    continue

                metadata = self.cache.get_or_update(arquivo, force=force)

                if metadata.get('duration', 0) <= 0:
                    logger.warning(f"Arquivo ignorado (duração inválida): {arquivo.name}")
                    arquivos_ignorados.append(arquivo.name)
                    continue

                if not arquivo.name or arquivo.name.isspace():
                    arquivos_ignorados.append(arquivo.name)
                    continue

                arquivos_validos.append(arquivo.name)
                arquivos_nomes.add(arquivo.name)

            self.cache.cleanup(pasta, arquivos_nomes)

            self.playlist = sorted(arquivos_validos)
            self.current_index = -1
            self._atualizar_lista_player_ui()
            self.slider_progresso.setEnabled(False)
            self.musica_atual_label.setText("⏹️ Nenhuma música")
            self.tempo_label.setText("00:00 / 00:00")
            self.btn_play_pause.setText("▶ Play")

            logger.info(f"Playlist carregada: {len(self.playlist)} músicas (força={force})")
            if arquivos_ignorados:
                logger.warning(f"Arquivos ignorados: {len(arquivos_ignorados)} - {', '.join(arquivos_ignorados[:5])}{'...' if len(arquivos_ignorados) > 5 else ''}")
                self.append_log(f"⚠️ {len(arquivos_ignorados)} arquivo(s) ignorado(s) (ver log para detalhes).")

            self.config["last_player_folder"] = str(pasta)
            salvar_config(self.config)

            return len(self.playlist)
        except Exception as e:
            logger.error(f"Erro em carregar_playlist: {e}")
            self.playlist = []
            self.current_index = -1
            self._atualizar_lista_player_ui()
            return 0

    def _atualizar_lista_player_ui(self) -> None:
        self.playlist_widget.clear()
        for musica in self.playlist:
            self.playlist_widget.addItem(musica)
        if 0 <= self.current_index < len(self.playlist):
            self.playlist_widget.setCurrentRow(self.current_index)
        else:
            self.playlist_widget.setCurrentRow(-1)

    # ========================================================================
    # PLAYER - REPRODUÇÃO
    # ========================================================================

    def tocar_musica(self, indice: int) -> None:
        if not self.playlist:
            return
        if indice < 0 or indice >= len(self.playlist):
            logger.warning(f"Índice inválido: {indice}")
            return

        self.current_index = indice
        arquivo = self.playlist[indice]
        pasta = Path(self.player_folder_line.text().strip())
        caminho = pasta / arquivo

        if not caminho.exists():
            logger.warning(f"Arquivo não encontrado: {caminho}")
            self.append_log(f"⚠️ Arquivo não encontrado: {arquivo}")
            self.musica_proxima()
            return

        self.cache.update_play_count(caminho)

        self.player.stop()
        self._pending_play = True

        url = QUrl.fromLocalFile(str(caminho))
        self.player.setSource(url)

        self.musica_atual_label.setText(f"▶ {arquivo}")
        self.btn_play_pause.setText("⏸️ Pausar")
        self.playlist_widget.setCurrentRow(indice)
        self.playlist_widget.scrollToItem(self.playlist_widget.currentItem())

        QTimer.singleShot(2000, self._fallback_play)

    @Slot()
    def _fallback_play(self) -> None:
        if self._pending_play and self.player.playbackState() != QMediaPlayer.PlayingState:
            logger.warning("Fallback: iniciando reprodução por timeout.")
            self.player.play()
            self._pending_play = False

    @Slot(QMediaPlayer.MediaStatus)
    def on_media_status_changed(self, status: QMediaPlayer.MediaStatus) -> None:
        if status == QMediaPlayer.LoadedMedia:
            if self._pending_play:
                self.player.play()
                self._pending_play = False
        if status == QMediaPlayer.InvalidMedia:
            self.on_player_error(self.player.error())
        if status == QMediaPlayer.EndOfMedia:
            self.musica_proxima()

    def play_pause(self) -> None:
        if not self.playlist:
            return

        if self.player.playbackState() == QMediaPlayer.PlayingState:
            self.player.pause()
            self.btn_play_pause.setText("▶ Play")
            if self.current_index >= 0:
                self.musica_atual_label.setText(f"⏸️ {self.playlist[self.current_index]}")
            else:
                self.musica_atual_label.setText("⏸️ Pausado")
        else:
            if self.current_index < 0:
                self.tocar_musica(0)
            else:
                self.player.play()
                self.btn_play_pause.setText("⏸️ Pausar")
                if self.current_index >= 0:
                    self.musica_atual_label.setText(f"▶ {self.playlist[self.current_index]}")

    def parar_musica(self) -> None:
        self.player.stop()
        self.btn_play_pause.setText("▶ Play")
        self.slider_progresso.setValue(0)
        self.tempo_label.setText("00:00 / 00:00")
        self.musica_atual_label.setText("⏹️ Parado")
        self.slider_progresso.setEnabled(False)
        self._pending_play = False

    def musica_proxima(self) -> None:
        if not self.playlist:
            return

        if self.random_mode:
            if len(self.playlist) > 1:
                novo = random.randint(0, len(self.playlist)-1)
                while novo == self.current_index and len(self.playlist) > 1:
                    novo = random.randint(0, len(self.playlist)-1)
                self.tocar_musica(novo)
            else:
                self.tocar_musica(0)
        else:
            if self.current_index < len(self.playlist) - 1:
                self.tocar_musica(self.current_index + 1)
            elif self.loop_mode:
                self.tocar_musica(0)
            else:
                self.parar_musica()

    def musica_anterior(self) -> None:
        if not self.playlist:
            return
        if self.current_index > 0:
            self.tocar_musica(self.current_index - 1)
        else:
            self.tocar_musica(0)

    def alterar_volume(self, valor: int) -> None:
        self.audio_output.setVolume(valor / 100.0)

    # ========================================================================
    # SLOTS DO QMEDIAPLAYER
    # ========================================================================

    @Slot(int)
    def on_position_changed(self, pos: int) -> None:
        if not self.slider_progresso.isSliderDown():
            duracao = self.player.duration()
            if duracao > 0:
                self.slider_progresso.setMaximum(duracao)
                self.slider_progresso.setValue(pos)
                self.atualizar_label_tempo(pos, duracao)

    @Slot(int)
    def on_duration_changed(self, dur: int) -> None:
        if dur > 0:
            self.slider_progresso.setEnabled(True)
            self.slider_progresso.setMaximum(dur)
        else:
            self.slider_progresso.setEnabled(False)

    @Slot(QMediaPlayer.PlaybackState)
    def on_playback_state_changed(self, state: QMediaPlayer.PlaybackState) -> None:
        if state == QMediaPlayer.PlayingState:
            self.btn_play_pause.setText("⏸️ Pausar")
        elif state == QMediaPlayer.PausedState:
            self.btn_play_pause.setText("▶ Play")
        else:
            self.btn_play_pause.setText("▶ Play")

    # ========================================================================
    # SEEK
    # ========================================================================

    def slider_moved(self, pos: int) -> None:
        duracao = self.player.duration()
        if duracao > 0:
            self.atualizar_label_tempo(pos, duracao)

    def slider_released(self) -> None:
        pos = self.slider_progresso.value()
        self.player.setPosition(pos)

    def atualizar_label_tempo(self, pos: int, dur: int) -> None:
        if dur > 0:
            pos_seg = pos // 1000
            dur_seg = dur // 1000
            self.tempo_label.setText(
                f"{pos_seg//60:02d}:{pos_seg%60:02d} / {dur_seg//60:02d}:{dur_seg%60:02d}"
            )

    # ========================================================================
    # INTERAÇÃO COM A LISTA
    # ========================================================================

    def on_playlist_double_click(self, item: QListWidgetItem) -> None:
        nome_musica = item.text()
        try:
            idx = self.playlist.index(nome_musica)
        except ValueError:
            logger.warning(f"Música não encontrada na playlist: {nome_musica}")
            return
        self.tocar_musica(idx)

    def buscar_musicas_player(self) -> None:
        termo = self.busca_entry.text().strip().lower()
        self.playlist_widget.clear()
        if not termo:
            for musica in self.playlist:
                self.playlist_widget.addItem(musica)
        else:
            for musica in self.playlist:
                if termo in musica.lower():
                    self.playlist_widget.addItem(musica)

    # ========================================================================
    # MODOS
    # ========================================================================

    def toggle_aleatorio(self, checked: bool) -> None:
        self.random_mode = checked
        self.btn_aleatorio.setText("🔀 Aleatório ON" if checked else "🔀 Aleatório OFF")

    def toggle_continuo(self, checked: bool) -> None:
        self.loop_mode = checked
        self.btn_continuo.setText("🔁 Contínuo ON" if checked else "🔁 Contínuo OFF")

    # ========================================================================
    # DOWNLOADER
    # ========================================================================

    def _obter_opcoes_ytdlp(self, ffmpeg_path: Path, pasta: Path) -> Dict[str, Any]:
        return {
            'format': 'bestaudio/best',
            'postprocessors': [
                {'key': 'FFmpegExtractAudio', 'preferredcodec': 'mp3', 'preferredquality': '192'},
                {'key': 'FFmpegMetadata', 'add_metadata': True}
            ],
            'ffmpeg_location': str(ffmpeg_path),
            'outtmpl': str(pasta / '%(uploader)s - %(title)s.%(ext)s'),
            'quiet': True,
            'no_warnings': True,
            'writethumbnail': True,
        }

    def baixar_musica_unica(self) -> None:
        if not self._running:
            return

        url = self.url_entry.text().strip()
        if not url:
            self.show_message("warning", "Aviso", "Cole uma URL do YouTube primeiro!")
            return

        pasta_str = self.dest_folder_entry.text().strip()
        if not pasta_str:
            self.show_message("warning", "Aviso", "Escolha uma pasta para salvar!")
            return
        pasta = Path(pasta_str)

        ffmpeg_path = localizar_ffmpeg()
        if not ffmpeg_path:
            self.show_message(
                "critical",
                "FFmpeg não encontrado",
                "O FFmpeg não foi encontrado.\n\n"
                "Ele é necessário para converter os downloads para MP3.\n\n"
                "Você pode:\n"
                "• Colocar uma pasta chamada 'ffmpeg' na raiz do programa.\n"
                "ou\n"
                "• Instalar o FFmpeg no Windows e adicioná-lo ao PATH."
            )
            return

        self.append_log("🔍 Procurando informações da música...")
        self.btn_baixar.setEnabled(False)

        def download_task() -> None:
            try:
                ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
                with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                    info = ydl.extract_info(url, download=False)
                    nome_artista = info.get('uploader', 'Desconhecido')
                    titulo_musica = info.get('title', 'Sem título')

                    self.append_log(f"\n🎤 Artista: {nome_artista}")
                    self.append_log(f"🎵 Música: {titulo_musica}")
                    self.append_log("\n🔍 Verificando duplicatas...")

                    existe, arquivo_existente = verificar_duplicatas_avancado(pasta, nome_artista, titulo_musica)
                    if existe:
                        self.append_log(
                            f"⚠️ DUPLICATA ENCONTRADA!\n"
                            f"   Arquivo já existe: {arquivo_existente}\n"
                            f"⏭️ Download pulado!"
                        )
                        self.show_message("info", "Duplicata", f"Essa música já existe na pasta!\n{arquivo_existente}")
                        return

                    self.append_log("✅ Nenhuma duplicata encontrada!\n⏳ Baixando...")

                pasta.mkdir(parents=True, exist_ok=True)
                ydl_opts = self._obter_opcoes_ytdlp(ffmpeg_path, pasta)
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    ydl.download([url])

                self.adicionar_historico(nome_artista, titulo_musica)
                self.append_log("\n✅ Download concluído com sucesso!")
                self.show_message("info", "Sucesso", f"Música baixada com sucesso!\n{nome_artista} - {titulo_musica}")

                if Path(self.player_folder_line.text().strip()) == pasta:
                    QTimer.singleShot(0, partial(self.carregar_playlist, pasta, True))

            except Exception as e:
                logger.error(f"Erro no download único: {e}")
                self.append_log(f"\n❌ Erro: {e}")
                self.show_message("critical", "Erro", f"Ocorreu um erro:\n{e}")
            finally:
                self.btn_baixar.setEnabled(True)

        threading.Thread(target=download_task, daemon=True).start()

    def baixar_lote(self) -> None:
        if not self._running:
            return

        arquivo_path, _ = QFileDialog.getOpenFileName(
            self, "Selecione o arquivo com os links",
            "", "Arquivos de texto (*.txt);;Todos os arquivos (*.*)"
        )
        if not arquivo_path:
            return

        pasta_str = self.dest_folder_entry.text().strip()
        if not pasta_str:
            self.show_message("warning", "Aviso", "Escolha uma pasta para salvar!")
            return
        pasta = Path(pasta_str)

        ffmpeg_path = localizar_ffmpeg()
        if not ffmpeg_path:
            self.show_message(
                "critical",
                "FFmpeg não encontrado",
                "O FFmpeg não foi encontrado.\n\n"
                "Ele é necessário para converter os downloads para MP3.\n\n"
                "Você pode:\n"
                "• Colocar uma pasta chamada 'ffmpeg' na raiz do programa.\n"
                "ou\n"
                "• Instalar o FFmpeg no Windows e adicioná-lo ao PATH."
            )
            return

        try:
            with open(arquivo_path, 'r', encoding='utf-8') as f:
                links = [linha.strip() for linha in f if linha.strip() and not linha.startswith('#')]
        except Exception as e:
            logger.error(f"Erro ao ler arquivo de lote: {e}")
            self.show_message("critical", "Erro", f"Erro ao ler o arquivo:\n{e}")
            return

        if not links:
            self.show_message("warning", "Aviso", "Nenhum link encontrado no arquivo!")
            return

        self.append_log(f"📚 Encontrados {len(links)} links no arquivo!")
        self.append_log("🔍 Verificando duplicatas (pasta + lote)...\n")
        self.btn_baixar_lote.setEnabled(False)

        def download_lote_task() -> None:
            musicas_baixadas = []
            musicas_duplicadas = []
            nomes_lote = []

            try:
                arquivos_pasta = [f.name for f in pasta.glob("*.mp3") if f.is_file()]
                self.append_log(f"📁 {len(arquivos_pasta)} arquivos na pasta\n")
            except Exception as e:
                logger.error(f"Erro ao listar pasta: {e}")
                self.append_log("⚠️ Não foi possível ler a pasta\n")

            self.append_log("🔍 PASSO 1: Analisando e verificando duplicatas...\n")
            informacoes = []

            for i, url in enumerate(links, 1):
                if not self._running:
                    break
                try:
                    self.append_log(f"[{i}/{len(links)}] 🔍 Analisando...")
                    ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
                    with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                        info = ydl.extract_info(url, download=False)
                        nome_artista = info.get('uploader', 'Desconhecido')
                        titulo_musica = info.get('title', 'Sem título')

                        existe_na_pasta, arquivo_existente = verificar_duplicatas_avancado(pasta, nome_artista, titulo_musica)
                        if existe_na_pasta:
                            musicas_duplicadas.append(f"{nome_artista} - {titulo_musica}")
                            self.append_log(
                                f"   ⏭️ DUPLICATA NA PASTA: {nome_artista} - {titulo_musica}\n"
                                f"      (Arquivo: {arquivo_existente})\n"
                            )
                            continue

                        eh_duplicata_lote = False
                        for nome_existente in nomes_lote:
                            if nomes_sao_parecidos(titulo_musica, nome_existente):
                                eh_duplicata_lote = True
                                break

                        if eh_duplicata_lote:
                            musicas_duplicadas.append(f"{nome_artista} - {titulo_musica}")
                            self.append_log(
                                f"   ⏭️ DUPLICATA NO LOTE: {nome_artista} - {titulo_musica} "
                                f"(já está na lista, será pulada)\n"
                            )
                        else:
                            nomes_lote.append(titulo_musica)
                            informacoes.append((nome_artista, titulo_musica, url))
                            self.append_log(f"   ✅ {nome_artista} - {titulo_musica}\n")

                except Exception as e:
                    logger.error(f"Erro ao analisar link {url}: {e}")
                    self.append_log(f"   ❌ Erro: {e}\n")

            if not self._running:
                return

            if musicas_duplicadas:
                self.append_log(f"\n⚠️ {len(musicas_duplicadas)} duplicatas encontradas!\n")

            if not informacoes:
                self.append_log("❌ Nenhuma música nova para baixar.")
                self.show_message("warning", "Aviso", "Nenhuma música nova para baixar!")
                self.btn_baixar_lote.setEnabled(True)
                return

            pasta.mkdir(parents=True, exist_ok=True)

            self.append_log(
                f"\n📥 PASSO 2: Baixando {len(informacoes)} músicas com 3 threads paralelas...\n"
            )
            NUM_THREADS = 3
            musicas_com_erro = []
            ydl_opts_base = self._obter_opcoes_ytdlp(ffmpeg_path, pasta)

            def baixar_uma_musica(dados):
                nome_artista, titulo_musica, url = dados
                try:
                    with yt_dlp.YoutubeDL(ydl_opts_base) as ydl:
                        ydl.download([url])
                    return (nome_artista, titulo_musica, True, None)
                except Exception as e:
                    logger.error(f"Erro ao baixar {nome_artista} - {titulo_musica}: {e}")
                    return (nome_artista, titulo_musica, False, str(e))

            with ThreadPoolExecutor(max_workers=NUM_THREADS) as executor:
                futures = {executor.submit(baixar_uma_musica, dados): dados for dados in informacoes}
                for future in as_completed(futures):
                    if not self._running:
                        for f in futures:
                            f.cancel()
                        break
                    nome_artista, titulo_musica, sucesso, erro = future.result()
                    if sucesso:
                        musicas_baixadas.append((nome_artista, titulo_musica))
                        self.append_log(f"   ✅ {nome_artista} - {titulo_musica} baixada!")
                    else:
                        musicas_com_erro.append((nome_artista, titulo_musica, erro))
                        self.append_log(f"   ❌ Erro em {nome_artista} - {titulo_musica}: {erro}")

            if not self._running:
                return

            if musicas_baixadas:
                self.adicionar_bloco_historico(musicas_baixadas)
                self.append_log(f"\n🎉 Lote concluído!")
                self.append_log(f"   ✅ Baixadas: {len(musicas_baixadas)}")
                self.append_log(f"   ⏭️ Duplicatas: {len(musicas_duplicadas)}")
                if musicas_com_erro:
                    self.append_log(f"   ❌ Com erro: {len(musicas_com_erro)}")

                mensagem = f"{len(musicas_baixadas)} músicas baixadas!\n"
                if musicas_duplicadas:
                    mensagem += f"{len(musicas_duplicadas)} duplicatas puladas.\n"
                if musicas_com_erro:
                    mensagem += f"{len(musicas_com_erro)} com erro."
                self.show_message("info", "Sucesso", mensagem)

                if Path(self.player_folder_line.text().strip()) == pasta:
                    QTimer.singleShot(0, partial(self.carregar_playlist, pasta, True))
            else:
                self.append_log("\n❌ Nenhuma música foi baixada.")
                self.show_message("warning", "Aviso", "Nenhuma música foi baixada!")

            self.btn_baixar_lote.setEnabled(True)

        threading.Thread(target=download_lote_task, daemon=True).start()

    # ========================================================================
    # IMPORTAÇÃO
    # ========================================================================

    def importar_musicas(self) -> None:
        pasta_destino = Path(self.player_folder_line.text().strip())
        if not pasta_destino.is_dir():
            self.show_message("warning", "Aviso", "Selecione uma pasta de destino válida!")
            return

        if not os.access(str(pasta_destino), os.W_OK):
            self.show_message("warning", "Aviso", "Sem permissão de escrita na pasta destino!")
            return

        arquivos, _ = QFileDialog.getOpenFileNames(
            self, "Selecione as músicas para importar",
            "", "Arquivos MP3 (*.mp3);;Todos os arquivos (*.*)"
        )
        if not arquivos:
            return

        arquivos_para_copiar = []
        duplicatas = []
        for a in arquivos:
            origem = Path(a)
            destino = pasta_destino / origem.name
            if origem.resolve() == destino.resolve():
                self.append_log(f"⚠️ Arquivo já está na pasta destino: {origem.name}")
            elif destino.exists():
                duplicatas.append((str(origem), str(destino)))
                self.append_log(f"⚠️ Arquivo já existe na pasta destino: {origem.name} → {destino.name}")
            else:
                arquivos_para_copiar.append(origem)

        if duplicatas:
            dialog = DuplicateConfirmDialog(duplicatas, self)
            result = dialog.exec()
            if result == QDialog.Accepted:
                selecao = dialog.get_selecao()
                for i, (origem, destino) in enumerate(duplicatas):
                    if selecao[i]:
                        arquivos_para_copiar.append(Path(origem))
                        self.append_log(f"⏳ Substituindo: {Path(origem).name}")
                    else:
                        self.append_log(f"⏭️ Ignorando: {Path(origem).name}")
            else:
                self.append_log("⏭️ Todas as duplicatas serão ignoradas.")

        if not arquivos_para_copiar:
            self.show_message("info", "Importação", "Nenhum arquivo novo para importar.")
            return

        self.progress_dialog = QProgressDialog("Importando músicas...", "Cancelar", 0, len(arquivos_para_copiar), self)
        self.progress_dialog.setWindowTitle("Importação")
        self.progress_dialog.setModal(True)
        self.progress_dialog.setMinimumDuration(0)
        self.progress_dialog.setValue(0)

        self.import_thread = ImportThread(arquivos_para_copiar, pasta_destino)
        self.import_thread.progress.connect(self._update_import_progress)
        self.import_thread.file_copied.connect(lambda nome: self.append_log(f"📥 {nome}"))
        self.import_thread.error.connect(lambda msg: self.append_log(f"❌ {msg}"))
        self.import_thread.finished.connect(self._import_finished)
        self.import_thread.start()

        self.progress_dialog.canceled.connect(self._cancel_import)

        btn_import = self.sender()
        if btn_import:
            btn_import.setEnabled(False)

    def _update_import_progress(self, atual: int, total: int) -> None:
        if hasattr(self, 'progress_dialog') and self.progress_dialog:
            self.progress_dialog.setLabelText(f"Importando {atual} de {total}...")
            self.progress_dialog.setValue(atual)

    def _cancel_import(self) -> None:
        if hasattr(self, 'import_thread') and self.import_thread.isRunning():
            self.import_thread.cancel()
            self.import_thread.wait()
            self.append_log("⏹️ Importação cancelada pelo usuário.")

    def _import_finished(self, count: int) -> None:
        if hasattr(self, 'progress_dialog') and self.progress_dialog:
            self.progress_dialog.close()
        self.append_log(f"✅ Importação concluída: {count} arquivo(s) copiado(s).")
        for widget in self.findChildren(QPushButton):
            if widget.text() == "📥 Importar":
                widget.setEnabled(True)
        if count > 0:
            self.show_message("info", "Sucesso", f"{count} música(s) importada(s)!")
            pasta = Path(self.player_folder_line.text().strip())
            self.carregar_playlist(pasta, force=True)
        else:
            self.show_message("info", "Importação", "Nenhum arquivo foi importado.")

    # ========================================================================
    # HISTÓRICO
    # ========================================================================

    def adicionar_historico(self, nome_artista: str, titulo_musica: str, lote: bool = False) -> None:
        data_hora = datetime.now().strftime('%d/%m/%Y %H:%M')
        if lote:
            item = f'📦 {data_hora} - {nome_artista} - {titulo_musica}'
        else:
            item = f'{data_hora} - {nome_artista} - {titulo_musica}'
        self.historico.append(item)
        if len(self.historico) > 100:
            self.historico.pop(0)
        self.atualizar_historico_ui()

    def adicionar_bloco_historico(self, lista_musicas: List[Tuple[str, str]]) -> None:
        data_hora = datetime.now().strftime('%d/%m/%Y %H:%M')
        self.historico.append(f'🔵 {data_hora} - BLOCO DE {len(lista_musicas)} MÚSICAS')
        for artista, musica in lista_musicas:
            self.historico.append(f'   📌 {artista} - {musica}')
        if len(self.historico) > 100:
            self.historico = self.historico[-100:]
        self.atualizar_historico_ui()

    def limpar_historico(self) -> None:
        self.historico.clear()
        self.atualizar_historico_ui()
        self.show_message("info", "Histórico", "Histórico limpo com sucesso!")

    # ========================================================================
    # DUPLICATAS (VERSÃO OTIMIZADA)
    # ========================================================================

    def _atualizar_dup_list_ui(self, duplicatas: List[List[str]]) -> None:
        if not self._running:
            return
        self.dup_list.clear()
        if not duplicatas:
            self.dup_list.addItem("✅ Nenhuma duplicata encontrada!")
            return
        for grupo in duplicatas:
            self.dup_list.addItem(f"📁 {grupo[0]}")
            for arquivo in grupo[1:]:
                self.dup_list.addItem(f"   ╰─ {arquivo}")

    def escanear_duplicatas(self) -> None:
        if not self._running:
            return

        pasta_str = self.dup_folder_entry.text().strip()
        if not pasta_str:
            self.show_message("warning", "Aviso", "Selecione uma pasta primeiro!")
            return

        pasta = Path(pasta_str)
        if not pasta.exists():
            self.show_message("critical", "Erro", "Pasta não encontrada!")
            return

        self.append_log_dup(f"🔍 Escaneando pasta: {pasta}")
        self.append_log_dup("📁 Usando cache para acelerar...\n")
        self.btn_escanear.setEnabled(False)

        # --- Otimização: usar cache SQLite ---
        def scan_task_optimized() -> None:
            try:
                # Busca todos os metadados do cache para esta pasta
                registros = self.cache.get_all_metadata_for_folder(pasta)

                if not registros:
                    self.append_log_dup("⚠️ Nenhum arquivo MP3 encontrado no cache.")
                    self.append_log_dup("💡 Clique em 'Recarregar' na aba Player para popular o cache.")
                    QTimer.singleShot(0, partial(self._atualizar_dup_list_ui, []))
                    self.btn_escanear.setEnabled(True)
                    return

                total = len(registros)
                self.append_log_dup(f"📊 Carregados {total} registros do cache.")

                # --- Pré-processamento: extrair artista e título do cache ---
                # Se artista/título estiverem vazios, usar fallback do nome do arquivo
                musicas = []  # (nome_arquivo, artista_normalizado, titulo_normalizado)
                for reg in registros:
                    filename = reg.get('filename', '')
                    artist = reg.get('artist', '').strip()
                    title = reg.get('title', '').strip()
                    if not artist or not title:
                        # Fallback: extrair do nome do arquivo
                        art, tit = extrair_artista_musica(filename)
                        if not artist:
                            artist = art if art else ''
                        if not title:
                            title = tit if tit else ''
                    # Se ainda assim estiver vazio, usar o nome do arquivo como título
                    if not title:
                        title = Path(filename).stem
                    musicas.append({
                        'filename': filename,
                        'artist': artist,
                        'title': title,
                        'path': reg.get('path', '')
                    })

                # --- Agrupar por artista (normalizado) ---
                grupos = {}  # artista_normalizado -> lista de (nome_arquivo, título_normalizado, path)
                for m in musicas:
                    artista_raw = m['artist'].lower()
                    # Remover palavras comuns para normalizar melhor
                    artista_normalizado = limpar_nome(artista_raw)
                    if not artista_normalizado:
                        artista_normalizado = 'desconhecido'
                    if artista_normalizado not in grupos:
                        grupos[artista_normalizado] = []
                    # Normalizar título também
                    titulo_normalizado = limpar_nome(m['title'])
                    grupos[artista_normalizado].append({
                        'filename': m['filename'],
                        'title_raw': m['title'],
                        'title_norm': titulo_normalizado,
                        'path': m['path']
                    })

                # --- Dentro de cada grupo, comparar títulos ---
                duplicatas = []
                processados = set()

                for artista, lista in grupos.items():
                    n = len(lista)
                    # Se for 1, não há duplicata
                    if n < 2:
                        continue
                    # Para cada item, verificar com os seguintes
                    for i in range(n):
                        item1 = lista[i]
                        if item1['filename'] in processados:
                            continue
                        grupo_atual = [item1['filename']]
                        for j in range(i+1, n):
                            item2 = lista[j]
                            if item2['filename'] in processados:
                                continue
                            # Comparação rápida usando similaridade de strings (apenas títulos)
                            tit1 = item1['title_norm']
                            tit2 = item2['title_norm']
                            # Se um título estiver contido no outro, considerar duplicata
                            if tit1 == tit2 or (tit1 and tit2 and (tit1 in tit2 or tit2 in tit1)):
                                grupo_atual.append(item2['filename'])
                                processados.add(item2['filename'])
                            else:
                                # Usar SequenceMatcher apenas se a diferença for pequena
                                if abs(len(tit1) - len(tit2)) <= 10:
                                    sim = SequenceMatcher(None, tit1, tit2).ratio()
                                    if sim >= 0.85:
                                        grupo_atual.append(item2['filename'])
                                        processados.add(item2['filename'])
                        if len(grupo_atual) > 1:
                            duplicatas.append(grupo_atual)
                            processados.add(item1['filename'])

                # --- Exibe resultados ---
                if duplicatas:
                    self.append_log_dup(f"⚠️ Encontrados {len(duplicatas)} grupos de duplicatas!")
                    # Adiciona detalhes no log
                    for grupo in duplicatas:
                        self.append_log_dup("📌 GRUPO DE DUPLICATAS:")
                        for arquivo in grupo:
                            self.append_log_dup(f"   • {arquivo}")
                        self.append_log_dup("")
                    QTimer.singleShot(0, partial(self._atualizar_dup_list_ui, duplicatas))
                    self.show_message("info", "Concluído", f"Encontrados {len(duplicatas)} grupos de duplicatas!")
                else:
                    self.append_log_dup("✅ NENHUMA DUPLICATA ENCONTRADA!\n   Sua pasta está organizada!")
                    QTimer.singleShot(0, partial(self._atualizar_dup_list_ui, []))
                    self.show_message("info", "Concluído", "Nenhuma duplicata encontrada!")

            except Exception as e:
                logger.error(f"Erro em escanear_duplicatas: {e}")
                self.append_log_dup(f"\n❌ Erro: {e}")
                self.show_message("critical", "Erro", f"Ocorreu um erro:\n{e}")
            finally:
                self.btn_escanear.setEnabled(True)

        # Executa em thread separada para não bloquear a interface
        threading.Thread(target=scan_task_optimized, daemon=True).start()

    def deletar_duplicata_selecionada(self) -> None:
        selecao = self.dup_list.currentRow()
        if selecao < 0:
            self.show_message("warning", "Aviso", "Selecione um arquivo para deletar!")
            return
        item = self.dup_list.currentItem().text()
        if not item.startswith("   ╰─"):
            self.show_message("warning", "Aviso", "Selecione apenas arquivos duplicados (com \"╰─\")!")
            return
        nome_arquivo = item.replace("   ╰─ ", "").strip()
        pasta = Path(self.dup_folder_entry.text().strip())
        caminho = pasta / nome_arquivo
        if not caminho.exists():
            self.show_message("critical", "Erro", "Arquivo não encontrado!")
            return
        if self.show_message("question", "Confirmar", f"Tem certeza que deseja deletar:\n{nome_arquivo}") == QMessageBox.Yes:
            try:
                caminho.unlink()
                self.dup_list.takeItem(selecao)
                self.append_log_dup(f"🗑️ DELETADO: {nome_arquivo}")
                self.show_message("info", "Sucesso", f"Arquivo deletado:\n{nome_arquivo}")
                with self.cache._lock:
                    with self.cache._get_connection() as conn:
                        conn.execute("DELETE FROM music_cache WHERE path = ?", (str(caminho),))
                        conn.commit()
                if Path(self.player_folder_line.text().strip()) == pasta:
                    QTimer.singleShot(0, partial(self.carregar_playlist, pasta, True))
            except Exception as e:
                logger.error(f"Erro ao deletar duplicata: {e}")
                self.show_message("critical", "Erro", f"Erro ao deletar:\n{e}")

    # ========================================================================
    # SELEÇÃO DE PASTAS
    # ========================================================================

    def escolher_pasta_destino(self) -> None:
        pasta = QFileDialog.getExistingDirectory(self, "Escolha a pasta de destino")
        if pasta:
            self.dest_folder_entry.setText(pasta)

    def escolher_pasta_player(self) -> None:
        pasta = QFileDialog.getExistingDirectory(self, "Selecione a pasta de música")
        if pasta:
            self.player_folder_line.setText(pasta)
            self.config["last_player_folder"] = pasta
            salvar_config(self.config)

    def escolher_pasta_dup(self) -> None:
        pasta = QFileDialog.getExistingDirectory(self, "Selecione a pasta para escanear duplicatas")
        if pasta:
            self.dup_folder_entry.setText(pasta)

    # ========================================================================
    # ENCERRAMENTO
    # ========================================================================

    def closeEvent(self, event) -> None:
        self._running = False
        self.player.stop()
        self.player.setSource(QUrl())
        time.sleep(0.2)
        event.accept()

# ============================================================================
# PONTO DE ENTRADA
# ============================================================================

def main() -> None:
    app = QApplication(sys.argv)
    window = MusicApp()
    window.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()