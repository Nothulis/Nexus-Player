#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Nexus Player - Versão 0.18
- Detector de duplicatas aprimorado (ignora parênteses e lixo)
- Normalizador remove parênteses, colchetes e chaves
- Prévia mostra nome atual (verde se normalizado)
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
import webbrowser
from pathlib import Path
from datetime import datetime
from difflib import SequenceMatcher
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial
from typing import Optional, List, Tuple, Dict, Any

import yt_dlp
import mutagen.mp3

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QTabWidget, QWidget, QVBoxLayout,
    QHBoxLayout, QLabel, QLineEdit, QPushButton, QListWidget,
    QListWidgetItem, QSlider, QFileDialog, QMessageBox,
    QTextEdit, QGroupBox, QSplitter, QProgressDialog, QDialog,
    QCheckBox, QDialogButtonBox, QTableWidget, QTableWidgetItem,
    QHeaderView, QProgressBar, QComboBox
)
from PySide6.QtCore import Qt, QUrl, Slot, QTimer, QThread, Signal
from PySide6.QtMultimedia import QMediaPlayer, QAudioOutput
from PySide6.QtGui import QFont, QColor, QTextCharFormat, QTextCursor

# ============================================================================
# LOGGING
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
# CONFIGURAÇÃO
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
# UTILITÁRIOS
# ============================================================================
PALAVRAS_VERSAO = [
    'remix', 'live', 'acoustic', 'unplugged', 'version', 'edit', 'radio edit',
    'instrumental', 'a cappella', 'cover', 'medley', 'megamix', 'club mix',
    'extended', 'dub', 'reprise', 'intro', 'outro', 'interlude',
    'part', 'pt', 'chapter', 'act', 'movement', 'mov',
    'spring', 'summer', 'autumn', 'fall', 'winter',
    'i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x',
    '1', '2', '3', '4', '5', '6', '7', '8', '9', '10'
]

PALAVRAS_REMOVER = [
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

def limpar_nome_para_exibicao(nome: str) -> str:
    return limpar_nome(nome)

def extrair_artista_titulo_limpos(nome_arquivo: str) -> Tuple[str, str]:
    artista, titulo = extrair_artista_musica(nome_arquivo)
    if artista and titulo:
        return artista, titulo
    return "", limpar_nome(nome_arquivo)

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
# JANELA DE PRÉVIA DE NORMALIZAÇÃO (com nome atual em verde)
# ============================================================================

class NormalizePreviewDialog(QDialog):
    def __init__(self, alteracoes: List[Tuple[str, str]], parent=None):
        super().__init__(parent)
        self.setWindowTitle("Prévia de Normalização")
        self.setMinimumSize(900, 500)
        self.setModal(True)
        layout = QVBoxLayout(self)

        # Tabela com três colunas: Seleção, Nome atual (verde se já normalizado), Novo nome
        lbl = QLabel(f"{len(alteracoes)} arquivo(s) serão normalizados. Edite os nomes se necessário.")
        layout.addWidget(lbl)

        self.table = QTableWidget()
        self.table.setColumnCount(3)
        self.table.setHorizontalHeaderLabels(["Selecionar", "Nome atual", "Novo nome"])
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.table.setRowCount(len(alteracoes))

        self.checkboxes = []
        for i, (antigo, novo) in enumerate(alteracoes):
            # Checkbox
            cb = QCheckBox()
            cb.setChecked(True)
            self.table.setCellWidget(i, 0, cb)
            self.checkboxes.append(cb)

            # Nome atual
            item_atual = QTableWidgetItem(antigo)
            # Verifica se o nome já está normalizado
            if antigo == novo:
                item_atual.setForeground(QColor(0, 150, 0))  # verde
            self.table.setItem(i, 1, item_atual)

            # Novo nome (editável)
            item_novo = QTableWidgetItem(novo)
            item_novo.setFlags(item_novo.flags() | Qt.ItemIsEditable)
            self.table.setItem(i, 2, item_novo)

        layout.addWidget(self.table)

        btn_box = QDialogButtonBox()
        btn_confirmar = QPushButton("Confirmar Normalização")
        btn_confirmar.clicked.connect(self._confirmar)
        btn_cancelar = QPushButton("Cancelar")
        btn_cancelar.clicked.connect(self.reject)
        btn_selecionar_todos = QPushButton("Selecionar Todos")
        btn_selecionar_todos.clicked.connect(self._selecionar_todos)
        btn_desmarcar_todos = QPushButton("Desmarcar Todos")
        btn_desmarcar_todos.clicked.connect(self._desmarcar_todos)

        btn_box.addButton(btn_selecionar_todos, QDialogButtonBox.ActionRole)
        btn_box.addButton(btn_desmarcar_todos, QDialogButtonBox.ActionRole)
        btn_box.addButton(btn_confirmar, QDialogButtonBox.ActionRole)
        btn_box.addButton(btn_cancelar, QDialogButtonBox.ActionRole)
        layout.addWidget(btn_box)

        self._result = False

    def _selecionar_todos(self):
        for cb in self.checkboxes:
            cb.setChecked(True)

    def _desmarcar_todos(self):
        for cb in self.checkboxes:
            cb.setChecked(False)

    def _confirmar(self):
        self._result = True
        self.accept()

    def get_selecao(self) -> List[bool]:
        return [cb.isChecked() for cb in self.checkboxes]

# ============================================================================
# WIDGET DE LOG RETRÁTIL
# ============================================================================

class CollapsibleLog(QWidget):
    def __init__(self, titulo: str = "📋 Log", parent=None):
        super().__init__(parent)
        self._expanded = False
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        self.btn_toggle = QPushButton(f"▶ {titulo}")
        self.btn_toggle.setCheckable(True)
        self.btn_toggle.setChecked(False)
        self.btn_toggle.clicked.connect(self.toggle_log)
        layout.addWidget(self.btn_toggle)
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        self.log_text.setFont(QFont("Consolas", 8))
        self.log_text.setMaximumHeight(0)
        self.log_text.setVisible(False)
        layout.addWidget(self.log_text)

    def toggle_log(self):
        self._expanded = not self._expanded
        if self._expanded:
            self.log_text.setVisible(True)
            self.log_text.setMaximumHeight(200)
            self.btn_toggle.setText(f"▼ {self.btn_toggle.text()[2:]}")
        else:
            self.log_text.setVisible(False)
            self.log_text.setMaximumHeight(0)
            self.btn_toggle.setText(f"▶ {self.btn_toggle.text()[2:]}")

    def append_log(self, texto: str, tipo: str = "INFO"):
        cores = {
            "INFO": QColor(0, 0, 0),
            "WARNING": QColor(200, 150, 0),
            "ERROR": QColor(200, 0, 0),
            "SUCCESS": QColor(0, 150, 0)
        }
        cor = cores.get(tipo, QColor(0, 0, 0))
        fmt = QTextCharFormat()
        fmt.setForeground(cor)
        cursor = self.log_text.textCursor()
        cursor.movePosition(QTextCursor.End)
        self.log_text.setTextCursor(cursor)
        self.log_text.insertPlainText(f"[{datetime.now().strftime('%H:%M:%S')}] {texto}\n")

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

    def get_all_metadata_for_folder(self, pasta: Path, limpar_orfãos: bool = True) -> List[Dict[str, Any]]:
        pasta_str = str(pasta)
        with self._lock:
            with self._get_connection() as conn:
                rows = conn.execute(
                    "SELECT * FROM music_cache WHERE path LIKE ?",
                    (pasta_str + '%',)
                ).fetchall()
                registros = []
                orfaos = []
                for row in rows:
                    file_path = Path(row['path'])
                    if not file_path.exists():
                        orfaos.append(row['path'])
                        logger.info(f"[Cache] Registro órfão detectado: {file_path.name}")
                    else:
                        registros.append(dict(row))
                if limpar_orfãos and orfaos:
                    conn.executemany("DELETE FROM music_cache WHERE path = ?", [(p,) for p in orfaos])
                    conn.commit()
                    logger.info(f"[Cache] {len(orfaos)} registros órfãos removidos.")
                return registros

    def update_file_path(self, old_path: str, new_path: str) -> None:
        with self._lock:
            with self._get_connection() as conn:
                conn.execute("UPDATE music_cache SET path = ?, filename = ? WHERE path = ?",
                             (new_path, Path(new_path).name, old_path))
                conn.commit()

# ============================================================================
# SISTEMA INTELIGENTE DE NORMALIZAÇÃO (APRIMORADO)
# ============================================================================

class LibraryNormalizer:
    _instance = None
    _rules = None
    _compiled_patterns = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._load_rules()
        return cls._instance

    def _load_rules(self) -> None:
        rules_file = Path(__file__).parent / "normalizer_rules.json"
        default_rules = {
            "remove": [
                "official", "official video", "official music video", "official audio",
                "official visualizer", "official mv", "official clip", "official hd",
                "music video", "video oficial", "clipe oficial", "vídeo oficial",
                "lyrics", "lyric video", "lyrics video", "with lyrics", "legendado",
                "legendado pt-br", "tradução", "traduzido", "sub español", "sub english",
                "sub pt-br", "visualizer", "audio", "audio oficial", "hq", "hd",
                "full hd", "4k", "8k", "60fps", "1080p", "720p", "480p", "1440p", "2160p",
                "tiktok version", "tiktok audio", "tiktok edit", "youtube", "youtube version",
                "vevo", "topic", "stereo", "mono", "high quality", "best quality",
                "new version", "clean version", "dirty version", "explicit version",
                "uncensored", "free download", "download", "mp3", "lossless", "hq audio",
                "cd quality", "ultra hd", "audio rip", "vinyl rip", "remux", "mirror",
                "reupload", "fan made", "fanmade", "cover art", "performance",
                "performance video", "premiere", "premiere video", "clip oficial",
                "new upload", "full song", "complete song", "lyrics on screen", "audio only",
                "topic", "vevo", "official", "audio", "video", "music", "hd", "hq"
            ],
            "replace": {
                "feat": "ft.",
                "Feat": "ft.",
                "Feat.": "ft.",
                "FEAT": "ft.",
                "featuring": "ft.",
                "Featuring": "ft."
            },
            "keep": [
                "remix", "extended mix", "radio edit", "club mix", "vip mix",
                "bootleg", "mashup", "edit", "acoustic", "acoustic version",
                "live", "live version", "orchestra", "orchestral", "piano version",
                "instrumental", "karaoke", "remastered", "remastered 2023",
                "anniversary edition", "deluxe", "demo", "unplugged", "version",
                "original mix", "original version", "rework", "reimagined",
                "revisited", "lo-fi", "lofi", "nightcore", "slowed", "slowed + reverb",
                "reverb", "speed up", "sped up", "bass boosted", "8d audio",
                "10d audio", "surround", "dubstep remix", "trap remix", "house remix",
                "techno remix", "future bass remix", "hardstyle remix", "synthwave remix",
                "phonk", "brazilian phonk", "funk remix", "pagode version",
                "sertanejo version", "acústico", "ao vivo", "live at ...", "ost",
                "soundtrack", "theme", "opening", "ending"
            ],
            "invalid_characters": ["<", ">", ":", "\"", "/", "\\", "|", "?", "*"],
            "duplicate_ignore": [
                "official", "video", "music", "audio", "hd", "hq", "full", "song",
                "version", "clip", "visualizer", "lyrics", "live", "vevo", "topic",
                "remix", "edit", "acoustic", "instrumental", "karaoke", "demo",
                "unplugged", "rework", "reimagined", "revisited", "lofi", "nightcore",
                "slowed", "reverb", "bass boosted", "dubstep", "trap", "house", "techno",
                "future bass", "hardstyle", "synthwave", "phonk", "funk", "pagode",
                "sertanejo", "acústico", "ao vivo", "ost", "soundtrack", "theme",
                "opening", "ending"
            ],
            "duplicate_keep": [
                "part", "pt", "chapter", "act", "movement", "mov",
                "i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x",
                "1", "2", "3", "4", "5", "6", "7", "8", "9", "10"
            ],
            "artist_aliases": {},
            "title_aliases": {},
            "priority_suffixes": [
                "original mix", "original", "remastered", "320kbps", "flac", "wav"
            ],
            "preserve_case": [
                "AC/DC", "R.E.M.", "KSHMR", "DJ", "MC", "USA", "UK"
            ],
            "ignore_words": [
                "a", "an", "the", "of", "and", "or", "for", "with", "without",
                "on", "at", "from", "by", "in", "into", "through", "during", "including"
            ],
            "comparison_rules": {
                "case_sensitive": False,
                "ignore_articles": True,
                "ignore_punctuation": True,
                "ignore_spaces": True,
                "similarity_threshold": 0.92,
                "use_canonical_key": True
            }
        }

        if not rules_file.exists():
            with open(rules_file, 'w', encoding='utf-8') as f:
                json.dump(default_rules, f, indent=2, ensure_ascii=False)
            logger.info("[Normalizer] Arquivo de regras criado.")
            self._rules = default_rules
        else:
            try:
                with open(rules_file, 'r', encoding='utf-8') as f:
                    self._rules = json.load(f)
                logger.info("[Normalizer] Regras carregadas do arquivo.")
            except Exception as e:
                logger.error(f"[Normalizer] Erro ao carregar regras: {e}. Recriando arquivo padrão.")
                backup_file = rules_file.with_suffix(".json.bak")
                if rules_file.exists():
                    shutil.copy2(rules_file, backup_file)
                    logger.info(f"[Normalizer] Backup criado: {backup_file}")
                with open(rules_file, 'w', encoding='utf-8') as f:
                    json.dump(default_rules, f, indent=2, ensure_ascii=False)
                self._rules = default_rules

        self._compiled_patterns = {}
        self._compiled_remove = [re.compile(r'\b' + term + r'\b', re.IGNORECASE) for term in self._rules.get("remove", [])]
        invalid_chars = self._rules.get("invalid_characters", [])
        if invalid_chars:
            escaped = [re.escape(c) for c in invalid_chars]
            self._compiled_patterns["invalid"] = re.compile('[' + ''.join(escaped) + ']')
        else:
            self._compiled_patterns["invalid"] = None

        self._artist_aliases = self._rules.get("artist_aliases", {})
        self._title_aliases = self._rules.get("title_aliases", {})
        self._replace_map = self._rules.get("replace", {})
        self._keep_set = set(self._rules.get("keep", []))
        self._ignore_words = set(self._rules.get("ignore_words", []))
        self._duplicate_ignore = set(self._rules.get("duplicate_ignore", []))
        self._duplicate_keep = set(self._rules.get("duplicate_keep", []))
        self._priority_suffixes = self._rules.get("priority_suffixes", [])
        self._comparison_rules = self._rules.get("comparison_rules", {})
        self._preserve_case = self._rules.get("preserve_case", [])

        # Compila padrão para remover parênteses, colchetes e chaves (e o conteúdo dentro)
        self._compiled_patterns["parentheses"] = re.compile(r'\([^)]*\)')
        self._compiled_patterns["brackets"] = re.compile(r'\[[^\]]*\]')
        self._compiled_patterns["braces"] = re.compile(r'\{[^}]*\}')

        logger.info("[Normalizer] Sistema inicializado.")

    def normalize_title(self, title: str) -> str:
        if not title:
            return ""
        title_lower = title.lower().strip()
        for alias, canonical in self._title_aliases.items():
            if alias in title_lower or title_lower == alias:
                title = canonical
                break

        # Remove parênteses, colchetes, chaves e seu conteúdo
        title = self._compiled_patterns["parentheses"].sub(' ', title)
        title = self._compiled_patterns["brackets"].sub(' ', title)
        title = self._compiled_patterns["braces"].sub(' ', title)

        # Remove palavras da lista "remove"
        for pattern in self._compiled_remove:
            title = pattern.sub(' ', title)

        # Remove caracteres inválidos
        if self._compiled_patterns["invalid"]:
            title = self._compiled_patterns["invalid"].sub('', title)

        # Substituições (ex: feat -> ft.)
        for old, new in self._replace_map.items():
            title = re.sub(r'\b' + old + r'\b', new, title, flags=re.IGNORECASE)

        # Remove múltiplos espaços e espaços extras
        title = ' '.join(title.split())
        return title.strip()

    def normalize_artist(self, artist: str) -> str:
        if not artist:
            return "Desconhecido"
        artist_lower = artist.lower().strip()
        for alias, canonical in self._artist_aliases.items():
            if alias in artist_lower or artist_lower == alias:
                artist = canonical
                break
        # Remove parênteses, colchetes, chaves do artista também
        artist = self._compiled_patterns["parentheses"].sub(' ', artist)
        artist = self._compiled_patterns["brackets"].sub(' ', artist)
        artist = self._compiled_patterns["braces"].sub(' ', artist)
        artist = self._clean_text(artist)
        words = artist.split()
        preserved = self._preserve_case
        new_words = []
        for w in words:
            if w in preserved:
                new_words.append(w)
            else:
                new_words.append(w.capitalize())
        artist = ' '.join(new_words)
        return artist.strip()

    def _clean_text(self, text: str) -> str:
        if not text:
            return ""
        text = ' '.join(text.split())
        if self._compiled_patterns["invalid"]:
            text = self._compiled_patterns["invalid"].sub('', text)
        return text.strip()

    def extract_artist_title(self, filename: str) -> Tuple[str, str]:
        name = Path(filename).stem
        separators = [' - ', ' – ', ' — ', ' | ', ' › ', ' : ', '; ']
        artista, titulo = None, None
        # Primeiro tenta separar por separadores
        for sep in separators:
            if sep in name:
                partes = name.split(sep, 1)
                if len(partes) == 2:
                    artista = partes[0].strip()
                    titulo = partes[1].strip()
                    break
        # Se não encontrou separador, tenta identificar por lista de artistas conhecidos
        if not artista and not titulo:
            for known in self._artist_aliases.keys():
                if name.lower().startswith(known):
                    artista = known
                    titulo = name[len(known):].strip()
                    break
        # Fallback: artista desconhecido
        if not artista and not titulo:
            titulo = name
            artista = "Desconhecido"
        # Normaliza ambos
        artista_norm = self.normalize_artist(artista)
        titulo_norm = self.normalize_title(titulo)
        return artista_norm, titulo_norm

    def canonical_key(self, artist: str, title: str) -> str:
        if not artist or not title:
            return ""
        a = self.normalize_artist(artist)
        t = self.normalize_title(title)
        # Remove palavras ignoradas na comparação
        for word in self._duplicate_ignore:
            a = re.sub(r'\b' + word + r'\b', '', a, flags=re.IGNORECASE)
            t = re.sub(r'\b' + word + r'\b', '', t, flags=re.IGNORECASE)
        # Remove palavras comuns
        for word in self._ignore_words:
            a = re.sub(r'\b' + word + r'\b', '', a, flags=re.IGNORECASE)
            t = re.sub(r'\b' + word + r'\b', '', t, flags=re.IGNORECASE)
        combined = (a + t).lower()
        combined = re.sub(r'[^a-zA-Z0-9]', '', combined)
        return combined

    def are_similar(self, name1: str, name2: str) -> bool:
        a1, t1 = self.extract_artist_title(name1)
        a2, t2 = self.extract_artist_title(name2)
        if a1 and t1 and a2 and t2:
            key1 = self.canonical_key(a1, t1)
            key2 = self.canonical_key(a2, t2)
            if key1 and key2:
                if key1 == key2:
                    return True
                if SequenceMatcher(None, key1, key2).ratio() >= 0.92:
                    return True
        return SequenceMatcher(None, name1.lower(), name2.lower()).ratio() >= 0.92

    def generate_new_name(self, filename: str, artist: str = None, title: str = None) -> str:
        if not artist or not title:
            artist, title = self.extract_artist_title(filename)
        artist_norm = self.normalize_artist(artist)
        title_norm = self.normalize_title(title)
        new_name = f"{artist_norm} - {title_norm}.mp3"
        return new_name

    def get_priority_suffix(self, filename: str) -> int:
        name_lower = filename.lower()
        for i, suffix in enumerate(self._priority_suffixes):
            if suffix in name_lower:
                return len(self._priority_suffixes) - i
        return 0

# ============================================================================
# GERENCIADOR DE FALHAS
# ============================================================================

class DownloadFailureManager:
    def __init__(self, app: 'MusicApp'):
        self.app = app
        self.failures_file = Path(__file__).parent / "failed_downloads.json"
        self.failures: List[Dict[str, Any]] = []
        self._lock = threading.Lock()
        self._load()

    def _load(self) -> None:
        if self.failures_file.exists():
            try:
                with open(self.failures_file, 'r', encoding='utf-8') as f:
                    self.failures = json.load(f)
                logger.info(f"[FailureManager] Carregados {len(self.failures)} registros.")
            except Exception as e:
                logger.error(f"[FailureManager] Erro ao carregar arquivo: {e}")
                self.failures = []
        else:
            self.failures = []
            self._save()

    def _save(self) -> None:
        try:
            with open(self.failures_file, 'w', encoding='utf-8') as f:
                json.dump(self.failures, f, indent=2, ensure_ascii=False)
            logger.debug(f"[FailureManager] Salvos {len(self.failures)} registros.")
        except Exception as e:
            logger.error(f"[FailureManager] Erro ao salvar: {e}")

    def _classify_error(self, error: Exception) -> str:
        msg = str(error).lower()
        if "403" in msg or "forbidden" in msg:
            return "FORBIDDEN"
        if "404" in msg or "not found" in msg:
            return "NOT_FOUND"
        if "timeout" in msg or "timed out" in msg:
            return "NETWORK"
        if "private" in msg:
            return "PRIVATE"
        if "unavailable" in msg:
            return "UNAVAILABLE"
        if "age restricted" in msg or "age-restricted" in msg:
            return "AGE_RESTRICTED"
        if "invalid" in msg or "unsupported" in msg:
            return "INVALID_URL"
        return "OTHER"

    def _get_backoff_delay(self, retry_count: int) -> int:
        delays = [5, 15, 30, 60, 120]
        if retry_count < len(delays):
            return delays[retry_count]
        return 300

    def add_failure(self, url: str, artist: str, title: str, filename: str,
                    playlist: str = "", error: Exception = None) -> None:
        with self._lock:
            for rec in self.failures:
                if rec.get("url") == url:
                    rec["timestamp"] = datetime.now().isoformat()
                    rec["error_type"] = self._classify_error(error) if error else "UNKNOWN"
                    rec["error_message"] = str(error) if error else ""
                    rec["retry_count"] = rec.get("retry_count", 0) + 1
                    rec["status"] = "pending"
                    self._save()
                    return
            record = {
                "url": url,
                "artist": artist or "Desconhecido",
                "title": title or "Sem título",
                "filename": filename or "",
                "playlist": playlist or "",
                "timestamp": datetime.now().isoformat(),
                "error_type": self._classify_error(error) if error else "UNKNOWN",
                "error_message": str(error) if error else "",
                "retry_count": 1,
                "status": "pending"
            }
            self.failures.append(record)
            self._save()
            logger.info(f"[FailureManager] Falha registrada: {artist} - {title}")

    def remove_success(self, url: str) -> None:
        with self._lock:
            for i, rec in enumerate(self.failures):
                if rec.get("url") == url:
                    self.failures.pop(i)
                    self._save()
                    logger.info(f"[FailureManager] Removido por sucesso: {url}")
                    return

    def get_pending(self) -> List[Dict[str, Any]]:
        return [r for r in self.failures if r.get("status") == "pending"]

    def get_all(self) -> List[Dict[str, Any]]:
        return self.failures

    def get_stats(self) -> Dict[str, Any]:
        pending = len(self.get_pending())
        total = len(self.failures)
        recovered = sum(1 for r in self.failures if r.get("status") == "completed")
        avg_retries = sum(r.get("retry_count", 0) for r in self.failures) / total if total > 0 else 0
        return {
            "pending": pending,
            "total": total,
            "recovered": recovered,
            "lost": total - recovered - pending,
            "avg_retries": round(avg_retries, 2)
        }

    def retry_all(self, downloader_func) -> None:
        pending = self.get_pending()
        if not pending:
            self.app.show_message("info", "Reprocessamento", "Nenhum download pendente.")
            return
        self.app.append_log_falhas(f"🔄 Reprocessando {len(pending)} downloads...", "INFO")
        for rec in pending:
            self._retry_one(rec, downloader_func)

    def retry_selected(self, urls: List[str], downloader_func) -> None:
        if not urls:
            return
        for rec in self.failures:
            if rec.get("url") in urls and rec.get("status") == "pending":
                self._retry_one(rec, downloader_func)

    def _retry_one(self, rec: Dict[str, Any], downloader_func) -> None:
        url = rec["url"]
        artist = rec.get("artist", "Desconhecido")
        title = rec.get("title", "Sem título")
        filename = rec.get("filename", "")
        playlist = rec.get("playlist", "")
        retry_count = rec.get("retry_count", 0)
        max_retries = 5

        if retry_count >= max_retries:
            rec["status"] = "failed"
            self._save()
            self.app.append_log_falhas(f"⚠️ Máximo de tentativas para {artist} - {title}", "WARNING")
            return

        delay = self._get_backoff_delay(retry_count)
        self.app.append_log_falhas(f"⏳ Tentativa {retry_count+1}/{max_retries} para {artist} - {title} (espera {delay}s)", "INFO")

        def success_callback():
            rec["status"] = "completed"
            self._save()
            self.app.append_log_falhas(f"✅ Recuperado: {artist} - {title}", "SUCCESS")
            self.app._atualizar_lista_falhas()

        def failure_callback(e: Exception):
            rec["retry_count"] = retry_count + 1
            rec["error_type"] = self._classify_error(e)
            rec["error_message"] = str(e)
            rec["timestamp"] = datetime.now().isoformat()
            self._save()
            self.app.append_log_falhas(f"❌ Falha na tentativa {retry_count+1}: {e}", "ERROR")
            if rec["retry_count"] < max_retries:
                QTimer.singleShot(delay * 1000, lambda: self._retry_one(rec, downloader_func))
            else:
                rec["status"] = "failed"
                self._save()
                self.app.append_log_falhas(f"⚠️ Máximo de tentativas para {artist} - {title}", "WARNING")
            self.app._atualizar_lista_falhas()

        threading.Thread(target=lambda: downloader_func(url, artist, title, filename, playlist, success_callback, failure_callback), daemon=True).start()

    def remove_by_url(self, url: str) -> None:
        with self._lock:
            for i, rec in enumerate(self.failures):
                if rec.get("url") == url:
                    self.failures.pop(i)
                    self._save()
                    self.app._atualizar_lista_falhas()
                    return

    def clear_completed(self) -> None:
        with self._lock:
            self.failures = [r for r in self.failures if r.get("status") != "completed"]
            self._save()
            self.app._atualizar_lista_falhas()

    def get_by_status(self, status: str) -> List[Dict[str, Any]]:
        return [r for r in self.failures if r.get("status") == status]

# ============================================================================
# THREADS
# ============================================================================

class NormalizeCollectThread(QThread):
    progress = Signal(str, int)
    finished = Signal(list)
    error = Signal(str)

    def __init__(self, pasta: Path, normalizer: LibraryNormalizer, cache: MetadataCache):
        super().__init__()
        self.pasta = pasta
        self.normalizer = normalizer
        self.cache = cache

    def run(self) -> None:
        try:
            arquivos = list(self.pasta.glob("*.mp3"))
            if not arquivos:
                self.error.emit("Nenhum arquivo MP3 encontrado.")
                self.finished.emit([])
                return
            total = len(arquivos)
            alteracoes = []
            for i, arquivo in enumerate(arquivos):
                metadata = self.cache.get_or_update(arquivo, force=False)
                artista = metadata.get('artist', '').strip()
                titulo = metadata.get('title', '').strip()
                if not artista or not titulo:
                    artista, titulo = self.normalizer.extract_artist_title(arquivo.name)
                novo_nome = self.normalizer.generate_new_name(arquivo.name, artista, titulo)
                # Armazena (nome_antigo, novo_nome)
                alteracoes.append((arquivo.name, novo_nome))
                progresso = int((i + 1) / total * 100)
                self.progress.emit(f"Processando {i+1}/{total}", progresso)
            self.finished.emit(alteracoes)
        except Exception as e:
            logger.error(f"Erro na thread de coleta: {e}")
            self.error.emit(str(e))

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

class ReloadPlaylistThread(QThread):
    progress = Signal(str, int)
    finished = Signal(int)
    error = Signal(str)

    def __init__(self, pasta: Path, cache: MetadataCache, force: bool = False, preserve: bool = False,
                 saved_file: Optional[str] = None, saved_position: int = 0):
        super().__init__()
        self.pasta = pasta
        self.cache = cache
        self.force = force
        self.preserve = preserve
        self.saved_file = saved_file
        self.saved_position = saved_position
        self._playlist_result = []

    def run(self) -> None:
        try:
            if not self.pasta.is_dir():
                self.error.emit("Pasta inválida")
                self.finished.emit(0)
                return
            self.progress.emit("Lendo arquivos...", 0)
            arquivos = list(self.pasta.glob("*.mp3"))
            total = len(arquivos)
            if total == 0:
                self.progress.emit("Nenhum MP3 encontrado.", 100)
                self.finished.emit(0)
                return
            arquivos_validos = []
            arquivos_ignorados = []
            arquivos_nomes = set()
            for i, arquivo in enumerate(arquivos):
                if not arquivo.is_file():
                    continue
                if not os.access(str(arquivo), os.R_OK):
                    arquivos_ignorados.append(arquivo.name)
                    continue
                metadata = self.cache.get_or_update(arquivo, force=self.force)
                if metadata.get('duration', 0) <= 0:
                    arquivos_ignorados.append(arquivo.name)
                    continue
                if not arquivo.name or arquivo.name.isspace():
                    arquivos_ignorados.append(arquivo.name)
                    continue
                arquivos_validos.append(arquivo.name)
                arquivos_nomes.add(arquivo.name)
                progresso = int((i + 1) / total * 80) + 10
                self.progress.emit(f"Processando {i+1}/{total}", progresso)
            self.cache.cleanup(self.pasta, arquivos_nomes)
            self.progress.emit("Organizando playlist...", 90)
            self._playlist_result = sorted(arquivos_validos)
            self.finished.emit(len(self._playlist_result))
        except Exception as e:
            logger.error(f"Erro na thread de recarregar: {e}")
            self.error.emit(str(e))
            self.finished.emit(0)

    def get_playlist(self) -> List[str]:
        return self._playlist_result

# ============================================================================
# CLASSE PRINCIPAL - MUSICAPP (com normalizador e detecção de duplicatas atualizados)
# ============================================================================

class MusicApp(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle("🎵 Nexus Player")
        self.setGeometry(100, 100, 1050, 750)
        self._running: bool = True

        self.cache = MetadataCache()
        self.normalizer = LibraryNormalizer()
        self.failure_manager = DownloadFailureManager(self)

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
        self.criar_aba_normalizador()
        self.criar_aba_falhas()

        self.config = carregar_config()
        pasta_player = self.config.get("last_player_folder", str(Path.home() / "Músicas" / "Nexus"))
        self.player_folder_line.setText(pasta_player)

        Path(pasta_player).mkdir(parents=True, exist_ok=True)
        self.carregar_playlist_sync(Path(pasta_player))

        self._pending_play = False
        self._pending_position = 0
        self._reload_thread = None
        self._normalize_thread = None

    # ========================================================================
    # MÉTODO SHOW_MESSAGE (thread-safe)
    # ========================================================================
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

    # ========================================================================
    # HISTÓRICO
    # ========================================================================
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
    # PLAYER ERROS
    # ========================================================================
    @Slot(QMediaPlayer.Error)
    def on_player_error(self, error: QMediaPlayer.Error) -> None:
        if not self._running:
            return
        erro_msg = self.player.errorString()
        logger.error(f"Erro no player: {erro_msg} (código {error})")
        self.append_log_player(f"⚠️ Erro ao reproduzir: {erro_msg}", "ERROR")
        if self.current_index >= 0 and self.current_index < len(self.playlist):
            self.musica_proxima()

    # ========================================================================
    # LOGS
    # ========================================================================
    def append_log_baixador(self, texto: str, tipo: str = "INFO"):
        if hasattr(self, 'log_baixador'):
            self.log_baixador.append_log(texto, tipo)

    def append_log_player(self, texto: str, tipo: str = "INFO"):
        if hasattr(self, 'log_player'):
            self.log_player.append_log(texto, tipo)

    def append_log_normalizador(self, texto: str, tipo: str = "INFO"):
        if hasattr(self, 'log_normalizador'):
            self.log_normalizador.append_log(texto, tipo)

    def append_log_falhas(self, texto: str, tipo: str = "INFO"):
        if hasattr(self, 'log_falhas'):
            self.log_falhas.append_log(texto, tipo)

    # ========================================================================
    # CRIAÇÃO DAS ABAS (resumido para não alongar)
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
        self.log_baixador = CollapsibleLog("📋 Log do Download")
        layout.addWidget(self.log_baixador)
        layout.addWidget(QLabel("📜 Histórico de downloads:"))
        row_hist = QHBoxLayout()
        self.historico_list = QListWidget()
        row_hist.addWidget(self.historico_list)
        btn_limpar = QPushButton("🗑️ Limpar")
        btn_limpar.clicked.connect(self.limpar_historico)
        row_hist.addWidget(btn_limpar)
        layout.addLayout(row_hist)
        footer = QLabel("⚡ Powered by yt-dlp | MP3 192 kbps | v0.18")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)
        self.append_log_baixador("Pronto para baixar músicas.", "INFO")

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
        btn_recarregar.clicked.connect(self.recarregar_playlist_threaded)
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
        self.log_player = CollapsibleLog("📋 Log do Player")
        layout.addWidget(self.log_player)
        self.append_log_player("Player inicializado.", "INFO")
        self.slider_progresso.setEnabled(False)

    def criar_aba_normalizador(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "📚 Sistema Inteligente de Normalização")
        layout = QVBoxLayout(tab)
        lbl = QLabel("📚 Sistema Inteligente de Normalização da Biblioteca Musical")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout.addWidget(lbl)
        row1 = QHBoxLayout()
        row1.addWidget(QLabel("📁 Selecione a pasta:"))
        self.norm_folder_entry = QLineEdit()
        self.norm_folder_entry.setText(str(Path.home() / "Músicas" / "Nexus"))
        row1.addWidget(self.norm_folder_entry)
        btn_dup_folder = QPushButton("📂")
        btn_dup_folder.clicked.connect(self.escolher_pasta_norm)
        row1.addWidget(btn_dup_folder)
        self.btn_escanear = QPushButton("🔍 Escanear Duplicatas")
        self.btn_escanear.clicked.connect(self.escanear_duplicatas_normalizado)
        row1.addWidget(self.btn_escanear)
        self.btn_normalizar = QPushButton("🧹 Normalizar Arquivos")
        self.btn_normalizar.clicked.connect(self.normalizar_arquivos)
        row1.addWidget(self.btn_normalizar)
        layout.addLayout(row1)
        status_layout = QHBoxLayout()
        self.norm_status_label = QLabel("Status: Aguardando")
        status_layout.addWidget(self.norm_status_label)
        self.norm_progress_bar = QProgressBar()
        self.norm_progress_bar.setRange(0, 100)
        self.norm_progress_bar.setValue(0)
        self.norm_progress_bar.setVisible(False)
        status_layout.addWidget(self.norm_progress_bar)
        layout.addLayout(status_layout)
        splitter = QSplitter(Qt.Horizontal)
        self.norm_log_text = QTextEdit()
        self.norm_log_text.setReadOnly(True)
        self.norm_log_text.setFont(QFont("Consolas", 9))
        splitter.addWidget(self.norm_log_text)
        self.norm_list = QListWidget()
        splitter.addWidget(self.norm_list)
        layout.addWidget(splitter)
        btn_delete = QPushButton("🗑️ Deletar Selecionado")
        btn_delete.clicked.connect(self.deletar_duplicata_selecionada_norm)
        layout.addWidget(btn_delete)
        self.log_normalizador = CollapsibleLog("📋 Log do Sistema de Normalização")
        layout.addWidget(self.log_normalizador)
        footer = QLabel("⚡ Selecione um arquivo duplicado (com \"╰─\") e clique em Deletar. Use 'Normalizar' para padronizar nomes.")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)
        self.append_log_normalizador("Sistema de Normalização inicializado.", "INFO")

    def criar_aba_falhas(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "📥 Downloads Falhados")
        layout = QVBoxLayout(tab)
        lbl = QLabel("📥 Gerenciador Inteligente de Downloads Falhados")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout.addWidget(lbl)
        stats_layout = QHBoxLayout()
        self.stats_label = QLabel("Estatísticas: Pendentes: 0 | Total: 0 | Recuperados: 0 | Perdidos: 0 | Tentativas médias: 0.0")
        stats_layout.addWidget(self.stats_label)
        layout.addLayout(stats_layout)
        filter_layout = QHBoxLayout()
        filter_layout.addWidget(QLabel("Filtrar:"))
        self.filter_combo = QComboBox()
        self.filter_combo.addItems(["Todos", "Pendentes", "Completados", "Falhas", "FORBIDDEN", "NOT_FOUND", "NETWORK", "PRIVATE", "UNAVAILABLE", "AGE_RESTRICTED", "INVALID_URL", "OTHER"])
        self.filter_combo.currentTextChanged.connect(self._atualizar_lista_falhas)
        filter_layout.addWidget(self.filter_combo)
        layout.addLayout(filter_layout)
        self.failures_list = QListWidget()
        layout.addWidget(self.failures_list)
        btn_layout = QHBoxLayout()
        btn_retry_all = QPushButton("🔄 Reprocessar Todos")
        btn_retry_all.clicked.connect(self._retry_all_failures)
        btn_layout.addWidget(btn_retry_all)
        btn_retry_selected = QPushButton("🔁 Reprocessar Selecionados")
        btn_retry_selected.clicked.connect(self._retry_selected_failures)
        btn_layout.addWidget(btn_retry_selected)
        btn_remove_selected = QPushButton("❌ Remover Selecionados")
        btn_remove_selected.clicked.connect(self._remove_selected_failures)
        btn_layout.addWidget(btn_remove_selected)
        btn_clear_completed = QPushButton("🗑️ Limpar Completados")
        btn_clear_completed.clicked.connect(self._clear_completed_failures)
        btn_layout.addWidget(btn_clear_completed)
        btn_open_link = QPushButton("🔗 Abrir Link")
        btn_open_link.clicked.connect(self._open_failure_link)
        btn_layout.addWidget(btn_open_link)
        btn_copy_url = QPushButton("📋 Copiar URL")
        btn_copy_url.clicked.connect(self._copy_failure_url)
        btn_layout.addWidget(btn_copy_url)
        layout.addLayout(btn_layout)
        self.log_falhas = CollapsibleLog("📋 Log de Falhas")
        layout.addWidget(self.log_falhas)
        footer = QLabel("⚡ Selecione um ou mais itens para reprocessar, remover ou copiar.")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)
        self.append_log_falhas("Gerenciador de falhas inicializado.", "INFO")
        self._atualizar_lista_falhas()

    # ========================================================================
    # FUNÇÕES DA ABA DE FALHAS
    # ========================================================================
    def _atualizar_lista_falhas(self) -> None:
        filtro = self.filter_combo.currentText() if hasattr(self, 'filter_combo') else "Todos"
        self.failures_list.clear()
        registros = self.failure_manager.get_all()
        if filtro != "Todos":
            registros = [r for r in registros if r.get("status") == filtro or r.get("error_type") == filtro]
        if not registros:
            self.failures_list.addItem("✅ Nenhum download falhado.")
            return
        for rec in registros:
            artist = rec.get("artist", "Desconhecido")
            title = rec.get("title", "Sem título")
            status = rec.get("status", "pending")
            err_type = rec.get("error_type", "UNKNOWN")
            retries = rec.get("retry_count", 0)
            display = f"{artist} - {title} [{status}] ({err_type}) tentativas: {retries}"
            self.failures_list.addItem(display)
        stats = self.failure_manager.get_stats()
        self.stats_label.setText(
            f"Estatísticas: Pendentes: {stats['pending']} | Total: {stats['total']} | "
            f"Recuperados: {stats['recovered']} | Perdidos: {stats['lost']} | "
            f"Tentativas médias: {stats['avg_retries']}"
        )

    def _get_selected_urls(self) -> List[str]:
        selected = self.failures_list.selectedItems()
        if not selected:
            return []
        urls = []
        for item in selected:
            display = item.text()
            for rec in self.failure_manager.get_all():
                artist = rec.get("artist", "Desconhecido")
                title = rec.get("title", "Sem título")
                status = rec.get("status", "pending")
                err_type = rec.get("error_type", "UNKNOWN")
                retries = rec.get("retry_count", 0)
                if f"{artist} - {title} [{status}] ({err_type}) tentativas: {retries}" == display:
                    urls.append(rec.get("url"))
                    break
        return urls

    def _retry_all_failures(self) -> None:
        self.failure_manager.retry_all(self._reprocess_download)

    def _retry_selected_failures(self) -> None:
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione pelo menos um item.")
            return
        self.failure_manager.retry_selected(urls, self._reprocess_download)

    def _remove_selected_failures(self) -> None:
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione pelo menos um item.")
            return
        for url in urls:
            self.failure_manager.remove_by_url(url)
        self._atualizar_lista_falhas()
        self.append_log_falhas(f"🗑️ {len(urls)} registro(s) removido(s).", "INFO")

    def _clear_completed_failures(self) -> None:
        self.failure_manager.clear_completed()
        self._atualizar_lista_falhas()
        self.append_log_falhas("🗑️ Registros completados removidos.", "INFO")

    def _open_failure_link(self) -> None:
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione um item.")
            return
        webbrowser.open(urls[0])

    def _copy_failure_url(self) -> None:
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione um item.")
            return
        QApplication.clipboard().setText(urls[0])
        self.append_log_falhas(f"📋 URL copiada: {urls[0]}", "INFO")

    def _reprocess_download(self, url: str, artist: str, title: str, filename: str,
                            playlist: str, success_cb, failure_cb) -> None:
        try:
            ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
            with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                info = ydl.extract_info(url, download=False)
                actual_artist = info.get('uploader', artist)
                actual_title = info.get('title', title)
            pasta = Path(self.dest_folder_entry.text().strip())
            if not pasta.exists():
                pasta.mkdir(parents=True, exist_ok=True)
            ffmpeg_path = localizar_ffmpeg()
            if not ffmpeg_path:
                failure_cb(Exception("FFmpeg não encontrado"))
                return
            ydl_opts = {
                'format': 'bestaudio/best',
                'postprocessors': [
                    {'key': 'FFmpegExtractAudio', 'preferredcodec': 'mp3', 'preferredquality': '192'},
                    {'key': 'FFmpegMetadata', 'add_metadata': True}
                ],
                'ffmpeg_location': str(ffmpeg_path),
                'outtmpl': str(pasta / '%(uploader)s - %(title)s.%(ext)s'),
                'quiet': False,
                'no_warnings': False,
                'writethumbnail': True,
            }
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            self.failure_manager.remove_success(url)
            success_cb()
        except Exception as e:
            failure_cb(e)

    # ========================================================================
    # NORMALIZADOR - FUNÇÕES
    # ========================================================================
    def escolher_pasta_norm(self) -> None:
        pasta = QFileDialog.getExistingDirectory(self, "Selecione a pasta para normalizar")
        if pasta:
            self.norm_folder_entry.setText(pasta)

    def normalizar_arquivos(self) -> None:
        if not self._running:
            return
        pasta_str = self.norm_folder_entry.text().strip()
        if not pasta_str:
            self.show_message("warning", "Aviso", "Selecione uma pasta primeiro!")
            return
        pasta = Path(pasta_str)
        if not pasta.exists():
            self.show_message("critical", "Erro", "Pasta não encontrada!")
            return
        self.append_log_normalizador(f"🧹 Coletando dados para normalização em: {pasta}", "INFO")
        self._update_norm_status("Coletando dados...", 0)
        self.btn_normalizar.setEnabled(False)
        self._normalize_thread = NormalizeCollectThread(pasta, self.normalizer, self.cache)
        self._normalize_thread.progress.connect(self._on_normalize_progress)
        self._normalize_thread.finished.connect(self._on_normalize_collected)
        self._normalize_thread.error.connect(self._on_normalize_error)
        self._normalize_thread.start()

    def _on_normalize_progress(self, msg: str, progress: int):
        self.append_log_normalizador(f"⏳ {msg}", "INFO")
        self._update_norm_status(msg, progress)

    def _on_normalize_collected(self, alteracoes: list):
        self.btn_normalizar.setEnabled(True)
        if not alteracoes:
            self.append_log_normalizador("✅ Todos os nomes já estão normalizados.", "SUCCESS")
            self._update_norm_status("Concluído (sem alterações)", 100)
            return
        # Usa a nova prévia com nome atual e verde
        dialog = NormalizePreviewDialog(alteracoes, self)
        if dialog.exec() == QDialog.Accepted:
            selecao = dialog.get_selecao()
            # Filtra apenas os selecionados, mas como a tabela tem 3 colunas, a seleção é pelas checkboxes
            # Mas precisamos das alterações completas
            alteracoes_selecionadas = [alt for i, alt in enumerate(alteracoes) if selecao[i]]
            if not alteracoes_selecionadas:
                self.append_log_normalizador("⏹️ Nenhum arquivo selecionado.", "INFO")
                self._update_norm_status("Cancelado", 0)
                return
            self._execute_normalize(alteracoes_selecionadas)
        else:
            self.append_log_normalizador("⏹️ Normalização cancelada pelo usuário.", "INFO")
            self._update_norm_status("Cancelado", 0)

    def _execute_normalize(self, alteracoes: list):
        self.append_log_normalizador("🧹 Normalizando arquivos...", "INFO")
        self._update_norm_status("Normalizando...", 90)
        self.btn_normalizar.setEnabled(False)

        def normalize_task():
            sucessos = 0
            for antigo_nome, novo_nome in alteracoes:
                # Antigo_nome é apenas o nome do arquivo, precisamos do caminho completo
                pasta = Path(self.norm_folder_entry.text().strip())
                antigo_path = pasta / antigo_nome
                novo_path = pasta / novo_nome
                if not antigo_path.exists():
                    self.append_log_normalizador(f"⚠️ Arquivo não encontrado: {antigo_nome}", "WARNING")
                    continue
                if novo_path.exists():
                    self.append_log_normalizador(f"⚠️ Nome já existe: {novo_nome}", "WARNING")
                    continue
                try:
                    antigo_path.rename(novo_path)
                    self.cache.update_file_path(str(antigo_path), str(novo_path))
                    sucessos += 1
                    self.append_log_normalizador(f"✅ Normalizado: {antigo_nome} → {novo_nome}", "SUCCESS")
                except Exception as e:
                    self.append_log_normalizador(f"❌ Erro ao normalizar {antigo_nome}: {e}", "ERROR")
                    logger.error(f"Erro ao normalizar {antigo_nome}: {e}")
            QTimer.singleShot(0, lambda: self._on_normalize_done(sucessos))

        threading.Thread(target=normalize_task, daemon=True).start()

    def _on_normalize_done(self, sucessos: int):
        self.btn_normalizar.setEnabled(True)
        self.append_log_normalizador(f"✅ Normalização concluída: {sucessos} arquivo(s) alterados.", "SUCCESS")
        self._update_norm_status(f"Concluído: {sucessos} normalizados", 100)
        self.show_message("info", "Normalização", f"{sucessos} arquivo(s) normalizados com sucesso!")
        pasta = Path(self.norm_folder_entry.text().strip())
        if Path(self.player_folder_line.text().strip()) == pasta:
            self.carregar_playlist_sync(pasta, True, True)

    def _on_normalize_error(self, erro: str):
        self.btn_normalizar.setEnabled(True)
        self.append_log_normalizador(f"❌ Erro: {erro}", "ERROR")
        self._update_norm_status("Erro", 0)
        self.show_message("critical", "Erro", f"Ocorreu um erro:\n{erro}")

    def _update_norm_status(self, texto: str, progresso: int = -1) -> None:
        if not self._running:
            return
        QTimer.singleShot(0, partial(self._update_norm_status_impl, texto, progresso))

    def _update_norm_status_impl(self, texto: str, progresso: int) -> None:
        self.norm_status_label.setText(f"Status: {texto}")
        if progresso >= 0:
            self.norm_progress_bar.setVisible(True)
            self.norm_progress_bar.setValue(progresso)
        else:
            self.norm_progress_bar.setVisible(False)

    # ========================================================================
    # NORMALIZADOR - DUPLICATAS (com chave canônica aprimorada)
    # ========================================================================
    def _atualizar_norm_list_ui(self, duplicatas: List[List[str]]) -> None:
        if not self._running:
            return
        self.norm_list.clear()
        if not duplicatas:
            self.norm_list.addItem("✅ Nenhuma duplicata encontrada!")
            return
        for grupo in duplicatas:
            self.norm_list.addItem(f"📁 {grupo[0]}")
            for arquivo in grupo[1:]:
                self.norm_list.addItem(f"   ╰─ {arquivo}")

    def escanear_duplicatas_normalizado(self) -> None:
        if not self._running:
            return
        pasta_str = self.norm_folder_entry.text().strip()
        if not pasta_str:
            self.show_message("warning", "Aviso", "Selecione uma pasta primeiro!")
            return
        pasta = Path(pasta_str)
        if not pasta.exists():
            self.show_message("critical", "Erro", "Pasta não encontrada!")
            return
        self.append_log_normalizador(f"🔍 Escaneando pasta: {pasta} (usando normalizador aprimorado)", "INFO")
        self._update_norm_status("Iniciando...", 0)
        self.btn_escanear.setEnabled(False)
        self.norm_progress_bar.setVisible(True)

        def scan_task_normalized() -> None:
            try:
                registros = self.cache.get_all_metadata_for_folder(pasta, limpar_orfãos=True)
                if not registros:
                    self.append_log_normalizador("⚠️ Nenhum arquivo MP3 encontrado no cache.", "WARNING")
                    self._update_norm_status("Concluído (sem dados)", 100)
                    QTimer.singleShot(0, partial(self._atualizar_norm_list_ui, []))
                    self.btn_escanear.setEnabled(True)
                    self.norm_progress_bar.setVisible(False)
                    return
                total = len(registros)
                self.append_log_normalizador(f"📊 Carregados {total} registros do cache.", "INFO")
                self._update_norm_status("Processando registros...", 10)
                musicas = []
                for reg in registros:
                    filename = reg.get('filename', '')
                    artist = reg.get('artist', '').strip()
                    title = reg.get('title', '').strip()
                    if not artist or not title:
                        artist, title = self.normalizer.extract_artist_title(filename)
                    # Normaliza com remoção de parênteses e palavras genéricas
                    artist_norm = self.normalizer.normalize_artist(artist)
                    title_norm = self.normalizer.normalize_title(title)
                    musicas.append({
                        'filename': filename,
                        'artist': artist_norm,
                        'title': title_norm,
                        'path': reg.get('path', '')
                    })
                # Agrupa por artista normalizado
                grupos = {}
                for m in musicas:
                    artista_chave = m['artist'].lower().strip()
                    if not artista_chave:
                        artista_chave = 'desconhecido'
                    if artista_chave not in grupos:
                        grupos[artista_chave] = []
                    grupos[artista_chave].append(m)
                duplicatas = []
                processados = set()
                for artista, lista in grupos.items():
                    if len(lista) < 2:
                        continue
                    # Ordena por título normalizado
                    lista.sort(key=lambda x: x['title'].lower())
                    i = 0
                    while i < len(lista):
                        item_atual = lista[i]
                        if item_atual['filename'] in processados:
                            i += 1
                            continue
                        grupo = [item_atual['filename']]
                        j = i + 1
                        while j < len(lista):
                            item_prox = lista[j]
                            if item_prox['filename'] in processados:
                                j += 1
                                continue
                            tit1 = item_atual['title'].lower().strip()
                            tit2 = item_prox['title'].lower().strip()
                            # Se os títulos forem idênticos após a normalização, são duplicatas
                            if tit1 == tit2:
                                grupo.append(item_prox['filename'])
                                processados.add(item_prox['filename'])
                            else:
                                # Usa similaridade com threshold alto
                                if SequenceMatcher(None, tit1, tit2).ratio() >= 0.92:
                                    grupo.append(item_prox['filename'])
                                    processados.add(item_prox['filename'])
                            j += 1
                        if len(grupo) > 1:
                            duplicatas.append(grupo)
                            processados.add(item_atual['filename'])
                        i = j
                if duplicatas:
                    self.append_log_normalizador(f"⚠️ Encontrados {len(duplicatas)} grupos de duplicatas!", "WARNING")
                    for grupo in duplicatas:
                        self.append_log_normalizador("📌 GRUPO DE DUPLICATAS:", "INFO")
                        for arquivo in grupo:
                            self.append_log_normalizador(f"   • {arquivo}", "INFO")
                        self.append_log_normalizador("", "INFO")
                    QTimer.singleShot(0, partial(self._atualizar_norm_list_ui, duplicatas))
                    self._update_norm_status(f"Concluído: {len(duplicatas)} grupos", 100)
                    self.show_message("info", "Concluído", f"Encontrados {len(duplicatas)} grupos de duplicatas!")
                else:
                    self.append_log_normalizador("✅ NENHUMA DUPLICATA ENCONTRADA!", "SUCCESS")
                    QTimer.singleShot(0, partial(self._atualizar_norm_list_ui, []))
                    self._update_norm_status("Concluído: 0 grupos", 100)
                    self.show_message("info", "Concluído", "Nenhuma duplicata encontrada!")
            except Exception as e:
                logger.error(f"Erro em escanear_duplicatas: {e}")
                self.append_log_normalizador(f"❌ Erro: {e}", "ERROR")
                self._update_norm_status(f"Erro: {str(e)[:50]}...", 0)
                self.show_message("critical", "Erro", f"Ocorreu um erro:\n{e}")
            finally:
                self.btn_escanear.setEnabled(True)
                self.norm_progress_bar.setVisible(False)

        threading.Thread(target=scan_task_normalized, daemon=True).start()

    def deletar_duplicata_selecionada_norm(self) -> None:
        selecao = self.norm_list.currentRow()
        if selecao < 0:
            self.show_message("warning", "Aviso", "Selecione um arquivo para deletar!")
            return
        item = self.norm_list.currentItem().text()
        if not item.startswith("   ╰─"):
            self.show_message("warning", "Aviso", "Selecione apenas arquivos duplicados (com \"╰─\")!")
            return
        nome_arquivo = item.replace("   ╰─ ", "").strip()
        pasta = Path(self.norm_folder_entry.text().strip())
        caminho = pasta / nome_arquivo
        if not caminho.exists():
            self.show_message("critical", "Erro", "Arquivo não encontrado!")
            return
        if self.show_message("question", "Confirmar", f"Tem certeza que deseja deletar:\n{nome_arquivo}") == QMessageBox.Yes:
            try:
                caminho.unlink()
                self.norm_list.takeItem(selecao)
                self.append_log_normalizador(f"🗑️ DELETADO: {nome_arquivo}", "SUCCESS")
                self.show_message("info", "Sucesso", f"Arquivo deletado:\n{nome_arquivo}")
                with self.cache._lock:
                    with self.cache._get_connection() as conn:
                        conn.execute("DELETE FROM music_cache WHERE path = ?", (str(caminho),))
                        conn.commit()
                if Path(self.player_folder_line.text().strip()) == pasta:
                    self.carregar_playlist_sync(pasta, True, True)
            except Exception as e:
                logger.error(f"Erro ao deletar duplicata: {e}")
                self.append_log_normalizador(f"❌ Erro ao deletar: {e}", "ERROR")
                self.show_message("critical", "Erro", f"Erro ao deletar:\n{e}")

    # ========================================================================
    # RECARREGAR PLAYLIST EM THREAD
    # ========================================================================
    def recarregar_playlist_threaded(self) -> None:
        if self._reload_thread and self._reload_thread.isRunning():
            self.append_log_player("⚠️ Recarregamento já em andamento.", "WARNING")
            return
        pasta = Path(self.player_folder_line.text().strip())
        if not pasta.is_dir():
            self.show_message("warning", "Aviso", "Pasta inválida ou não encontrada.")
            return
        saved_index = self.current_index if self.current_index >= 0 else -1
        saved_file = self.playlist[saved_index] if saved_index >= 0 else None
        saved_position = self.player.position() if self.player.isSeekable() else 0
        self.append_log_player("🔄 Recarregando playlist em segundo plano...", "INFO")
        self.btn_recarregar.setEnabled(False)
        self.btn_recarregar.setText("⏳ Carregando...")
        self._reload_thread = ReloadPlaylistThread(pasta, self.cache, force=True, preserve=True,
                                                   saved_file=saved_file, saved_position=saved_position)
        self._reload_thread.progress.connect(self._on_reload_progress)
        self._reload_thread.finished.connect(self._on_reload_finished)
        self._reload_thread.error.connect(self._on_reload_error)
        self._reload_thread.start()

    def _on_reload_progress(self, mensagem: str, progresso: int):
        self.append_log_player(f"⏳ {mensagem}", "INFO")

    def _on_reload_finished(self, count: int):
        self.btn_recarregar.setEnabled(True)
        self.btn_recarregar.setText("🔄 Recarregar")
        if self._reload_thread:
            nova_playlist = self._reload_thread.get_playlist()
            if nova_playlist:
                self.playlist = nova_playlist
                self._atualizar_lista_player_ui()
                if self.current_index >= 0 and self.current_index < len(self.playlist):
                    self.tocar_musica(self.current_index, self._pending_position)
                self.append_log_player(f"✅ Playlist recarregada: {count} músicas.", "SUCCESS")
            else:
                self.append_log_player("⚠️ Playlist vazia após recarregamento.", "WARNING")
        self._reload_thread = None

    def _on_reload_error(self, erro: str):
        self.btn_recarregar.setEnabled(True)
        self.btn_recarregar.setText("🔄 Recarregar")
        self.append_log_player(f"❌ Erro ao recarregar: {erro}", "ERROR")
        self.show_message("critical", "Erro", f"Erro ao recarregar playlist:\n{erro}")
        self._reload_thread = None

    # ========================================================================
    # CARREGAR PLAYLIST SÍNCRONA
    # ========================================================================
    def carregar_playlist_sync(self, pasta: Path, force: bool = False, preserve_position: bool = False) -> int:
        saved_index = self.current_index if preserve_position else -1
        saved_file = self.playlist[saved_index] if (preserve_position and 0 <= saved_index < len(self.playlist)) else None
        saved_position = self.player.position() if preserve_position and self.player.isSeekable() else 0
        was_playing = (self.player.playbackState() == QMediaPlayer.PlayingState) if preserve_position else False

        try:
            if not pasta.is_dir():
                logger.warning(f"Pasta inválida: {pasta}")
                self.playlist = []
                self.current_index = -1
                self._atualizar_lista_player_ui()
                self.slider_progresso.setEnabled(False)
                self.musica_atual_label.setText("⏹️ Nenhuma música")
                self.tempo_label.setText("00:00 / 00:00")
                self.append_log_player("Pasta inválida selecionada.", "WARNING")
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
            self._atualizar_lista_player_ui()

            new_index = -1
            if preserve_position and saved_file is not None:
                try:
                    new_index = self.playlist.index(saved_file)
                except ValueError:
                    for idx, f in enumerate(self.playlist):
                        if self.normalizer.are_similar(saved_file, f):
                            new_index = idx
                            break

            if new_index >= 0:
                self.current_index = new_index
                self.tocar_musica(new_index, resume_position=saved_position if preserve_position else 0)
                if was_playing and self.player.playbackState() != QMediaPlayer.PlayingState:
                    self.player.play()
                self.append_log_player(f"Playlist recarregada, música restaurada: {self.playlist[new_index]}", "SUCCESS")
            else:
                self.current_index = -1
                self.slider_progresso.setEnabled(False)
                self.musica_atual_label.setText("⏹️ Nenhuma música")
                self.tempo_label.setText("00:00 / 00:00")
                self.btn_play_pause.setText("▶ Play")
                self.append_log_player("Playlist recarregada, nenhuma música correspondente encontrada.", "INFO")

            logger.info(f"Playlist carregada: {len(self.playlist)} músicas (força={force}, preserve={preserve_position})")
            if arquivos_ignorados:
                logger.warning(f"Arquivos ignorados: {len(arquivos_ignorados)} - {', '.join(arquivos_ignorados[:5])}{'...' if len(arquivos_ignorados) > 5 else ''}")
                self.append_log_player(f"⚠️ {len(arquivos_ignorados)} arquivo(s) ignorado(s).", "WARNING")

            self.config["last_player_folder"] = str(pasta)
            salvar_config(self.config)

            return len(self.playlist)
        except Exception as e:
            logger.error(f"Erro em carregar_playlist: {e}")
            self.append_log_player(f"Erro ao carregar playlist: {e}", "ERROR")
            self.playlist = []
            self.current_index = -1
            self._atualizar_lista_player_ui()
            return 0

    def _atualizar_lista_player_ui(self) -> None:
        self.playlist_widget.clear()
        for idx, musica in enumerate(self.playlist):
            item = QListWidgetItem(musica)
            item.setData(Qt.UserRole, idx)
            self.playlist_widget.addItem(item)
        if 0 <= self.current_index < len(self.playlist):
            self.playlist_widget.setCurrentRow(self.current_index)
        else:
            self.playlist_widget.setCurrentRow(-1)

    # ========================================================================
    # PLAYER - REPRODUÇÃO
    # ========================================================================
    def tocar_musica(self, indice: int, resume_position: int = 0) -> None:
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
            self.append_log_player(f"⚠️ Arquivo não encontrado: {arquivo}", "WARNING")
            self.musica_proxima()
            return
        self.cache.update_play_count(caminho)
        self.player.stop()
        self._pending_play = True
        url = QUrl.fromLocalFile(str(caminho))
        self.player.setSource(url)
        self.musica_atual_label.setText(f"▶ {arquivo}")
        self.btn_play_pause.setText("⏸️ Pausar")
        for i in range(self.playlist_widget.count()):
            item = self.playlist_widget.item(i)
            if item.data(Qt.UserRole) == indice:
                self.playlist_widget.setCurrentItem(item)
                self.playlist_widget.scrollToItem(item)
                break
        self.append_log_player(f"Tocando: {arquivo}", "INFO")
        QTimer.singleShot(2000, self._fallback_play)
        if resume_position > 0:
            self._pending_position = resume_position
        else:
            self._pending_position = 0

    @Slot()
    def _fallback_play(self) -> None:
        if self._pending_play and self.player.playbackState() != QMediaPlayer.PlayingState:
            logger.warning("Fallback: iniciando reprodução por timeout.")
            self.append_log_player("Fallback: iniciando reprodução por timeout.", "WARNING")
            self.player.play()
            self._pending_play = False

    @Slot(QMediaPlayer.MediaStatus)
    def on_media_status_changed(self, status: QMediaPlayer.MediaStatus) -> None:
        if status == QMediaPlayer.LoadedMedia:
            if self._pending_play:
                self.player.play()
                self._pending_play = False
            if hasattr(self, '_pending_position') and self._pending_position > 0:
                self.player.setPosition(self._pending_position)
                self._pending_position = 0
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
            self.append_log_player("Pausado", "INFO")
        else:
            if self.current_index < 0:
                self.tocar_musica(0)
            else:
                self.player.play()
                self.btn_play_pause.setText("⏸️ Pausar")
                if self.current_index >= 0:
                    self.musica_atual_label.setText(f"▶ {self.playlist[self.current_index]}")
            self.append_log_player("Reproduzindo", "INFO")

    def parar_musica(self) -> None:
        self.player.stop()
        self.btn_play_pause.setText("▶ Play")
        self.slider_progresso.setValue(0)
        self.tempo_label.setText("00:00 / 00:00")
        self.musica_atual_label.setText("⏹️ Parado")
        self.slider_progresso.setEnabled(False)
        self._pending_play = False
        self.append_log_player("Parado", "INFO")

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
        idx = item.data(Qt.UserRole)
        if idx is not None and 0 <= idx < len(self.playlist):
            self.tocar_musica(idx)
        else:
            logger.warning(f"Índice inválido ou não encontrado no item: {item.text()}")

    def buscar_musicas_player(self) -> None:
        termo = self.busca_entry.text().strip().lower()
        self.playlist_widget.clear()
        if not termo:
            for idx, musica in enumerate(self.playlist):
                item = QListWidgetItem(musica)
                item.setData(Qt.UserRole, idx)
                self.playlist_widget.addItem(item)
        else:
            for idx, musica in enumerate(self.playlist):
                if termo in musica.lower():
                    item = QListWidgetItem(musica)
                    item.setData(Qt.UserRole, idx)
                    self.playlist_widget.addItem(item)

    # ========================================================================
    # MODOS
    # ========================================================================
    def toggle_aleatorio(self, checked: bool) -> None:
        self.random_mode = checked
        self.btn_aleatorio.setText("🔀 Aleatório ON" if checked else "🔀 Aleatório OFF")
        self.append_log_player(f"Aleatório: {'ON' if checked else 'OFF'}", "INFO")

    def toggle_continuo(self, checked: bool) -> None:
        self.loop_mode = checked
        self.btn_continuo.setText("🔁 Contínuo ON" if checked else "🔁 Contínuo OFF")
        self.append_log_player(f"Contínuo: {'ON' if checked else 'OFF'}", "INFO")

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
            'quiet': False,
            'no_warnings': False,
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
        self.append_log_baixador("🔍 Procurando informações da música...", "INFO")
        self.btn_baixar.setEnabled(False)

        def download_task() -> None:
            try:
                ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
                with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                    info = ydl.extract_info(url, download=False)
                    nome_artista = info.get('uploader', 'Desconhecido')
                    titulo_musica = info.get('title', 'Sem título')
                    self.append_log_baixador(f"🎤 Artista: {nome_artista}", "INFO")
                    self.append_log_baixador(f"🎵 Música: {titulo_musica}", "INFO")
                    self.append_log_baixador("🔍 Verificando duplicatas...", "INFO")
                    existe, arquivo_existente = verificar_duplicatas_avancado(pasta, nome_artista, titulo_musica)
                    if existe:
                        self.append_log_baixador(
                            f"⚠️ DUPLICATA: {arquivo_existente} já existe.", "WARNING"
                        )
                        self.show_message("info", "Duplicata", f"Essa música já existe na pasta!\n{arquivo_existente}")
                        return
                    self.append_log_baixador("✅ Nenhuma duplicata encontrada. Baixando...", "SUCCESS")
                pasta.mkdir(parents=True, exist_ok=True)
                ydl_opts = self._obter_opcoes_ytdlp(ffmpeg_path, pasta)
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    ydl.download([url])
                    self.append_log_baixador("✅ Download concluído com sucesso!", "SUCCESS")
                self.adicionar_historico(nome_artista, titulo_musica)
                self.show_message("info", "Sucesso", f"Música baixada com sucesso!\n{nome_artista} - {titulo_musica}")
                self.failure_manager.remove_success(url)
                if Path(self.player_folder_line.text().strip()) == pasta:
                    QTimer.singleShot(0, partial(self.carregar_playlist_sync, pasta, True, True))
            except Exception as e:
                logger.error(f"Erro no download único: {e}")
                self.append_log_baixador(f"❌ Erro: {e}", "ERROR")
                self.failure_manager.add_failure(
                    url=url,
                    artist=nome_artista if 'nome_artista' in locals() else "Desconhecido",
                    title=titulo_musica if 'titulo_musica' in locals() else "Sem título",
                    filename="",
                    playlist="",
                    error=e
                )
                self._atualizar_lista_falhas()
                self.show_message("critical", "Erro", f"Ocorreu um erro no download:\n{e}")
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
            self.append_log_baixador(f"❌ Erro ao ler arquivo: {e}", "ERROR")
            self.show_message("critical", "Erro", f"Erro ao ler o arquivo:\n{e}")
            return
        if not links:
            self.show_message("warning", "Aviso", "Nenhum link encontrado no arquivo!")
            return
        self.append_log_baixador(f"📚 Encontrados {len(links)} links no arquivo!", "INFO")
        self.append_log_baixador("🔍 Verificando duplicatas...", "INFO")
        self.btn_baixar_lote.setEnabled(False)

        def download_lote_task() -> None:
            musicas_baixadas = []
            musicas_duplicadas = []
            nomes_lote = []
            try:
                arquivos_pasta = [f.name for f in pasta.glob("*.mp3") if f.is_file()]
                self.append_log_baixador(f"📁 {len(arquivos_pasta)} arquivos na pasta", "INFO")
            except Exception as e:
                logger.error(f"Erro ao listar pasta: {e}")
                self.append_log_baixador("⚠️ Não foi possível ler a pasta", "WARNING")
            self.append_log_baixador("🔍 PASSO 1: Analisando e verificando duplicatas...", "INFO")
            informacoes = []
            for i, url in enumerate(links, 1):
                if not self._running:
                    break
                try:
                    self.append_log_baixador(f"[{i}/{len(links)}] Analisando...", "INFO")
                    ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
                    with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                        info = ydl.extract_info(url, download=False)
                        nome_artista = info.get('uploader', 'Desconhecido')
                        titulo_musica = info.get('title', 'Sem título')
                        existe_na_pasta, arquivo_existente = verificar_duplicatas_avancado(pasta, nome_artista, titulo_musica)
                        if existe_na_pasta:
                            musicas_duplicadas.append(f"{nome_artista} - {titulo_musica}")
                            self.append_log_baixador(
                                f"   ⏭️ DUPLICATA: {nome_artista} - {titulo_musica} (já existe)", "WARNING"
                            )
                            continue
                        eh_duplicata_lote = False
                        for nome_existente in nomes_lote:
                            if nomes_sao_parecidos(titulo_musica, nome_existente):
                                eh_duplicata_lote = True
                                break
                        if eh_duplicata_lote:
                            musicas_duplicadas.append(f"{nome_artista} - {titulo_musica}")
                            self.append_log_baixador(
                                f"   ⏭️ DUPLICATA NO LOTE: {nome_artista} - {titulo_musica} (pulada)", "WARNING"
                            )
                        else:
                            nomes_lote.append(titulo_musica)
                            informacoes.append((nome_artista, titulo_musica, url))
                            self.append_log_baixador(f"   ✅ {nome_artista} - {titulo_musica}", "SUCCESS")
                except Exception as e:
                    logger.error(f"Erro ao analisar link {url}: {e}")
                    self.append_log_baixador(f"   ❌ Erro: {e}", "ERROR")
                    self.failure_manager.add_failure(
                        url=url,
                        artist=nome_artista if 'nome_artista' in locals() else "Desconhecido",
                        title=titulo_musica if 'titulo_musica' in locals() else "Sem título",
                        filename="",
                        playlist=arquivo_path,
                        error=e
                    )
                    self._atualizar_lista_falhas()
            if not self._running:
                return
            if musicas_duplicadas:
                self.append_log_baixador(f"⚠️ {len(musicas_duplicadas)} duplicatas encontradas!", "WARNING")
            if not informacoes:
                self.append_log_baixador("❌ Nenhuma música nova para baixar.", "INFO")
                self.show_message("warning", "Aviso", "Nenhuma música nova para baixar!")
                self.btn_baixar_lote.setEnabled(True)
                return
            pasta.mkdir(parents=True, exist_ok=True)
            self.append_log_baixador(
                f"📥 PASSO 2: Baixando {len(informacoes)} músicas com 3 threads...", "INFO"
            )
            NUM_THREADS = 3
            musicas_com_erro = []
            ydl_opts_base = self._obter_opcoes_ytdlp(ffmpeg_path, pasta)

            def baixar_uma_musica(dados):
                nome_artista, titulo_musica, url = dados
                try:
                    with yt_dlp.YoutubeDL(ydl_opts_base) as ydl:
                        ydl.download([url])
                    self.failure_manager.remove_success(url)
                    return (nome_artista, titulo_musica, True, None)
                except Exception as e:
                    logger.error(f"Erro ao baixar {nome_artista} - {titulo_musica}: {e}")
                    self.failure_manager.add_failure(
                        url=url,
                        artist=nome_artista,
                        title=titulo_musica,
                        filename="",
                        playlist=arquivo_path,
                        error=e
                    )
                    self._atualizar_lista_falhas()
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
                        self.append_log_baixador(f"   ✅ {nome_artista} - {titulo_musica} baixada!", "SUCCESS")
                    else:
                        musicas_com_erro.append((nome_artista, titulo_musica, erro))
                        self.append_log_baixador(f"   ❌ Erro em {nome_artista} - {titulo_musica}: {erro}", "ERROR")
            if not self._running:
                return
            if musicas_baixadas:
                self.adicionar_bloco_historico(musicas_baixadas)
                self.append_log_baixador(f"🎉 Lote concluído: {len(musicas_baixadas)} baixadas!", "SUCCESS")
                self.append_log_baixador(f"   ⏭️ Duplicatas: {len(musicas_duplicadas)}", "INFO")
                if musicas_com_erro:
                    self.append_log_baixador(f"   ❌ Com erro: {len(musicas_com_erro)}", "ERROR")
                mensagem = f"{len(musicas_baixadas)} músicas baixadas!\n"
                if musicas_duplicadas:
                    mensagem += f"{len(musicas_duplicadas)} duplicatas puladas.\n"
                if musicas_com_erro:
                    mensagem += f"{len(musicas_com_erro)} com erro."
                self.show_message("info", "Sucesso", mensagem)
                if Path(self.player_folder_line.text().strip()) == pasta:
                    QTimer.singleShot(0, partial(self.carregar_playlist_sync, pasta, True, True))
            else:
                self.append_log_baixador("❌ Nenhuma música foi baixada.", "WARNING")
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
                self.append_log_player(f"⚠️ Arquivo já está na pasta destino: {origem.name}", "WARNING")
            elif destino.exists():
                duplicatas.append((str(origem), str(destino)))
                self.append_log_player(f"⚠️ Arquivo já existe: {origem.name} → {destino.name}", "WARNING")
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
                        self.append_log_player(f"⏳ Substituindo: {Path(origem).name}", "INFO")
                    else:
                        self.append_log_player(f"⏭️ Ignorando: {Path(origem).name}", "INFO")
            else:
                self.append_log_player("⏭️ Todas as duplicatas ignoradas.", "INFO")
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
        self.import_thread.file_copied.connect(lambda nome: self.append_log_player(f"📥 {nome}", "INFO"))
        self.import_thread.error.connect(lambda msg: self.append_log_player(f"❌ {msg}", "ERROR"))
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
            self.append_log_player("⏹️ Importação cancelada pelo usuário.", "WARNING")

    def _import_finished(self, count: int) -> None:
        if hasattr(self, 'progress_dialog') and self.progress_dialog:
            self.progress_dialog.close()
        self.append_log_player(f"✅ Importação concluída: {count} arquivo(s) copiado(s).", "SUCCESS")
        for widget in self.findChildren(QPushButton):
            if widget.text() == "📥 Importar":
                widget.setEnabled(True)
        if count > 0:
            self.show_message("info", "Sucesso", f"{count} música(s) importada(s)!")
            pasta = Path(self.player_folder_line.text().strip())
            self.carregar_playlist_sync(pasta, force=True, preserve_position=True)
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

    # ========================================================================
    # ENCERRAMENTO
    # ========================================================================
    def closeEvent(self, event) -> None:
        self._running = False
        if self._reload_thread and self._reload_thread.isRunning():
            self._reload_thread.quit()
            self._reload_thread.wait(1000)
        if self._normalize_thread and self._normalize_thread.isRunning():
            self._normalize_thread.quit()
            self._normalize_thread.wait(1000)
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
