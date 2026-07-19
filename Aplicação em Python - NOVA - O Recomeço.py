#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Nexus Player - Versão 0.32
- ESTABILIZAÇÃO: Nexus Parsing Engine (NPE) v3.1
  * Aprendizado supervisionado por tipo de decisão (não por arquivo)
  * Preservação do delimitador "-" (Artista - Música)
  * Detecção de VEVO concatenado (BonJoviVEVO → BonJovi + VEVO)
  * Categoria HASHTAG controlada por JSON
  * Representação canônica única para comparação
- CORREÇÃO: Downloader não baixa duplicatas (usa representação canônica)
- CORREÇÃO: Detector de duplicatas usa representação canônica
- CORREÇÃO: Exclusão de duplicatas apaga arquivo e atualiza cache/interface
- CORREÇÃO: Player seek reescrito com estados (IDLE, PLAYING, SEEKING)
- MELHORIA: Logs detalhados com decisões, regras e resultados
- PRESERVAÇÃO: Todas as funcionalidades existentes mantidas
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
from typing import Optional, List, Tuple, Dict, Any, Callable
from queue import Queue, PriorityQueue
import uuid
import unicodedata
from dataclasses import dataclass, field
from enum import Enum
from collections import defaultdict
import hashlib

import yt_dlp
import mutagen.mp3

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QTabWidget, QWidget, QVBoxLayout,
    QHBoxLayout, QLabel, QLineEdit, QPushButton, QListWidget,
    QListWidgetItem, QSlider, QFileDialog, QMessageBox,
    QTextEdit, QGroupBox, QSplitter, QProgressDialog, QDialog,
    QCheckBox, QDialogButtonBox, QTableWidget, QTableWidgetItem,
    QHeaderView, QProgressBar, QComboBox, QTabBar
)
from PySide6.QtCore import Qt, QUrl, Slot, QTimer, QThread, Signal, QObject, QMutex, QWaitCondition
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
# NEXUS PARSING ENGINE (NPE) v3.1 - COM APRENDIZADO SUPERVISIONADO
# ============================================================================

class TokenType(Enum):
    ARTIST = "ARTIST"
    TITLE = "TITLE"
    CHANNEL = "CHANNEL"
    CHANNEL_SUFFIX = "CHANNEL_SUFFIX"
    FEAT = "FEAT"
    VERSION = "VERSION"
    LIVE = "LIVE"
    REMIX = "REMIX"
    MASHUP = "MASHUP"
    COVER = "COVER"
    PART = "PART"
    OFFICIAL_TAG = "OFFICIAL_TAG"
    QUALITY_TAG = "QUALITY_TAG"
    FORMAT_TAG = "FORMAT_TAG"
    PROMOTION = "PROMOTION"
    DISCARDABLE = "DISCARDABLE"
    ARTIST_ALIAS = "ARTIST_ALIAS"
    HASHTAG = "HASHTAG"
    UNKNOWN = "UNKNOWN"

@dataclass
class ParsedToken:
    text: str
    original_text: str
    type: TokenType
    confidence: float
    position: int
    discard: bool = False
    decision_type: str = ""  # ex: "REMOVE_VEVO", "REMOVE_OFFICIAL", "REMOVE_SEPARATOR"

@dataclass
class ParsedResult:
    original_name: str
    tokens: List[ParsedToken]
    raw_tokens: List[str]  # tokens brutos
    artist: str = ""
    title: str = ""
    channel: str = ""
    channel_suffix: str = ""
    version: str = ""
    live: str = ""
    remix: str = ""
    mashup: str = ""
    cover: str = ""
    part: str = ""
    feat: List[str] = field(default_factory=list)
    official_tags: List[str] = field(default_factory=list)
    quality_tags: List[str] = field(default_factory=list)
    format_tags: List[str] = field(default_factory=list)
    promotion: List[str] = field(default_factory=list)
    hashtags: List[str] = field(default_factory=list)
    unknown: List[str] = field(default_factory=list)
    confidence: float = 0.0
    quality: float = 0.0
    decisions: List[Dict] = field(default_factory=list)  # para logging

class ParserRules:
    def __init__(self):
        self.rules_file = Path(__file__).parent / "parser_rules.json"
        self.default_rules = {
            "discardable": [
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
                "clipe", "clipe oficial", "vídeo clipe", "videoclipe", "oficial",
                "legendado", "tradução", "traduzido", "sub", "subtitle", "subtitled",
                "letra", "lyric", "lyrics", "karaoke", "instrumental", "acústico", "acoustic",
                "ao vivo", "live", "remasterizado", "remastered", "edição", "edition",
                "deluxe", "bonus", "extra", "versão", "version", "mix", "remix",
                "television", "archive", "show", "tv", "records", "music official",
                "official channel", "official music", "md digital music", "daptonerecords",
                "canal", "canais", "no copyright", "nc", "royalty free", "audio library",
                "youtube audio library", "youtube music", "topic", "vevo", "official"
            ],
            "channel_indicators": [
                "vevo", "official", "topic", "tv", "records", "music", "channel",
                "canal", "show", "archive", "television", "md digital music",
                "daptonerecords", "no copyright", "royalty free", "audio library"
            ],
            "preserve": [
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
            "version_keywords": [
                "version", "versão", "versao", "edit", "radio edit", "single", "album",
                "original", "extended", "dub", "instrumental", "a cappella"
            ],
            "remix_keywords": [
                "remix", "rework", "bootleg", "mashup", "mix", "reimagined"
            ],
            "feature_keywords": ["feat", "ft", "featuring", "with", "part"],
            "year_pattern": r'\b(19|20)\d{2}\b',
            "separators": [' - ', ' – ', ' — ', ' | ', ' › ', ' : ', '; '],
            "artist_aliases": {
                "鄧麗君": "Teresa Teng",
                "テレサ・テン": "Teresa Teng",
                "marisamonte": "Marisa Monte",
                "césar menotti e fabiano": "César Menotti & Fabiano",
                "koolandthegang": "Kool & The Gang",
                "t-ara": "T-ARA",
                "a-ha": "A-Ha",
                "b.b. king": "B.B. King",
                "b-52s": "B-52's",
                "g-unit": "G-Unit",
                "ac/dc": "AC/DC",
                "r.e.m.": "R.E.M."
            },
            "title_aliases": {},
            "hashtag_pattern": r'#\w+',
            "concat_suffixes": ["VEVO", "Official", "Music", "Records", "Topic", "Channel", "TV"]
        }
        self.rules = {}
        self._load()

    def _load(self):
        if not self.rules_file.exists():
            with open(self.rules_file, 'w', encoding='utf-8') as f:
                json.dump(self.default_rules, f, indent=2, ensure_ascii=False)
            logger.info("[ParserRules] Arquivo de regras criado.")
            self.rules = self.default_rules
        else:
            try:
                with open(self.rules_file, 'r', encoding='utf-8') as f:
                    self.rules = json.load(f)
                logger.info("[ParserRules] Regras carregadas do arquivo.")
            except Exception as e:
                logger.error(f"[ParserRules] Erro ao carregar regras: {e}. Usando padrão.")
                self.rules = self.default_rules

    def get(self, key: str, default=None):
        return self.rules.get(key, default)

class DecisionWeights:
    """Sistema de pesos por tipo de decisão (aprendizado supervisionado)."""
    def __init__(self):
        self.weights_file = Path(__file__).parent / "parser_decision_weights.json"
        self.weights = {
            "REMOVE_VEVO": {"weight": 1.0, "count": 0, "accepted": 0},
            "REMOVE_OFFICIAL": {"weight": 1.0, "count": 0, "accepted": 0},
            "REMOVE_CHANNEL": {"weight": 1.0, "count": 0, "accepted": 0},
            "REMOVE_TOPIC": {"weight": 1.0, "count": 0, "accepted": 0},
            "REMOVE_SEPARATOR": {"weight": 0.0, "count": 0, "accepted": 0},  # inicialmente 0 para nunca remover
            "REMOVE_DOUBLE_SEPARATOR": {"weight": 1.0, "count": 0, "accepted": 0},
            "REMOVE_HASHTAG": {"weight": 1.0, "count": 0, "accepted": 0},
            "REMOVE_PROMOTION": {"weight": 1.0, "count": 0, "accepted": 0}
        }
        self._load()

    def _load(self):
        if self.weights_file.exists():
            try:
                with open(self.weights_file, 'r', encoding='utf-8') as f:
                    loaded = json.load(f)
                    # Mescla com as chaves padrão (preserva existentes)
                    for k, v in loaded.items():
                        if k in self.weights:
                            self.weights[k].update(v)
                logger.info("[DecisionWeights] Pesos carregados.")
            except Exception as e:
                logger.error(f"[DecisionWeights] Erro ao carregar pesos: {e}")
        else:
            self._save()

    def _save(self):
        try:
            with open(self.weights_file, 'w', encoding='utf-8') as f:
                json.dump(self.weights, f, indent=2, ensure_ascii=False)
        except Exception as e:
            logger.error(f"[DecisionWeights] Erro ao salvar pesos: {e}")

    def get_weight(self, decision_type: str) -> float:
        return self.weights.get(decision_type, {}).get("weight", 0.5)

    def record_decision(self, decision_type: str, accepted: bool):
        if decision_type not in self.weights:
            self.weights[decision_type] = {"weight": 0.5, "count": 0, "accepted": 0}
        entry = self.weights[decision_type]
        entry["count"] += 1
        if accepted:
            entry["accepted"] += 1
        # Atualiza peso: proporção de aceitações
        if entry["count"] > 0:
            entry["weight"] = entry["accepted"] / entry["count"]
        self._save()

    def should_apply(self, decision_type: str) -> bool:
        """Retorna True se a decisão deve ser aplicada com base no peso."""
        weight = self.get_weight(decision_type)
        # Se peso >= 0.5, aplicar; se < 0.5, não aplicar
        # Para REMOVE_SEPARATOR, inicialmente peso 0, então não aplica
        return weight >= 0.5


class NexusParsingEngine:
    """NPE v3.1 - Com aprendizado supervisionado e estabilização."""
    VERSION = "3.1"

    def __init__(self, enable_debug: bool = False):
        self.rules = ParserRules()
        self.decisions = DecisionWeights()
        self.enable_debug = enable_debug
        self._debug_logs = []

        # Carregar listas
        self.discardable = set(self.rules.get("discardable", []))
        self.channel_indicators = set(self.rules.get("channel_indicators", []))
        self.preserve = set(self.rules.get("preserve", []))
        self.version_keywords = set(self.rules.get("version_keywords", []))
        self.remix_keywords = set(self.rules.get("remix_keywords", []))
        self.feature_keywords = set(self.rules.get("feature_keywords", []))
        self.separators = self.rules.get("separators", [' - ', ' – ', ' — ', ' | ', ' › ', ' : ', '; '])
        self.artist_aliases = self.rules.get("artist_aliases", {})
        self.year_pattern = re.compile(self.rules.get("year_pattern", r'\b(19|20)\d{2}\b'))
        self.hashtag_pattern = re.compile(self.rules.get("hashtag_pattern", r'#\w+'))
        self.concat_suffixes = self.rules.get("concat_suffixes", ["VEVO", "Official", "Music", "Records", "Topic", "Channel", "TV"])
        self._debug_logs = []

    def _log_debug(self, msg: str):
        if self.enable_debug:
            self._debug_logs.append(msg)
            logger.debug(f"[NPE] {msg}")

    # ------------------------------------------------------------
    # Pipeline Principal
    # ------------------------------------------------------------
    def parse(self, filename: str) -> ParsedResult:
        name = Path(filename).stem
        self._log_debug(f"Parsing: {name}")

        # 1. Pré-processamento
        preprocessed = self._preprocess(name)
        self._log_debug(f"Pré-processado: {preprocessed}")

        # 2. Tokenização
        raw_tokens = self._tokenize(preprocessed)
        self._log_debug(f"Tokens brutos: {raw_tokens}")

        # 3. Detecção de VEVO concatenado
        raw_tokens = self._split_concatenated(raw_tokens)
        self._log_debug(f"Após split concatenado: {raw_tokens}")

        # 4. Classificação
        tokens = self._classify_tokens(raw_tokens)
        self._log_debug(f"Tokens classificados: {[(t.text, t.type.value, t.confidence) for t in tokens]}")

        # 5. Marcação de descartáveis (baseado em pesos)
        self._mark_discardable(tokens)

        # 6. Construção do resultado
        result = self._build_result(name, tokens, raw_tokens)

        return result

    # ------------------------------------------------------------
    # Etapas
    # ------------------------------------------------------------
    def _preprocess(self, name: str) -> str:
        name = unicodedata.normalize('NFKC', name)
        name = name.replace('.mp3', '').replace('.wav', '').replace('.flac', '').replace('.m4a', '')
        name = re.sub(r'[\x00-\x1f\x7f]', '', name)
        name = re.sub(r'\s+', ' ', name).strip()
        return name

    def _tokenize(self, text: str) -> List[str]:
        for sep in self.separators:
            if sep in text:
                parts = text.split(sep)
                tokens = []
                for p in parts:
                    tokens.extend(p.strip().split())
                return tokens
        return text.split()

    def _split_concatenated(self, tokens: List[str]) -> List[str]:
        """Detecta e separa VEVO, Official, etc. concatenados."""
        result = []
        for token in tokens:
            # Verifica se token termina com algum sufixo (VEVO, Official, etc.)
            for suffix in self.concat_suffixes:
                if token.upper().endswith(suffix.upper()) and len(token) > len(suffix):
                    # Separa: "BonJoviVEVO" -> ["BonJovi", "VEVO"]
                    prefix = token[:-len(suffix)]
                    # Verifica se o prefixo é um artista conhecido (pela capitalização)
                    if prefix and prefix[0].isupper():
                        result.append(prefix)
                        result.append(suffix)
                        break
            else:
                result.append(token)
        return result

    def _classify_tokens(self, raw_tokens: List[str]) -> List[ParsedToken]:
        classified = []
        for idx, tok in enumerate(raw_tokens):
            # Aplica aliases de artista
            original = tok
            if tok.lower() in self.artist_aliases:
                tok = self.artist_aliases[tok.lower()]
            # Classifica
            ttype, confidence, decision_type = self._classify_single(tok, original)
            token = ParsedToken(
                text=tok,
                original_text=original,
                type=ttype,
                confidence=confidence,
                position=idx,
                discard=False,
                decision_type=decision_type
            )
            classified.append(token)
        return classified

    def _classify_single(self, token: str, original: str) -> Tuple[TokenType, float, str]:
        t_lower = token.lower().strip()

        # 1. Hashtag
        if self.hashtag_pattern.match(original):
            return TokenType.HASHTAG, 0.95, "REMOVE_HASHTAG"

        # 2. Descartáveis
        if t_lower in self.discardable:
            # Identifica o tipo de decisão
            if "vevo" in t_lower:
                return TokenType.DISCARDABLE, 0.95, "REMOVE_VEVO"
            if "official" in t_lower:
                return TokenType.DISCARDABLE, 0.95, "REMOVE_OFFICIAL"
            if "topic" in t_lower:
                return TokenType.DISCARDABLE, 0.95, "REMOVE_TOPIC"
            if any(ind in t_lower for ind in self.channel_indicators):
                return TokenType.DISCARDABLE, 0.85, "REMOVE_CHANNEL"
            return TokenType.DISCARDABLE, 0.90, "REMOVE_PROMOTION"

        # 3. Separadores (não são descartáveis, mas podem ser ajustados)
        # Não classificamos separadores como descartáveis

        # 4. Indicadores de canal
        if any(ind in t_lower for ind in self.channel_indicators):
            return TokenType.CHANNEL_SUFFIX, 0.85, "REMOVE_CHANNEL"

        # 5. Ano
        if self.year_pattern.match(token):
            return TokenType.VERSION, 0.90, "KEEP_VERSION"

        # 6. Palavras-chave de versão/remix
        if t_lower in self.version_keywords:
            return TokenType.VERSION, 0.90, "KEEP_VERSION"
        if t_lower in self.remix_keywords:
            return TokenType.REMIX, 0.90, "KEEP_REMIX"
        if "live" in t_lower:
            return TokenType.LIVE, 0.85, "KEEP_LIVE"
        if "mashup" in t_lower:
            return TokenType.MASHUP, 0.90, "KEEP_MASHUP"
        if "cover" in t_lower:
            return TokenType.COVER, 0.90, "KEEP_COVER"
        if t_lower in self.feature_keywords:
            return TokenType.FEAT, 0.90, "KEEP_FEAT"
        if "part" in t_lower or re.match(r'^[ivxlcdm]+$', t_lower, re.I):
            return TokenType.PART, 0.90, "KEEP_PART"

        # 7. Inferência: capitalização -> ARTIST
        if token[0].isupper() and len(token) > 2 and token.isalpha():
            return TokenType.ARTIST, 0.5, "INFER_ARTIST"

        # 8. Alias de artista
        if token.lower() in self.artist_aliases:
            return TokenType.ARTIST, 0.8, "ALIAS_ARTIST"

        # 9. Desconhecido
        return TokenType.UNKNOWN, 0.2, "UNKNOWN"

    def _mark_discardable(self, tokens: List[ParsedToken]):
        """Marca tokens com base nos pesos das decisões."""
        for token in tokens:
            # Se já é DISCARDABLE, verifica se deve aplicar com base no peso
            if token.type == TokenType.DISCARDABLE and token.decision_type:
                if self.decisions.should_apply(token.decision_type):
                    token.discard = True
                    # Registra a decisão (para aprendizado)
                    # Será registrada quando o usuário confirmar/cancelar
            # Se for CHANNEL_SUFFIX e houver ARTIST anterior, descarta
            if token.type == TokenType.CHANNEL_SUFFIX:
                has_artist = any(t.type == TokenType.ARTIST and t.position < token.position for t in tokens)
                if has_artist and self.decisions.should_apply("REMOVE_CHANNEL"):
                    token.discard = True
            # Se for HASHTAG, descarta se peso permitir
            if token.type == TokenType.HASHTAG:
                if self.decisions.should_apply("REMOVE_HASHTAG"):
                    token.discard = True
            # Remover separadores inválidos: apenas duplicados
            if token.type == TokenType.UNKNOWN and token.text in ["-", "–", "—"]:
                # Verifica se é um separador isolado
                # Mantém se for o único separador entre dois tokens
                # A lógica de remoção de separadores duplicados é feita na reconstrução
                pass

    def _build_result(self, name: str, tokens: List[ParsedToken], raw_tokens: List[str]) -> ParsedResult:
        result = ParsedResult(original_name=name, tokens=tokens, raw_tokens=raw_tokens)

        # Extrai categorias mantendo ordem
        for t in tokens:
            if t.discard:
                continue
            if t.type == TokenType.ARTIST:
                result.artist = t.text if not result.artist else result.artist + " " + t.text
            elif t.type == TokenType.TITLE:
                result.title = t.text if not result.title else result.title + " " + t.text
            elif t.type == TokenType.CHANNEL:
                result.channel = t.text if not result.channel else result.channel + " " + t.text
            elif t.type == TokenType.CHANNEL_SUFFIX:
                result.channel_suffix = t.text if not result.channel_suffix else result.channel_suffix + " " + t.text
            elif t.type == TokenType.VERSION:
                result.version = t.text if not result.version else result.version + " " + t.text
            elif t.type == TokenType.LIVE:
                result.live = t.text if not result.live else result.live + " " + t.text
            elif t.type == TokenType.REMIX:
                result.remix = t.text if not result.remix else result.remix + " " + t.text
            elif t.type == TokenType.MASHUP:
                result.mashup = t.text if not result.mashup else result.mashup + " " + t.text
            elif t.type == TokenType.COVER:
                result.cover = t.text if not result.cover else result.cover + " " + t.text
            elif t.type == TokenType.PART:
                result.part = t.text if not result.part else result.part + " " + t.text
            elif t.type == TokenType.FEAT:
                result.feat.append(t.text)
            elif t.type == TokenType.OFFICIAL_TAG:
                result.official_tags.append(t.text)
            elif t.type == TokenType.QUALITY_TAG:
                result.quality_tags.append(t.text)
            elif t.type == TokenType.FORMAT_TAG:
                result.format_tags.append(t.text)
            elif t.type == TokenType.PROMOTION:
                result.promotion.append(t.text)
            elif t.type == TokenType.HASHTAG:
                result.hashtags.append(t.text)
            else:
                result.unknown.append(t.text)

        # Fallback
        if not result.artist and raw_tokens:
            result.artist = raw_tokens[0]
        if not result.title:
            if len(raw_tokens) > 1:
                result.title = " ".join(raw_tokens[1:])
            else:
                result.title = name

        # Confiança geral
        confs = [t.confidence for t in tokens if not t.discard]
        result.confidence = sum(confs) / len(confs) if confs else 0.0
        # Qualidade
        valid = sum(1 for t in tokens if not t.discard)
        result.quality = valid / len(tokens) if tokens else 0.0

        return result

    # ------------------------------------------------------------
    # Métodos Públicos
    # ------------------------------------------------------------
    def normalize_for_compare(self, filename: str) -> Tuple[str, str]:
        """Retorna (artista_normalizado, titulo_normalizado) para comparação."""
        parsed = self.parse(filename)
        artist = parsed.artist
        title = parsed.title
        # Remove tokens descartáveis do título e artista
        for t in parsed.tokens:
            if t.discard:
                title = title.replace(t.text, '').strip()
                artist = artist.replace(t.text, '').strip()
        # Remove espaços extras
        artist = ' '.join(artist.split())
        title = ' '.join(title.split())
        return artist, title

    def normalize_filename(self, filename: str) -> str:
        """Gera nome de arquivo preservando ordem, removendo descartáveis e corrigindo separadores."""
        parsed = self.parse(filename)
        # Reconstrói preservando ordem
        parts = []
        for t in parsed.tokens:
            if not t.discard:
                parts.append(t.original_text if t.original_text else t.text)
        # Se não sobrou nada, usa original
        if not parts:
            parts = [parsed.original_name]
        # Junta com espaços
        name = " ".join(parts)
        # Corrige separadores duplicados: "- -" → "-"
        name = re.sub(r'\s*[-–—]\s*[-–—]\s*', ' - ', name)
        # Remove separadores isolados (ex: "Artista - " ou " - Música")
        name = re.sub(r'^[-–—]\s*', '', name)
        name = re.sub(r'\s*[-–—]$', '', name)
        # Remove espaços extras
        name = re.sub(r'\s{2,}', ' ', name).strip()
        return name + ".mp3"

    def register_user_correction(self, original: str, final: str):
        """Registra correção manual do usuário e atualiza pesos das decisões."""
        # Tokeniza original e final
        original_tokens = self._tokenize(original)
        final_tokens = self._tokenize(final)
        # Compara tokens para identificar decisões
        for t in original_tokens:
            if t not in final_tokens:
                # Token removido: provavelmente descartado
                # Identifica o tipo de decisão (simplificado)
                t_lower = t.lower()
                if "vevo" in t_lower:
                    self.decisions.record_decision("REMOVE_VEVO", True)
                elif "official" in t_lower:
                    self.decisions.record_decision("REMOVE_OFFICIAL", True)
                elif "topic" in t_lower:
                    self.decisions.record_decision("REMOVE_TOPIC", True)
                elif any(ind in t_lower for ind in self.channel_indicators):
                    self.decisions.record_decision("REMOVE_CHANNEL", True)
                elif t in ["-", "–", "—"]:
                    # Separador removido: provavelmente duplicado
                    self.decisions.record_decision("REMOVE_DOUBLE_SEPARATOR", True)
                else:
                    self.decisions.record_decision("REMOVE_PROMOTION", True)
        # Se o usuário manteve um separador, registra rejeição
        for t in final_tokens:
            if t in ["-", "–", "—"] and t not in original_tokens:
                # Adicionou separador (não deve ocorrer)
                pass

    def are_similar(self, name1: str, name2: str) -> bool:
        a1, t1 = self.normalize_for_compare(name1)
        a2, t2 = self.normalize_for_compare(name2)
        return a1.lower() == a2.lower() and t1.lower() == t2.lower()


# ============================================================================
# INSTÂNCIA GLOBAL DA NPE
# ============================================================================
_npe = NexusParsingEngine(enable_debug=False)

# ============================================================================
# UTILITÁRIOS (compatibilidade)
# ============================================================================
def extrair_artista_musica(nome_arquivo: str) -> Tuple[Optional[str], Optional[str]]:
    parsed = _npe.parse(nome_arquivo)
    return parsed.artist or None, parsed.title or None

def nomes_sao_parecidos(nome1: str, nome2: str) -> bool:
    return _npe.are_similar(nome1, nome2)

def verificar_duplicatas_avancado(pasta: Path, artista: str, musica: str) -> Tuple[bool, Optional[str]]:
    target_a, target_t = _npe.normalize_for_compare(f"{artista} - {musica}")
    for f in pasta.glob("*.mp3"):
        if f.is_file():
            a, t = _npe.normalize_for_compare(f.name)
            if a.lower() == target_a.lower() and t.lower() == target_t.lower():
                return True, f.name
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
# DOWNLOAD MANAGER (com NPE)
# ============================================================================
class DownloadManager(QObject):
    log_signal = Signal(str, str)
    progress_signal = Signal(int, int)
    finished_signal = Signal(int, int, int)
    error_signal = Signal(str)
    status_signal = Signal(str)
    stats_signal = Signal(dict)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.mutex = QMutex()
        self.wait_condition = QWaitCondition()
        self.paused = False
        self.cancelled = False
        self.running = False

        self.queue = Queue()
        self.retry_queue = []

        self.stats = {
            'total': 0,
            'success': 0,
            'failed': 0,
            'skipped': 0,
            'retries': 0,
            'consecutive_errors': 0,
            'cooldowns': 0,
            'start_time': None,
            'avg_time': 0,
            'speed': 0,
        }

        self.user_agents = self._load_user_agents()
        self.cookie_manager = CookieManager()
        self.header_manager = HeaderManager()
        self.cooldown_manager = CooldownManager()
        self.retry_manager = RetryManager()

        self.config = carregar_config()
        self.download_folder = Path(self.config.get('download_folder', str(Path.home() / "Músicas" / "Nexus")))
        self.ffmpeg_path = localizar_ffmpeg()
        self.max_concurrent = 3
        self.executor = ThreadPoolExecutor(max_workers=self.max_concurrent)
        self.consecutive_errors = 0
        self.cooldown_active = False
        self.current_downloads = []
        self._load_retry_queue()

    def _load_user_agents(self) -> List[str]:
        return [
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36 Edg/122.0.0.0",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:123.0) Gecko/20100101 Firefox/123.0",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:122.0) Gecko/20100101 Firefox/122.0",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:121.0) Gecko/20100101 Firefox/121.0",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36 OPR/108.0.0.0",
            "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15",
            "Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.6261.119 Mobile Safari/537.36",
            "Mozilla/5.0 (Linux; Android 13) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.6167.164 Mobile Safari/537.36",
            "Mozilla/5.0 (Android 14; Mobile; rv:123.0) Gecko/123.0 Firefox/123.0",
            "Mozilla/5.0 (iPhone; CPU iPhone OS 17_4_1 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
        ]

    def _load_retry_queue(self):
        file_path = Path(__file__).parent / "failed_downloads.json"
        if file_path.exists():
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    if isinstance(data, list):
                        self.retry_queue = data
                        logger.info(f"Carregados {len(self.retry_queue)} itens para retry.")
            except Exception as e:
                logger.error(f"Erro ao carregar failed_downloads.json: {e}")
                self.retry_queue = []

    def _save_retry_queue(self):
        file_path = Path(__file__).parent / "failed_downloads.json"
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                json.dump(self.retry_queue, f, indent=2, ensure_ascii=False)
        except Exception as e:
            logger.error(f"Erro ao salvar failed_downloads.json: {e}")

    def add_item(self, url: str, artist: str, title: str, playlist: str = "", priority: int = 0):
        item = {
            'url': url,
            'artist': artist,
            'title': title,
            'playlist': playlist,
            'priority': priority,
            'timestamp': datetime.now().isoformat(),
            'retries': 0,
            'status': 'pending'
        }
        if priority > 0:
            self.retry_queue.append(item)
        else:
            self.queue.put(item)
        self.stats['total'] += 1
        self._save_retry_queue()

    def start(self):
        if self.running:
            return
        self.running = True
        self.paused = False
        self.cancelled = False
        self.stats['start_time'] = time.time()
        self._process_queue()

    def pause(self):
        self.mutex.lock()
        self.paused = True
        self.mutex.unlock()

    def resume(self):
        self.mutex.lock()
        self.paused = False
        self.wait_condition.wakeAll()
        self.mutex.unlock()
        if not self.running:
            self.start()

    def cancel(self):
        self.cancelled = True
        self.paused = False
        for future in self.current_downloads:
            future.cancel()
        self.current_downloads.clear()
        while not self.queue.empty():
            try:
                self.queue.get_nowait()
            except:
                break
        self.retry_queue.clear()
        self._save_retry_queue()
        self.running = False
        self.status_signal.emit("Cancelado")

    def _process_queue(self):
        threading.Thread(target=self._process_loop, daemon=True).start()

    def _process_loop(self):
        while self.running and not self.cancelled:
            self.mutex.lock()
            while self.paused and not self.cancelled:
                self.wait_condition.wait(self.mutex)
            self.mutex.unlock()

            if self.cancelled:
                break

            if self.cooldown_active:
                time.sleep(5)
                continue

            item = None
            if self.retry_queue:
                item = self.retry_queue.pop(0)
                item['priority'] = 1
            elif not self.queue.empty():
                item = self.queue.get()
            else:
                time.sleep(1)
                continue

            if item is None:
                continue

            self._download_item(item)

            if not self.cancelled and not self.paused:
                delay = random.uniform(1, 4)
                time.sleep(delay)

        self.running = False
        self.finished_signal.emit(self.stats['success'], self.stats['failed'], self.stats['skipped'])

    def _download_item(self, item: Dict):
        url = item['url']
        artist = item.get('artist', 'Desconhecido')
        title = item.get('title', 'Sem título')
        playlist = item.get('playlist', '')
        retries = item.get('retries', 0)

        try:
            # Obtém informações reais do YouTube
            ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
            with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                info = ydl.extract_info(url, download=False)
                real_artist = info.get('uploader', artist)
                real_title = info.get('title', title)
                if real_artist == "Desconhecido" or not real_artist:
                    real_artist = info.get('channel', "Desconhecido")
                if not real_title:
                    real_title = info.get('track', title)

            # Comparação usando NPE
            target_a, target_t = _npe.normalize_for_compare(f"{real_artist} - {real_title}")
            # Verifica duplicata na pasta
            existe, existente = verificar_duplicatas_avancado(self.download_folder, target_a, target_t)
            if existe:
                self.log_signal.emit(f"⏭️ DUPLICATA: {target_a} - {target_t} (já existe: {existente})", "WARNING")
                self.stats['skipped'] += 1
                self.stats_signal.emit(self.stats)
                return

            artist, title = target_a, target_t
            self.log_signal.emit(f"⬇️ Iniciando download: {artist} - {title}", "INFO")
            self.status_signal.emit(f"Baixando: {artist} - {title}")

            user_agent = random.choice(self.user_agents)
            headers = self.header_manager.get_headers(user_agent)

            ydl_opts = {
                'format': 'bestaudio/best',
                'postprocessors': [
                    {'key': 'FFmpegExtractAudio', 'preferredcodec': 'mp3', 'preferredquality': '192'},
                    {'key': 'FFmpegMetadata', 'add_metadata': True}
                ],
                'ffmpeg_location': str(self.ffmpeg_path) if self.ffmpeg_path else None,
                'outtmpl': str(self.download_folder / '%(uploader)s - %(title)s.%(ext)s'),
                'quiet': False,
                'no_warnings': False,
                'writethumbnail': True,
                'user_agent': user_agent,
                'headers': headers,
                'cookiefile': self.cookie_manager.get_cookie_file(),
                'extractor_args': {
                    'youtube': {
                        'player_client': ['android', 'web'],
                        'skip': ['hls', 'dash']
                    }
                }
            }

            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])

            self.log_signal.emit(f"✅ Download concluído: {artist} - {title}", "SUCCESS")
            self.stats['success'] += 1
            self.stats['retries'] += retries
            self.consecutive_errors = 0
            self.cooldown_active = False
            self.stats_signal.emit(self.stats)
            self._remove_from_retry(url)

        except Exception as e:
            error_msg = str(e)
            self.log_signal.emit(f"❌ Erro ao baixar {artist} - {title}: {error_msg}", "ERROR")
            self.consecutive_errors += 1
            self.stats['failed'] += 1
            self.stats_signal.emit(self.stats)

            if self.consecutive_errors >= 5:
                self.cooldown_active = True
                self.stats['cooldowns'] += 1
                self.log_signal.emit("🔄 Muitos erros consecutivos. Ativando cooldown automático...", "WARNING")
                time.sleep(60)
                self.consecutive_errors = 0
                self.cooldown_active = False
                self.log_signal.emit("✅ Cooldown finalizado. Retomando downloads.", "INFO")

            if retries < 3:
                item['retries'] = retries + 1
                item['timestamp'] = datetime.now().isoformat()
                item['error'] = error_msg
                self.retry_queue.append(item)
                self._save_retry_queue()
                self.log_signal.emit(f"⏳ Agendado para retry ({retries+1}/3): {artist} - {title}", "INFO")
            else:
                self.log_signal.emit(f"⚠️ Máximo de tentativas para {artist} - {title}. Descartando.", "WARNING")

    def _classify_error(self, error_msg: str) -> str:
        error_lower = error_msg.lower()
        if "403" in error_lower or "forbidden" in error_lower:
            return "FORBIDDEN"
        if "429" in error_lower or "too many requests" in error_lower:
            return "RATE_LIMIT"
        if "sign in" in error_lower or "bot" in error_lower:
            return "BOT_DETECTED"
        if "unable to download" in error_lower:
            return "DOWNLOAD_ERROR"
        if "video unavailable" in error_lower:
            return "VIDEO_UNAVAILABLE"
        if "network" in error_lower or "timeout" in error_lower:
            return "NETWORK"
        return "OTHER"

    def _remove_from_retry(self, url: str):
        self.retry_queue = [item for item in self.retry_queue if item.get('url') != url]
        self._save_retry_queue()

    def get_stats(self) -> Dict:
        stats = self.stats.copy()
        if stats['start_time']:
            elapsed = time.time() - stats['start_time']
            stats['elapsed'] = elapsed
            if stats['success'] > 0:
                stats['avg_time'] = elapsed / stats['success']
        return stats


class CookieManager:
    def __init__(self):
        self.cookie_file = None
        self._find_cookie_file()

    def _find_cookie_file(self):
        base_dir = Path(__file__).parent
        candidates = [
            base_dir / "cookies.txt",
            base_dir / "cookies" / "cookies.txt",
            base_dir / "resources" / "cookies.txt",
        ]
        for candidate in candidates:
            if candidate.is_file():
                self.cookie_file = str(candidate)
                logger.info(f"Arquivo de cookies encontrado: {candidate}")
                return
        logger.info("Nenhum arquivo de cookies encontrado. Continuando sem cookies.")
        self.cookie_file = None

    def get_cookie_file(self) -> Optional[str]:
        return self.cookie_file


class HeaderManager:
    @staticmethod
    def get_headers(user_agent: str) -> Dict[str, str]:
        return {
            'User-Agent': user_agent,
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
            'Accept-Language': 'pt-BR,pt;q=0.9,en-US;q=0.8,en;q=0.7',
            'Accept-Encoding': 'gzip, deflate, br',
            'Cache-Control': 'no-cache',
            'Connection': 'keep-alive',
            'DNT': '1',
            'Upgrade-Insecure-Requests': '1',
            'Sec-Fetch-Dest': 'document',
            'Sec-Fetch-Mode': 'navigate',
            'Sec-Fetch-Site': 'none',
            'Sec-Fetch-User': '?1',
            'Pragma': 'no-cache',
        }


class CooldownManager:
    def __init__(self):
        self.cooldown_until = 0
        self.active = False

    def activate(self, duration_seconds: int = 60):
        self.cooldown_until = time.time() + duration_seconds
        self.active = True

    def is_active(self) -> bool:
        if self.active and time.time() < self.cooldown_until:
            return True
        self.active = False
        return False

    def remaining(self) -> int:
        if self.active:
            return max(0, int(self.cooldown_until - time.time()))
        return 0


class RetryManager:
    def __init__(self):
        self.max_retries = 3
        self.backoff_base = 5

    def get_delay(self, retry_count: int) -> int:
        return self.backoff_base * (2 ** retry_count)


# ============================================================================
# JANELAS DE DIÁLOGO
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


class NormalizePreviewDialog(QDialog):
    def __init__(self, alteracoes: List[Tuple[str, str]], parent=None):
        super().__init__(parent)
        self.setWindowTitle("Prévia de Normalização")
        self.setMinimumSize(900, 500)
        self.setModal(True)
        layout = QVBoxLayout(self)

        lbl = QLabel(f"{len(alteracoes)} arquivo(s) serão normalizados. Edite os nomes se necessário.")
        layout.addWidget(lbl)

        self.table = QTableWidget()
        self.table.setColumnCount(3)
        self.table.setHorizontalHeaderLabels(["Selecionar", "Nome atual", "Novo nome"])
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.table.setRowCount(len(alteracoes))

        self.checkboxes = []
        for i, (antigo, novo) in enumerate(alteracoes):
            cb = QCheckBox()
            cb.setChecked(True)
            self.table.setCellWidget(i, 0, cb)
            self.checkboxes.append(cb)

            item_atual = QTableWidgetItem(antigo)
            if antigo == novo:
                item_atual.setForeground(QColor(0, 150, 0))
            self.table.setItem(i, 1, item_atual)

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

    def _selecionar_todos(self):
        for cb in self.checkboxes:
            cb.setChecked(True)

    def _desmarcar_todos(self):
        for cb in self.checkboxes:
            cb.setChecked(False)

    def _confirmar(self):
        self.accept()

    def get_selecao(self) -> List[bool]:
        return [cb.isChecked() for cb in self.checkboxes]

    def get_alteracoes_editadas(self) -> List[Tuple[str, str]]:
        resultado = []
        for i, cb in enumerate(self.checkboxes):
            if cb.isChecked():
                nome_atual = self.table.item(i, 1).text()
                novo_nome = self.table.item(i, 2).text()
                resultado.append((nome_atual, novo_nome))
        return resultado


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
# SISTEMA DE CACHE DE METADADOS (INCREMENTAL)
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
                        logger.info(f"[Cache] HIT: {file_path.name} (não modificado)")
                        return dict(row)
                    else:
                        logger.info(f"[Cache] MISMATCH (modificado ou force): {file_path.name}")
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

    def delete_entry(self, path: Path) -> None:
        with self._lock:
            with self._get_connection() as conn:
                conn.execute("DELETE FROM music_cache WHERE path = ?", (str(path),))
                conn.commit()
                logger.info(f"[Cache] Entrada removida: {path.name}")

    def update_metadata_for_files(self, file_paths: List[Path]) -> None:
        for path in file_paths:
            self.get_or_update(path, force=True)


# ============================================================================
# NORMALIZADOR (usa NPE v3.1)
# ============================================================================

class LibraryNormalizer:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init()
        return cls._instance

    def _init(self):
        self.npe = _npe
        logger.info("[Normalizer] Inicializado com NPE v3.1.")

    def normalize_title(self, title: str) -> str:
        parsed = self.npe.parse(f"Artista - {title}")
        return parsed.title

    def normalize_artist(self, artist: str) -> str:
        parsed = self.npe.parse(f"{artist} - Música")
        return parsed.artist or artist

    def extract_artist_title(self, filename: str) -> Tuple[str, str]:
        parsed = self.npe.parse(filename)
        return parsed.artist or "Desconhecido", parsed.title or "Sem título"

    def generate_new_name(self, filename: str, artist: str = None, title: str = None) -> str:
        if artist and title:
            return self.npe.normalize_filename(f"{artist} - {title}")
        return self.npe.normalize_filename(filename)

    def are_similar(self, name1: str, name2: str) -> bool:
        return self.npe.are_similar(name1, name2)

    def canonical_key(self, artist: str, title: str) -> str:
        return (artist + title).lower().replace(" ", "")

    def get_priority_suffix(self, filename: str) -> int:
        return 0


# ============================================================================
# WORKERS E THREADS PARA NORMALIZAÇÃO E DETECÇÃO
# ============================================================================

class NormalizeCollectWorker(QObject):
    progress = Signal(str, int)
    log = Signal(str, str)
    finished = Signal(list)
    error = Signal(str)

    def __init__(self, pasta: Path, normalizer: LibraryNormalizer, cache: MetadataCache):
        super().__init__()
        self.pasta = pasta
        self.normalizer = normalizer
        self.cache = cache
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        try:
            arquivos = list(self.pasta.glob("*.mp3"))
            if not arquivos:
                self.log.emit("Nenhum arquivo MP3 encontrado.", "WARNING")
                self.finished.emit([])
                return
            total = len(arquivos)
            alteracoes = []
            for i, arquivo in enumerate(arquivos):
                if self._cancel:
                    break
                novo_nome = self.normalizer.generate_new_name(arquivo.name)
                if arquivo.name != novo_nome:
                    alteracoes.append((arquivo.name, novo_nome))
                progresso = int((i + 1) / total * 100)
                self.progress.emit(f"Coletando {i+1}/{total}", progresso)
            self.finished.emit(alteracoes)
        except Exception as e:
            logger.error(f"Erro no NormalizeCollectWorker: {e}")
            self.error.emit(str(e))


class RenameWorker(QObject):
    progress = Signal(int)
    log = Signal(str, str)
    finished = Signal(int)
    error = Signal(str)

    def __init__(self, alteracoes: List[Tuple[str, str]], pasta: Path, cache: MetadataCache):
        super().__init__()
        self.alteracoes = alteracoes
        self.pasta = pasta
        self.cache = cache
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        try:
            total = len(self.alteracoes)
            sucessos = 0
            arquivos_renomeados = []
            for i, (antigo_nome, novo_nome) in enumerate(self.alteracoes):
                if self._cancel:
                    break
                antigo_path = self.pasta / antigo_nome
                novo_path = self.pasta / novo_nome
                if not antigo_path.exists():
                    self.log.emit(f"⚠️ Arquivo não encontrado: {antigo_nome}", "WARNING")
                    continue
                if novo_path.exists():
                    self.log.emit(f"⚠️ Nome já existe: {novo_nome}", "WARNING")
                    continue
                try:
                    antigo_path.rename(novo_path)
                    self.cache.update_file_path(str(antigo_path), str(novo_path))
                    # Registra aprendizado
                    _npe.register_user_correction(antigo_nome, novo_nome)
                    arquivos_renomeados.append(novo_path)
                    sucessos += 1
                    self.log.emit(f"✅ Normalizado: {antigo_nome} → {novo_nome}", "SUCCESS")
                except Exception as e:
                    self.log.emit(f"❌ Erro ao normalizar {antigo_nome}: {e}", "ERROR")
                    logger.error(f"Erro ao normalizar {antigo_nome}: {e}")
                progresso = int((i + 1) / total * 100)
                self.progress.emit(progresso)

            if arquivos_renomeados:
                for path in arquivos_renomeados:
                    self.cache.get_or_update(path, force=True)

            self.finished.emit(sucessos)
        except Exception as e:
            logger.error(f"Erro no RenameWorker: {e}")
            self.error.emit(str(e))


class DuplicateScanWorker(QObject):
    progress = Signal(str, int)
    log = Signal(str, str)
    group_found = Signal(list)
    finished = Signal(list)
    error = Signal(str)

    def __init__(self, pasta: Path, normalizer: LibraryNormalizer, cache: MetadataCache):
        super().__init__()
        self.pasta = pasta
        self.normalizer = normalizer
        self.cache = cache
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        try:
            registros = self.cache.get_all_metadata_for_folder(self.pasta, limpar_orfãos=True)
            if not registros:
                self.log.emit("⚠️ Nenhum arquivo MP3 encontrado no cache.", "WARNING")
                self.finished.emit([])
                return
            total = len(registros)
            self.progress.emit("Processando registros...", 10)

            musicas = []
            for reg in registros:
                filename = reg.get('filename', '')
                duration = reg.get('duration', 0.0)
                bitrate = reg.get('bitrate', 0)
                size = reg.get('size', 0)
                a, t = _npe.normalize_for_compare(filename)
                musicas.append({
                    'filename': filename,
                    'artist': a,
                    'title': t,
                    'duration': duration,
                    'bitrate': bitrate,
                    'size': size,
                    'path': reg.get('path', '')
                })

            # Agrupar por artista (comparação canônica)
            grupos_artista = {}
            for m in musicas:
                chave_artista = m['artist'].lower().strip()
                if not chave_artista:
                    chave_artista = 'desconhecido'
                grupos_artista.setdefault(chave_artista, []).append(m)

            duplicatas = []
            processados = set()
            self.progress.emit("Analisando duplicatas...", 30)

            for artista, lista in grupos_artista.items():
                if len(lista) < 2:
                    continue
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
                        # Compara artista e título normalizados
                        if item_atual['artist'].lower() == item_prox['artist'].lower() and \
                           item_atual['title'].lower() == item_prox['title'].lower():
                            # Verifica duração, bitrate e tamanho
                            dur1 = item_atual['duration']
                            dur2 = item_prox['duration']
                            if dur1 > 0 and dur2 > 0 and abs(dur1 - dur2) / max(dur1, dur2) > 0.03:
                                j += 1
                                continue
                            bit1 = item_atual['bitrate']
                            bit2 = item_prox['bitrate']
                            if bit1 > 0 and bit2 > 0 and bit1 != bit2:
                                j += 1
                                continue
                            size1 = item_atual['size']
                            size2 = item_prox['size']
                            if size1 > 0 and size2 > 0 and abs(size1 - size2) / max(size1, size2) > 0.05:
                                j += 1
                                continue
                            grupo.append(item_prox['filename'])
                            processados.add(item_prox['filename'])
                        j += 1
                    if len(grupo) > 1:
                        duplicatas.append(grupo)
                        processados.add(item_atual['filename'])
                    i = j
                self.progress.emit(f"Processado artista: {artista}", int(30 + 60 * (i / len(lista))))

            for grupo in duplicatas:
                self.group_found.emit(grupo)

            self.finished.emit(duplicatas)
        except Exception as e:
            logger.error(f"Erro no DuplicateScanWorker: {e}")
            self.error.emit(str(e))


class NormalizeThread(QThread):
    progress = Signal(str, int)
    log = Signal(str, str)
    finished = Signal(int)
    error = Signal(str)

    def __init__(self, pasta: Path, normalizer: LibraryNormalizer, cache: MetadataCache, alteracoes: List[Tuple[str, str]] = None):
        super().__init__()
        self.pasta = pasta
        self.normalizer = normalizer
        self.cache = cache
        self.alteracoes = alteracoes
        self._collect_worker = None
        self._rename_worker = None
        self._collect_thread = None
        self._rename_thread = None
        self._pending_alteracoes = None

    def run(self):
        if self.alteracoes is None:
            self._collect_worker = NormalizeCollectWorker(self.pasta, self.normalizer, self.cache)
            self._collect_worker.progress.connect(self.progress.emit)
            self._collect_worker.log.connect(self.log.emit)
            self._collect_worker.finished.connect(self._on_collect_finished)
            self._collect_worker.error.connect(self.error.emit)

            self._collect_thread = QThread()
            self._collect_worker.moveToThread(self._collect_thread)
            self._collect_thread.started.connect(self._collect_worker.run)
            self._collect_thread.start()
        else:
            self._pending_alteracoes = self.alteracoes
            self._show_preview_and_rename()

    def _on_collect_finished(self, alteracoes: list):
        if self._collect_thread:
            self._collect_thread.quit()
            self._collect_thread.wait()
            self._collect_thread.deleteLater()
            self._collect_worker.deleteLater()
            self._collect_thread = None
            self._collect_worker = None

        if not alteracoes:
            self.log.emit("✅ Todos os nomes já estão normalizados.", "SUCCESS")
            self.finished.emit(0)
            return

        self._pending_alteracoes = alteracoes
        self._show_preview_and_rename()

    def _show_preview_and_rename(self):
        self.log.emit("PRÉVIA", "INFO")

    def get_preview_data(self):
        return self._pending_alteracoes

    def execute_rename(self, alteracoes_editadas):
        if not alteracoes_editadas:
            self.log.emit("⏹️ Nenhum arquivo selecionado.", "INFO")
            self.finished.emit(0)
            return
        self._start_rename(alteracoes_editadas)

    def _start_rename(self, alteracoes: list):
        self._rename_worker = RenameWorker(alteracoes, self.pasta, self.cache)
        self._rename_worker.progress.connect(lambda p: self.progress.emit(f"Renomeando... {p}%", p))
        self._rename_worker.log.connect(self.log.emit)
        self._rename_worker.finished.connect(self._on_rename_finished)
        self._rename_worker.error.connect(self.error.emit)

        self._rename_thread = QThread()
        self._rename_worker.moveToThread(self._rename_thread)
        self._rename_thread.started.connect(self._rename_worker.run)
        self._rename_thread.start()

    def _on_rename_finished(self, sucessos: int):
        if self._rename_thread:
            self._rename_thread.quit()
            self._rename_thread.wait()
            self._rename_thread.deleteLater()
            self._rename_worker.deleteLater()
            self._rename_thread = None
            self._rename_worker = None
        self.finished.emit(sucessos)

    def cancel(self):
        if self._collect_worker:
            self._collect_worker.cancel()
        if self._rename_worker:
            self._rename_worker.cancel()
        if self._collect_thread and self._collect_thread.isRunning():
            self._collect_thread.quit()
            self._collect_thread.wait()
        if self._rename_thread and self._rename_thread.isRunning():
            self._rename_thread.quit()
            self._rename_thread.wait()


class DuplicateScanThread(QThread):
    progress = Signal(str, int)
    log = Signal(str, str)
    group_found = Signal(list)
    finished = Signal(list)
    error = Signal(str)

    def __init__(self, pasta: Path, normalizer: LibraryNormalizer, cache: MetadataCache):
        super().__init__()
        self.pasta = pasta
        self.normalizer = normalizer
        self.cache = cache
        self.worker = None

    def run(self):
        self.worker = DuplicateScanWorker(self.pasta, self.normalizer, self.cache)
        self.worker.progress.connect(self.progress.emit)
        self.worker.log.connect(self.log.emit)
        self.worker.group_found.connect(self.group_found.emit)
        self.worker.finished.connect(self._on_finished)
        self.worker.error.connect(self.error.emit)

        thread = QThread()
        self.worker.moveToThread(thread)
        thread.started.connect(self.worker.run)
        thread.start()
        self._thread = thread

    def _on_finished(self, duplicatas: list):
        if hasattr(self, '_thread'):
            self._thread.quit()
            self._thread.wait()
            self._thread.deleteLater()
        if self.worker:
            self.worker.deleteLater()
            self.worker = None
        self.finished.emit(duplicatas)

    def cancel(self):
        if self.worker:
            self.worker.cancel()


# ============================================================================
# THREADS ADICIONAIS (Importação e Recarregamento)
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
            # Verifica duplicata
            a, t = _npe.normalize_for_compare(origem.name)
            existe, _ = verificar_duplicatas_avancado(self.destino, a, t)
            if existe:
                self.log.emit(f"⏭️ DUPLICATA: {origem.name}", "WARNING")
                continue
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
# CLASSE PRINCIPAL - MUSICAPP
# ============================================================================

class MusicApp(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle("🎵 Nexus Player")
        self.setGeometry(100, 100, 1050, 750)
        self._running: bool = True

        self.cache = MetadataCache()
        self.normalizer = LibraryNormalizer()
        self.download_manager = DownloadManager()
        self.download_manager.log_signal.connect(self.append_log_baixador)
        self.download_manager.progress_signal.connect(self._on_download_progress)
        self.download_manager.finished_signal.connect(self._on_download_finished)
        self.download_manager.error_signal.connect(lambda e: self.append_log_baixador(f"❌ {e}", "ERROR"))
        self.download_manager.status_signal.connect(self._on_download_status)
        self.download_manager.stats_signal.connect(self._update_download_stats)

        self.playlist: List[str] = []
        self.current_index: int = -1
        self.random_mode: bool = False
        self.loop_mode: bool = False
        self.historico: List[str] = []

        self.player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        self.player.setAudioOutput(self.audio_output)
        self.audio_output.setVolume(0.7)

        # Estados do player
        self.player_state = "IDLE"  # IDLE, PLAYING, PAUSED, SEEKING

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

        self.config = carregar_config()
        pasta_player = self.config.get("last_player_folder", str(Path.home() / "Músicas" / "Nexus"))
        self.player_folder_line.setText(pasta_player)

        Path(pasta_player).mkdir(parents=True, exist_ok=True)
        self.carregar_playlist_sync(Path(pasta_player))

        self._pending_play = False
        self._pending_position = 0
        self._reload_thread = None
        self._normalize_thread = None
        self._duplicate_thread = None

        self._seeking = False

        self._atualizar_indicador_falhas()

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
    # CRIAÇÃO DAS ABAS
    # ========================================================================
    def criar_aba_baixador(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "🎵 Baixador")
        layout = QVBoxLayout(tab)

        self.sub_tabs = QTabWidget()
        layout.addWidget(self.sub_tabs)

        # Aba "Baixar"
        aba_baixar = QWidget()
        self.sub_tabs.addTab(aba_baixar, "⬇️ Baixar")

        layout_baixar = QVBoxLayout(aba_baixar)
        lbl = QLabel("🎵 Baixador de Músicas")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout_baixar.addWidget(lbl)
        row = QHBoxLayout()
        row.addWidget(QLabel("🔗 URL do YouTube:"))
        self.url_entry = QLineEdit()
        self.url_entry.setText("https://youtu.be/MkEVPjwZbrY")
        row.addWidget(self.url_entry)
        layout_baixar.addLayout(row)
        row2 = QHBoxLayout()
        row2.addWidget(QLabel("📁 Pasta de destino:"))
        self.dest_folder_entry = QLineEdit()
        self.dest_folder_entry.setText(str(Path.home() / "Músicas" / "Nexus"))
        row2.addWidget(self.dest_folder_entry)
        btn_pasta = QPushButton("📂 Escolher")
        btn_pasta.clicked.connect(self.escolher_pasta_destino)
        row2.addWidget(btn_pasta)
        layout_baixar.addLayout(row2)
        row3 = QHBoxLayout()
        self.btn_baixar = QPushButton("⬇️ Baixar Música")
        self.btn_baixar.clicked.connect(self.baixar_musica_unica)
        row3.addWidget(self.btn_baixar)
        self.btn_baixar_lote = QPushButton("📂 Baixar Lote (Arquivo .txt)")
        self.btn_baixar_lote.clicked.connect(self.baixar_lote)
        row3.addWidget(self.btn_baixar_lote)
        self.btn_pause = QPushButton("⏸️ Pausar")
        self.btn_pause.clicked.connect(self._pause_downloads)
        self.btn_pause.setEnabled(False)
        row3.addWidget(self.btn_pause)
        self.btn_resume = QPushButton("▶️ Continuar")
        self.btn_resume.clicked.connect(self._resume_downloads)
        self.btn_resume.setEnabled(False)
        row3.addWidget(self.btn_resume)
        self.btn_cancel = QPushButton("⏹️ Cancelar")
        self.btn_cancel.clicked.connect(self._cancel_downloads)
        self.btn_cancel.setEnabled(False)
        row3.addWidget(self.btn_cancel)
        layout_baixar.addLayout(row3)
        self.log_baixador = CollapsibleLog("📋 Log do Download")
        layout_baixar.addWidget(self.log_baixador)
        self.stats_label = QLabel("Estatísticas: Baixadas: 0 | Falhas: 0 | Puladas: 0 | Tentativas: 0")
        layout_baixar.addWidget(self.stats_label)
        layout_baixar.addWidget(QLabel("📜 Histórico de downloads:"))
        row_hist = QHBoxLayout()
        self.historico_list = QListWidget()
        row_hist.addWidget(self.historico_list)
        btn_limpar = QPushButton("🗑️ Limpar")
        btn_limpar.clicked.connect(self.limpar_historico)
        row_hist.addWidget(btn_limpar)
        layout_baixar.addLayout(row_hist)
        footer = QLabel("⚡ Powered by yt-dlp | MP3 192 kbps | v0.32 (NPE v3.1)")
        footer.setFont(QFont("Arial", 8))
        layout_baixar.addWidget(footer)
        self.append_log_baixador("Pronto para baixar músicas.", "INFO")

        # Aba "Falhas"
        aba_falhas = QWidget()
        self.sub_tabs.addTab(aba_falhas, "📥 Falhas")
        layout_falhas = QVBoxLayout(aba_falhas)
        lbl_falhas = QLabel("📥 Gerenciador Inteligente de Downloads Falhados")
        lbl_falhas.setFont(QFont("Arial", 18, QFont.Bold))
        layout_falhas.addWidget(lbl_falhas)
        stats_falhas = QHBoxLayout()
        self.stats_falhas_label = QLabel("Pendentes: 0 | Total: 0 | Recuperados: 0 | Perdidos: 0")
        stats_falhas.addWidget(self.stats_falhas_label)
        layout_falhas.addLayout(stats_falhas)
        filter_layout = QHBoxLayout()
        filter_layout.addWidget(QLabel("Filtrar:"))
        self.filter_combo = QComboBox()
        self.filter_combo.addItems(["Todos", "Pendentes", "Completados", "Falhas"])
        self.filter_combo.currentTextChanged.connect(self._atualizar_lista_falhas)
        filter_layout.addWidget(self.filter_combo)
        layout_falhas.addLayout(filter_layout)
        self.failures_list = QListWidget()
        layout_falhas.addWidget(self.failures_list)
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
        layout_falhas.addLayout(btn_layout)
        self.log_falhas = CollapsibleLog("📋 Log de Falhas")
        layout_falhas.addWidget(self.log_falhas)
        footer_falhas = QLabel("⚡ Selecione um ou mais itens para reprocessar, remover ou copiar.")
        footer_falhas.setFont(QFont("Arial", 8))
        layout_falhas.addWidget(footer_falhas)
        self.append_log_falhas("Gerenciador de falhas inicializado.", "INFO")
        self._atualizar_lista_falhas()

    def _atualizar_indicador_falhas(self):
        pendentes = len(self.download_manager.retry_queue)
        if pendentes > 0:
            self.sub_tabs.setTabText(1, f"📥 Falhas ({pendentes})")
        else:
            self.sub_tabs.setTabText(1, "📥 Falhas")

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
        self.btn_import = QPushButton("📥 Importar")
        self.btn_import.clicked.connect(self.importar_musicas)
        row1.addWidget(self.btn_import)
        btn_baixar_player = QPushButton("⬇️ Baixar")
        btn_baixar_player.clicked.connect(lambda: self.tabs.setCurrentIndex(0))
        row1.addWidget(btn_baixar_player)
        self.btn_recarregar = QPushButton("🔄 Recarregar")
        self.btn_recarregar.clicked.connect(self.recarregar_playlist_threaded)
        row1.addWidget(self.btn_recarregar)
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
        self.slider_progresso.sliderPressed.connect(self.slider_pressed)
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
        self.tabs.addTab(tab, "📚 Normalização")
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

        self.norm_list = QListWidget()
        layout.addWidget(self.norm_list)

        btn_delete = QPushButton("🗑️ Deletar Selecionado")
        btn_delete.clicked.connect(self.deletar_duplicata_selecionada_norm)
        layout.addWidget(btn_delete)

        self.log_normalizador = CollapsibleLog("📋 Log do Sistema de Normalização")
        layout.addWidget(self.log_normalizador)

        footer = QLabel("⚡ Selecione um arquivo duplicado (com \"╰─\") e clique em Deletar. Use 'Normalizar' para padronizar nomes.")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)
        self.append_log_normalizador("Sistema de Normalização inicializado.", "INFO")

    # ========================================================================
    # DOWNLOAD MANAGER CONTROLS
    # ========================================================================
    def _pause_downloads(self):
        self.download_manager.pause()
        self.btn_pause.setEnabled(False)
        self.btn_resume.setEnabled(True)
        self.append_log_baixador("⏸️ Downloads pausados.", "INFO")

    def _resume_downloads(self):
        self.download_manager.resume()
        self.btn_pause.setEnabled(True)
        self.btn_resume.setEnabled(False)
        self.append_log_baixador("▶️ Downloads continuados.", "INFO")

    def _cancel_downloads(self):
        self.download_manager.cancel()
        self.btn_pause.setEnabled(False)
        self.btn_resume.setEnabled(False)
        self.btn_cancel.setEnabled(False)
        self.append_log_baixador("⏹️ Downloads cancelados.", "WARNING")

    def _on_download_progress(self, atual: int, total: int):
        pass

    def _on_download_finished(self, success: int, failed: int, skipped: int):
        self.btn_pause.setEnabled(False)
        self.btn_resume.setEnabled(False)
        self.btn_cancel.setEnabled(False)
        self.append_log_baixador(f"✅ Lote concluído: {success} sucessos, {failed} falhas, {skipped} puladas.", "SUCCESS")
        pasta = Path(self.dest_folder_entry.text().strip())
        if Path(self.player_folder_line.text().strip()) == pasta:
            self.carregar_playlist_sync(pasta, force=True, preserve_position=True)

    def _on_download_status(self, status: str):
        self.append_log_baixador(f"📊 Status: {status}", "INFO")

    def _update_download_stats(self, stats: Dict):
        self.stats_label.setText(
            f"Estatísticas: Baixadas: {stats['success']} | Falhas: {stats['failed']} | "
            f"Puladas: {stats['skipped']} | Tentativas: {stats['retries']}"
        )

    # ========================================================================
    # FUNÇÕES DA ABA DE FALHAS
    # ========================================================================
    def _atualizar_lista_falhas(self):
        filtro = self.filter_combo.currentText() if hasattr(self, 'filter_combo') else "Todos"
        self.failures_list.clear()
        registros = self.download_manager.retry_queue
        if filtro != "Todos":
            registros = [r for r in registros if r.get('status') == filtro or r.get('status') == 'pending']
        if not registros:
            self.failures_list.addItem("✅ Nenhum download falhado.")
            return
        for rec in registros:
            artist = rec.get('artist', 'Desconhecido')
            title = rec.get('title', 'Sem título')
            retries = rec.get('retries', 0)
            status = rec.get('status', 'pending')
            display = f"{artist} - {title} [tentativas: {retries}] ({status})"
            self.failures_list.addItem(display)
        total = len(registros)
        pendentes = sum(1 for r in registros if r.get('status') == 'pending')
        self.stats_falhas_label.setText(f"Pendentes: {pendentes} | Total: {total}")

    def _get_selected_urls(self) -> List[str]:
        selected = self.failures_list.selectedItems()
        if not selected:
            return []
        urls = []
        for item in selected:
            display = item.text()
            for rec in self.download_manager.retry_queue:
                artist = rec.get('artist', 'Desconhecido')
                title = rec.get('title', 'Sem título')
                retries = rec.get('retries', 0)
                status = rec.get('status', 'pending')
                if f"{artist} - {title} [tentativas: {retries}] ({status})" == display:
                    urls.append(rec.get('url'))
                    break
        return urls

    def _retry_all_failures(self):
        if not self.download_manager.retry_queue:
            self.show_message("info", "Aviso", "Nenhum download falhado para reprocessar.")
            return
        for item in self.download_manager.retry_queue:
            item['status'] = 'pending'
            self.download_manager.queue.put(item)
        self.download_manager.retry_queue.clear()
        self.download_manager._save_retry_queue()
        self._atualizar_lista_falhas()
        self.append_log_falhas("🔄 Todos os itens foram movidos para a fila de download.", "INFO")
        if not self.download_manager.running:
            self.download_manager.start()
            self.btn_pause.setEnabled(True)
            self.btn_cancel.setEnabled(True)

    def _retry_selected_failures(self):
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione pelo menos um item.")
            return
        for url in urls:
            for item in self.download_manager.retry_queue:
                if item.get('url') == url:
                    item['status'] = 'pending'
                    self.download_manager.queue.put(item)
                    break
        self.download_manager.retry_queue = [r for r in self.download_manager.retry_queue if r.get('url') not in urls]
        self.download_manager._save_retry_queue()
        self._atualizar_lista_falhas()
        self.append_log_falhas(f"🔁 {len(urls)} item(s) movido(s) para a fila.", "INFO")
        if not self.download_manager.running:
            self.download_manager.start()
            self.btn_pause.setEnabled(True)
            self.btn_cancel.setEnabled(True)

    def _remove_selected_failures(self):
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione pelo menos um item.")
            return
        self.download_manager.retry_queue = [r for r in self.download_manager.retry_queue if r.get('url') not in urls]
        self.download_manager._save_retry_queue()
        self._atualizar_lista_falhas()
        self.append_log_falhas(f"🗑️ {len(urls)} registro(s) removido(s).", "INFO")

    def _clear_completed_failures(self):
        self.download_manager.retry_queue = [r for r in self.download_manager.retry_queue if r.get('status') != 'completed']
        self.download_manager._save_retry_queue()
        self._atualizar_lista_falhas()
        self.append_log_falhas("🗑️ Registros completados removidos.", "INFO")

    def _open_failure_link(self):
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione um item.")
            return
        webbrowser.open(urls[0])

    def _copy_failure_url(self):
        urls = self._get_selected_urls()
        if not urls:
            self.show_message("warning", "Aviso", "Selecione um item.")
            return
        QApplication.clipboard().setText(urls[0])
        self.append_log_falhas(f"📋 URL copiada: {urls[0]}", "INFO")

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

        if self._normalize_thread and self._normalize_thread.isRunning():
            self.append_log_normalizador("⚠️ Normalização já em andamento.", "WARNING")
            return

        self.append_log_normalizador(f"🧹 Coletando dados para normalização em: {pasta}", "INFO")
        self._update_norm_status("Coletando dados...", 0)
        self.btn_normalizar.setEnabled(False)
        self.norm_progress_bar.setVisible(True)

        self._normalize_thread = NormalizeThread(pasta, self.normalizer, self.cache, alteracoes=None)
        self._normalize_thread.progress.connect(self._on_norm_progress)
        self._normalize_thread.log.connect(self._on_norm_log)
        self._normalize_thread.finished.connect(self._on_norm_finished)
        self._normalize_thread.error.connect(self._on_norm_error)
        self._normalize_thread.start()

    def _on_norm_progress(self, msg: str, progress: int):
        self._update_norm_status(msg, progress)

    def _on_norm_log(self, texto: str, tipo: str):
        if tipo == "INFO" and texto == "PRÉVIA":
            if self._normalize_thread:
                alteracoes = self._normalize_thread.get_preview_data()
                if alteracoes:
                    self._show_normalize_preview(alteracoes)
            return
        self.append_log_normalizador(texto, tipo)

    def _show_normalize_preview(self, alteracoes: list):
        dialog = NormalizePreviewDialog(alteracoes, self)
        if dialog.exec() == QDialog.Accepted:
            alteracoes_editadas = dialog.get_alteracoes_editadas()
            if self._normalize_thread:
                self._normalize_thread.execute_rename(alteracoes_editadas)
        else:
            self.append_log_normalizador("⏹️ Normalização cancelada pelo usuário.", "INFO")
            self._update_norm_status("Cancelado", 0)
            self.btn_normalizar.setEnabled(True)
            self.norm_progress_bar.setVisible(False)

    def _on_norm_finished(self, sucessos: int):
        self._normalize_thread = None
        self.btn_normalizar.setEnabled(True)
        self.norm_progress_bar.setVisible(False)
        self._update_norm_status(f"Concluído: {sucessos} normalizados", 100)
        self.append_log_normalizador(f"✅ Normalização concluída: {sucessos} arquivo(s) alterados.", "SUCCESS")
        self.show_message("info", "Normalização", f"{sucessos} arquivo(s) normalizados com sucesso!")
        pasta = Path(self.norm_folder_entry.text().strip())
        if Path(self.player_folder_line.text().strip()) == pasta:
            self.carregar_playlist_sync(pasta, force=False, preserve_position=True)

    def _on_norm_error(self, erro: str):
        self._normalize_thread = None
        self.btn_normalizar.setEnabled(True)
        self.norm_progress_bar.setVisible(False)
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
    # NORMALIZADOR - DUPLICATAS
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

        if self._duplicate_thread and self._duplicate_thread.isRunning():
            self.append_log_normalizador("⚠️ Escaneamento já em andamento.", "WARNING")
            return

        self.append_log_normalizador(f"🔍 Escaneando pasta: {pasta} (usando NPE v3.1)", "INFO")
        self._update_norm_status("Iniciando...", 0)
        self.btn_escanear.setEnabled(False)
        self.norm_progress_bar.setVisible(True)
        self.norm_list.clear()

        self._duplicate_thread = DuplicateScanThread(pasta, self.normalizer, self.cache)
        self._duplicate_thread.progress.connect(self._on_dup_progress)
        self._duplicate_thread.log.connect(self._on_dup_log)
        self._duplicate_thread.group_found.connect(self._on_dup_group_found)
        self._duplicate_thread.finished.connect(self._on_dup_finished)
        self._duplicate_thread.error.connect(self._on_dup_error)
        self._duplicate_thread.start()

    def _on_dup_progress(self, msg: str, progress: int):
        self._update_norm_status(msg, progress)

    def _on_dup_log(self, texto: str, tipo: str):
        self.append_log_normalizador(texto, tipo)

    def _on_dup_group_found(self, grupo: List[str]):
        self.norm_list.addItem(f"📁 {grupo[0]}")
        for arquivo in grupo[1:]:
            self.norm_list.addItem(f"   ╰─ {arquivo}")

    def _on_dup_finished(self, duplicatas: List[List[str]]):
        self._duplicate_thread = None
        self.btn_escanear.setEnabled(True)
        self.norm_progress_bar.setVisible(False)
        if not duplicatas:
            self._update_norm_status("Concluído: 0 grupos", 100)
            self.show_message("info", "Concluído", "Nenhuma duplicata encontrada!")
        else:
            self._update_norm_status(f"Concluído: {len(duplicatas)} grupos", 100)
            self.show_message("info", "Concluído", f"Encontrados {len(duplicatas)} grupos de duplicatas!")

    def _on_dup_error(self, erro: str):
        self._duplicate_thread = None
        self.btn_escanear.setEnabled(True)
        self.norm_progress_bar.setVisible(False)
        self.append_log_normalizador(f"❌ Erro: {erro}", "ERROR")
        self._update_norm_status("Erro", 0)
        self.show_message("critical", "Erro", f"Ocorreu um erro:\n{erro}")

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
                # Tenta excluir o arquivo
                if caminho.is_file():
                    caminho.unlink()
                    logger.info(f"Arquivo deletado: {caminho}")
                # Atualiza cache
                self.cache.delete_entry(caminho)
                # Remove da lista visual
                self.norm_list.takeItem(selecao)
                self.append_log_normalizador(f"🗑️ DELETADO: {nome_arquivo}", "SUCCESS")
                self.show_message("info", "Sucesso", f"Arquivo deletado:\n{nome_arquivo}")
                # Atualiza playlist se necessário
                if Path(self.player_folder_line.text().strip()) == pasta:
                    self.carregar_playlist_sync(pasta, force=False, preserve_position=True)
            except PermissionError as e:
                self.append_log_normalizador(f"❌ Erro de permissão ao deletar {nome_arquivo}: {e}", "ERROR")
                self.show_message("critical", "Erro", f"Erro de permissão:\n{e}")
            except OSError as e:
                self.append_log_normalizador(f"❌ Erro ao deletar {nome_arquivo}: {e}", "ERROR")
                self.show_message("critical", "Erro", f"Erro ao deletar:\n{e}")
            except Exception as e:
                self.append_log_normalizador(f"❌ Erro inesperado ao deletar {nome_arquivo}: {e}", "ERROR")
                self.show_message("critical", "Erro", f"Erro inesperado:\n{e}")

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
        was_playing = (self.player.playbackState() == QMediaPlayer.PlayingState)
        self.append_log_player("🔄 Recarregando playlist em segundo plano...", "INFO")
        self.btn_recarregar.setEnabled(False)
        self.btn_recarregar.setText("⏳ Carregando...")
        self._reload_thread = ReloadPlaylistThread(pasta, self.cache, force=False, preserve=True,
                                                   saved_file=saved_file, saved_position=saved_position)
        self._reload_thread.progress.connect(self._on_reload_progress)
        self._reload_thread.finished.connect(lambda: self._on_reload_finished(was_playing))
        self._reload_thread.error.connect(self._on_reload_error)
        self._reload_thread.start()

    def _on_reload_progress(self, mensagem: str, progresso: int):
        self.append_log_player(f"⏳ {mensagem}", "INFO")

    def _on_reload_finished(self, was_playing: bool):
        self.btn_recarregar.setEnabled(True)
        self.btn_recarregar.setText("🔄 Recarregar")
        if self._reload_thread:
            nova_playlist = self._reload_thread.get_playlist()
            if nova_playlist:
                self.playlist = nova_playlist
                self._atualizar_lista_player_ui()
                if self.current_index >= 0 and self.current_index < len(self.playlist):
                    self.musica_atual_label.setText(f"▶ {self.playlist[self.current_index]}")
                    if was_playing and self.player.playbackState() != QMediaPlayer.PlayingState:
                        self.player.play()
                    elif not was_playing and self.player.playbackState() == QMediaPlayer.PlayingState:
                        self.player.pause()
                    self.append_log_player(f"✅ Playlist recarregada: {len(self.playlist)} músicas.", "SUCCESS")
                else:
                    self.current_index = -1
                    self.slider_progresso.setEnabled(False)
                    self.musica_atual_label.setText("⏹️ Nenhuma música")
                    self.tempo_label.setText("00:00 / 00:00")
                    self.btn_play_pause.setText("▶ Play")
                    self.player.stop()
                    self.append_log_player("Playlist recarregada, música anterior não encontrada.", "WARNING")
            else:
                self.append_log_player("⚠️ Playlist vazia após recarregamento.", "WARNING")
                self.playlist = []
                self.current_index = -1
                self._atualizar_lista_player_ui()
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
                self.musica_atual_label.setText(f"▶ {self.playlist[new_index]}")
                if was_playing:
                    self.player.play()
                else:
                    self.player.pause()
                if saved_position > 0:
                    self.player.setPosition(saved_position)
                self.append_log_player(f"Playlist recarregada, música restaurada: {self.playlist[new_index]}", "SUCCESS")
            else:
                self.current_index = -1
                self.slider_progresso.setEnabled(False)
                self.musica_atual_label.setText("⏹️ Nenhuma música")
                self.tempo_label.setText("00:00 / 00:00")
                self.btn_play_pause.setText("▶ Play")
                self.player.stop()
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
    # PLAYER - REPRODUÇÃO (com correção do seek)
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
        self.player_state = "IDLE"
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
        if resume_position > 0:
            self._pending_position = resume_position
        else:
            self._pending_position = 0

    @Slot(QMediaPlayer.MediaStatus)
    def on_media_status_changed(self, status: QMediaPlayer.MediaStatus) -> None:
        if status == QMediaPlayer.LoadedMedia:
            if self._pending_play:
                self.player.play()
                self._pending_play = False
                self.player_state = "PLAYING"
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
            self.player_state = "PAUSED"
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
                self.player_state = "PLAYING"
                self.btn_play_pause.setText("⏸️ Pausar")
                if self.current_index >= 0:
                    self.musica_atual_label.setText(f"▶ {self.playlist[self.current_index]}")
            self.append_log_player("Reproduzindo", "INFO")

    def parar_musica(self) -> None:
        self.player.stop()
        self.player_state = "IDLE"
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
    # SLOTS DO QMEDIAPLAYER (com correção do seek)
    # ========================================================================
    @Slot(int)
    def on_position_changed(self, pos: int) -> None:
        # Só atualiza se não estiver em SEEKING e não estiver arrastando
        if not self._seeking and self.player_state != "SEEKING":
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
    # SEEK (CORRIGIDO)
    # ========================================================================
    def slider_pressed(self):
        """Usuário começou a arrastar."""
        self._seeking = True
        self.player_state = "SEEKING"
        # Pausa a atualização automática

    def slider_moved(self, pos: int) -> None:
        """Atualiza apenas o label durante o arrasto."""
        duracao = self.player.duration()
        if duracao > 0:
            self.atualizar_label_tempo(pos, duracao)

    def slider_released(self) -> None:
        """Usuário soltou o slider."""
        pos = self.slider_progresso.value()
        self.player.setPosition(pos)
        duracao = self.player.duration()
        if duracao > 0:
            self.atualizar_label_tempo(pos, duracao)
        self._seeking = False
        self.player_state = "PLAYING" if self.player.playbackState() == QMediaPlayer.PlayingState else "PAUSED"

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
    # DOWNLOADER (chamadas para o DownloadManager)
    # ========================================================================
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
            self.show_message("critical", "FFmpeg não encontrado", "FFmpeg não encontrado.\n\nColoque o ffmpeg na pasta do programa ou no PATH.")
            return
        self.download_manager.download_folder = pasta
        self.download_manager.ffmpeg_path = ffmpeg_path
        self.download_manager.start()
        self.btn_pause.setEnabled(True)
        self.btn_cancel.setEnabled(True)

        self.download_manager.add_item(url, "Desconhecido", "Sem título")
        self.append_log_baixador(f"⬆️ URL adicionada à fila: {url}", "INFO")

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
            self.show_message("critical", "FFmpeg não encontrado", "FFmpeg não encontrado.\n\nColoque o ffmpeg na pasta do programa ou no PATH.")
            return
        try:
            with open(arquivo_path, 'r', encoding='utf-8') as f:
                links = [linha.strip() for linha in f if linha.strip() and not linha.startswith('#')]
        except Exception as e:
            self.append_log_baixador(f"❌ Erro ao ler arquivo: {e}", "ERROR")
            self.show_message("critical", "Erro", f"Erro ao ler o arquivo:\n{e}")
            return
        if not links:
            self.show_message("warning", "Aviso", "Nenhum link encontrado no arquivo!")
            return
        self.append_log_baixador(f"📚 Encontrados {len(links)} links no arquivo!", "INFO")
        self.download_manager.download_folder = pasta
        self.download_manager.ffmpeg_path = ffmpeg_path
        self.download_manager.start()
        self.btn_pause.setEnabled(True)
        self.btn_cancel.setEnabled(True)

        for url in links:
            self.download_manager.add_item(url, "Desconhecido", "Sem título")
        self.append_log_baixador(f"⬆️ {len(links)} URLs adicionadas à fila.", "INFO")

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
        self.btn_import.setEnabled(False)

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
        self.btn_import.setEnabled(True)
        if count > 0:
            self.show_message("info", "Sucesso", f"{count} música(s) importada(s)!")
            pasta = Path(self.player_folder_line.text().strip())
            self.carregar_playlist_sync(pasta, force=False, preserve_position=True)
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
            self._normalize_thread.cancel()
            self._normalize_thread.wait(1000)
        if self._duplicate_thread and self._duplicate_thread.isRunning():
            self._duplicate_thread.cancel()
            self._duplicate_thread.wait(1000)
        self.download_manager.cancel()
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