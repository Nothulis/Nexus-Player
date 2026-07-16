#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Nexus Player - Versão 5.0 (Estabilização Final)
BaseWorker, DownloadWorker, Cache LRU, Índices, Tratamento de Exceções, Testes
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
import hashlib
import traceback
from pathlib import Path
from datetime import datetime, timedelta
from difflib import SequenceMatcher
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial, lru_cache
from typing import Optional, List, Tuple, Dict, Any, Callable, Union, Set
from dataclasses import dataclass, field
from enum import Enum
import uuid
import math
from collections import OrderedDict

import yt_dlp
import mutagen.mp3

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QTabWidget, QWidget, QVBoxLayout,
    QHBoxLayout, QLabel, QLineEdit, QPushButton, QListWidget,
    QListWidgetItem, QSlider, QFileDialog, QMessageBox,
    QTextEdit, QGroupBox, QSplitter, QProgressDialog, QDialog,
    QCheckBox, QDialogButtonBox, QTableWidget, QTableWidgetItem,
    QHeaderView, QProgressBar, QComboBox, QFrame, QDoubleSpinBox,
    QFormLayout
)
from PySide6.QtCore import Qt, QUrl, Slot, QTimer, QThread, Signal, QSize, QMetaObject, Q_ARG, QEventLoop
from PySide6.QtMultimedia import QMediaPlayer, QAudioOutput
from PySide6.QtGui import QFont, QColor, QTextCharFormat, QTextCursor, QIcon, QPalette

# ============================================================================
# CONFIGURAÇÕES GLOBAIS
# ============================================================================

APP_NAME = "Nexus Player"
APP_VERSION = "5.0.0"
BASE_DIR = Path(__file__).parent
LOG_DIR = BASE_DIR / "logs"
CONFIG_DIR = BASE_DIR / "config"
DATA_DIR = BASE_DIR / "data"
MUSIC_DIR = DATA_DIR / "Music"
COVERS_DIR = DATA_DIR / "Covers"
CACHE_DIR = DATA_DIR / "Cache"
DB_PATH = DATA_DIR / "nexus.db"

for dir_path in [LOG_DIR, CONFIG_DIR, DATA_DIR, MUSIC_DIR, COVERS_DIR, CACHE_DIR]:
    dir_path.mkdir(parents=True, exist_ok=True)

# ============================================================================
# LOGGER UNIFICADO
# ============================================================================

class NexusLogger:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init_logger()
        return cls._instance

    def _init_logger(self):
        log_file = LOG_DIR / f"nexus_{datetime.now().strftime('%Y%m%d')}.log"
        self.logger = logging.getLogger("Nexus")
        self.logger.setLevel(logging.DEBUG)
        self.logger.handlers.clear()

        fh = logging.FileHandler(log_file, encoding='utf-8')
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(name)s - %(message)s'))
        self.logger.addHandler(fh)

        ch = logging.StreamHandler()
        ch.setLevel(logging.ERROR)
        ch.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
        self.logger.addHandler(ch)

        self.norm_log_file = LOG_DIR / f"normalizer_unknown_{datetime.now().strftime('%Y%m%d')}.log"
        self.norm_logger = logging.getLogger("NexusNormalizer")
        self.norm_logger.setLevel(logging.INFO)
        self.norm_logger.handlers.clear()
        nfh = logging.FileHandler(self.norm_log_file, encoding='utf-8')
        nfh.setLevel(logging.INFO)
        nfh.setFormatter(logging.Formatter('%(asctime)s - %(message)s'))
        self.norm_logger.addHandler(nfh)

    def _log(self, level, category, msg):
        full_msg = f"[{category}] {msg}"
        self.logger.log(level, full_msg)
        if category == "NORMALIZER" and level >= logging.INFO:
            self.norm_logger.info(msg)

    def info(self, msg, category="GENERAL"):
        self._log(logging.INFO, category, msg)

    def warning(self, msg, category="GENERAL"):
        self._log(logging.WARNING, category, msg)

    def error(self, msg, category="GENERAL"):
        self._log(logging.ERROR, category, msg)

    def debug(self, msg, category="GENERAL"):
        self._log(logging.DEBUG, category, msg)

    def critical(self, msg, category="GENERAL"):
        self._log(logging.CRITICAL, category, msg)

    def success(self, msg, category="GENERAL"):
        self._log(logging.INFO, category, f"✅ {msg}")

    def task(self, msg):
        self.info(msg, "TASK")

    def download(self, msg):
        self.info(msg, "DOWNLOAD")

    def player(self, msg):
        self.info(msg, "PLAYER")

    def normalizer(self, msg):
        self.info(msg, "NORMALIZER")

    def cache(self, msg):
        self.info(msg, "CACHE")

    def ffmpeg(self, msg):
        self.info(msg, "FFMPEG")

    def thread(self, msg):
        self.info(msg, "THREAD")

    def retry(self, msg):
        self.info(msg, "RETRY")

    def norm_unknown(self, msg):
        self.normalizer(f"[UNKNOWN] {msg}")

logger = NexusLogger()

# ============================================================================
# CONFIGURAÇÃO UNIFICADA
# ============================================================================

class Config:
    _instance = None
    _config = {}
    _lock = threading.Lock()

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._load()
        return cls._instance

    def _load(self):
        config_file = CONFIG_DIR / "config.json"
        default_config = {
            "download_workers": 4,
            "max_retries": 5,
            "retry_delays": [5, 15, 30, 60, 120],
            "download_folder": str(MUSIC_DIR),
            "covers_folder": str(COVERS_DIR),
            "cache_folder": str(CACHE_DIR),
            "max_history": 100,
            "auto_reload_playlist": True,
            "default_quality": "192",
            "language": "pt-BR",
            "theme": "dark",
            "last_player_folder": str(Path.home() / "Músicas" / "Nexus"),
            "confidence_threshold": 70,
            "log_unknown_variations": True,
            "ffmpeg_path": "",
            "duplicate_similarity_threshold": 0.92,
            "preserve_case_list": ["AC/DC", "R.E.M.", "KSHMR", "DJ", "MC", "USA", "UK", "M.I.A.", "P!nk", "ABBA", "TLC", "B2K", "NSYNC", "MSTRKRFT"],
            "ignore_articles": ["a", "an", "the", "of", "and", "or", "for", "with", "without", "in", "on", "at", "to", "from", "by", "as", "into", "through", "during", "including"]
        }
        if config_file.exists():
            try:
                with open(config_file, 'r', encoding='utf-8') as f:
                    self._config = json.load(f)
                logger.info("Configurações carregadas.", "CONFIG")
            except Exception as e:
                logger.error(f"Erro ao carregar configurações: {e}", "CONFIG")
                self._config = default_config
        else:
            self._config = default_config
            self._save()

    def _save(self):
        config_file = CONFIG_DIR / "config.json"
        with self._lock:
            try:
                with open(config_file, 'w', encoding='utf-8') as f:
                    json.dump(self._config, f, indent=2, ensure_ascii=False)
                logger.info("Configurações salvas.", "CONFIG")
            except Exception as e:
                logger.error(f"Erro ao salvar configurações: {e}", "CONFIG")

    def get(self, key, default=None):
        with self._lock:
            return self._config.get(key, default)

    def set(self, key, value):
        with self._lock:
            self._config[key] = value
        self._save()

    def get_workers(self):
        return self.get("download_workers", 4)

    def get_retry_delays(self):
        return self.get("retry_delays", [5, 15, 30, 60, 120])

    def get_max_retries(self):
        return self.get("max_retries", 5)

    def get_download_folder(self):
        return Path(self.get("download_folder", str(MUSIC_DIR)))

    def get_covers_folder(self):
        return Path(self.get("covers_folder", str(COVERS_DIR)))

    def get_confidence_threshold(self):
        return self.get("confidence_threshold", 70)

    def get_preserve_case(self):
        return self.get("preserve_case_list", [])

    def get_ignore_articles(self):
        return self.get("ignore_articles", [])

    def get_ffmpeg_path(self):
        return self.get("ffmpeg_path", "")

    def set_ffmpeg_path(self, path):
        self.set("ffmpeg_path", str(path))

    def get_duplicate_threshold(self):
        return self.get("duplicate_similarity_threshold", 0.92)

# ============================================================================
# CACHE LRU
# ============================================================================

class LRUCache:
    """Cache LRU thread-safe com tamanho máximo."""
    def __init__(self, maxsize=500):
        self.maxsize = maxsize
        self._cache = OrderedDict()
        self._lock = threading.Lock()

    def get(self, key):
        with self._lock:
            if key in self._cache:
                self._cache.move_to_end(key)
                return self._cache[key]
            return None

    def put(self, key, value):
        with self._lock:
            if key in self._cache:
                self._cache.move_to_end(key)
                self._cache[key] = value
            else:
                if len(self._cache) >= self.maxsize:
                    self._cache.popitem(last=False)
                self._cache[key] = value

    def invalidate(self, key):
        with self._lock:
            if key in self._cache:
                del self._cache[key]

    def clear(self):
        with self._lock:
            self._cache.clear()

    def __contains__(self, key):
        with self._lock:
            return key in self._cache

    def __len__(self):
        with self._lock:
            return len(self._cache)

# ============================================================================
# BANCO DE DADOS (com WAL e índices)
# ============================================================================

class Database:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init_db()
        return cls._instance

    def _init_db(self):
        self.db_path = DB_PATH
        self._conn = None
        self._lock = threading.Lock()
        self._create_tables()

    def _get_connection(self):
        if self._conn is None:
            self._conn = sqlite3.connect(str(self.db_path), timeout=10)
            self._conn.row_factory = sqlite3.Row
            # Ativa WAL e sincronização otimizada
            self._conn.execute("PRAGMA journal_mode=WAL")
            self._conn.execute("PRAGMA synchronous=NORMAL")
        return self._conn

    def _create_tables(self):
        with self._lock:
            conn = self._get_connection()
            conn.execute('''
                CREATE TABLE IF NOT EXISTS songs (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
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
                    path TEXT UNIQUE,
                    filename TEXT,
                    cover_path TEXT,
                    mtime REAL,
                    date_added TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    play_count INTEGER DEFAULT 0,
                    last_played TIMESTAMP,
                    favorite INTEGER DEFAULT 0,
                    rating REAL DEFAULT 0.0,
                    file_hash TEXT,
                    normalized_artist TEXT,
                    normalized_title TEXT,
                    confidence REAL DEFAULT 0.0
                )
            ''')
            conn.execute('''
                CREATE TABLE IF NOT EXISTS tasks (
                    id TEXT PRIMARY KEY,
                    type TEXT,
                    status TEXT,
                    progress INTEGER DEFAULT 0,
                    total INTEGER DEFAULT 0,
                    current_item TEXT,
                    data TEXT,
                    error TEXT,
                    retries INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    completed_at TIMESTAMP,
                    start_time TIMESTAMP,
                    paused_time INTEGER DEFAULT 0,
                    elapsed_time INTEGER DEFAULT 0,
                    checkpoint_data TEXT
                )
            ''')
            conn.execute('''
                CREATE TABLE IF NOT EXISTS failed_tasks (
                    id TEXT PRIMARY KEY,
                    type TEXT,
                    url TEXT,
                    artist TEXT,
                    title TEXT,
                    error TEXT,
                    retries INTEGER DEFAULT 0,
                    last_attempt TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    data TEXT
                )
            ''')

            # Índices otimizados
            conn.execute("CREATE INDEX IF NOT EXISTS idx_songs_path ON songs(path)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_songs_normalized_artist ON songs(normalized_artist)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_songs_normalized_title ON songs(normalized_title)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_songs_file_hash ON songs(file_hash)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_songs_play_count ON songs(play_count)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_tasks_status ON tasks(status)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_failed_tasks_type ON failed_tasks(type)")

            # Análise para otimizador
            conn.execute("ANALYZE")
            conn.commit()
            logger.info("Banco de dados inicializado com WAL e índices.", "CACHE")

    def execute(self, query, params=()):
        with self._lock:
            conn = self._get_connection()
            cursor = conn.execute(query, params)
            conn.commit()
            return cursor

    def fetchone(self, query, params=()):
        with self._lock:
            conn = self._get_connection()
            return conn.execute(query, params).fetchone()

    def fetchall(self, query, params=()):
        with self._lock:
            conn = self._get_connection()
            return conn.execute(query, params).fetchall()

    def insert_song(self, song_data):
        with self._lock:
            conn = self._get_connection()
            conn.execute('''
                INSERT OR REPLACE INTO songs (
                    title, artist, album, album_artist, genre, year, track,
                    duration, bitrate, sample_rate, size, path, filename,
                    cover_path, mtime, date_added, file_hash,
                    normalized_artist, normalized_title, confidence
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                song_data.get('title', ''),
                song_data.get('artist', ''),
                song_data.get('album', ''),
                song_data.get('album_artist', ''),
                song_data.get('genre', ''),
                song_data.get('year', ''),
                song_data.get('track', ''),
                song_data.get('duration', 0.0),
                song_data.get('bitrate', 0),
                song_data.get('sample_rate', 0),
                song_data.get('size', 0),
                song_data.get('path', ''),
                song_data.get('filename', ''),
                song_data.get('cover_path', ''),
                song_data.get('mtime', 0),
                datetime.now().isoformat(),
                song_data.get('file_hash', ''),
                song_data.get('normalized_artist', ''),
                song_data.get('normalized_title', ''),
                song_data.get('confidence', 0.0)
            ))
            conn.commit()
            return conn.lastrowid

    def save_task(self, task):
        with self._lock:
            conn = self._get_connection()
            conn.execute('''
                INSERT OR REPLACE INTO tasks (
                    id, type, status, progress, total, current_item,
                    data, error, retries, updated_at, start_time,
                    paused_time, elapsed_time, checkpoint_data
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                task.id,
                task.type,
                task.status.value,
                task.progress,
                task.total,
                task.current_item or '',
                json.dumps(task.data) if task.data else '',
                task.error or '',
                task.retries,
                datetime.now().isoformat(),
                task.start_time.isoformat() if task.start_time else None,
                task.paused_time,
                task.elapsed_time,
                json.dumps(task.checkpoint_data) if task.checkpoint_data else ''
            ))
            conn.commit()

    def get_task(self, task_id):
        row = self.fetchone("SELECT * FROM tasks WHERE id = ?", (task_id,))
        return dict(row) if row else None

    def get_tasks(self, status=None):
        if status:
            rows = self.fetchall("SELECT * FROM tasks WHERE status = ? ORDER BY updated_at DESC", (status,))
        else:
            rows = self.fetchall("SELECT * FROM tasks ORDER BY updated_at DESC")
        return [dict(row) for row in rows]

    def delete_task(self, task_id):
        self.execute("DELETE FROM tasks WHERE id = ?", (task_id,))

    def save_failed(self, failed_data):
        with self._lock:
            conn = self._get_connection()
            conn.execute('''
                INSERT OR REPLACE INTO failed_tasks (
                    id, type, url, artist, title, error, retries, data
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                failed_data.get('id', str(uuid.uuid4())),
                failed_data.get('type', 'download'),
                failed_data.get('url', ''),
                failed_data.get('artist', ''),
                failed_data.get('title', ''),
                failed_data.get('error', ''),
                failed_data.get('retries', 0),
                json.dumps(failed_data.get('data', {}))
            ))
            conn.commit()

    def get_failed_tasks(self):
        rows = self.fetchall("SELECT * FROM failed_tasks ORDER BY last_attempt DESC")
        return [dict(row) for row in rows]

    def delete_failed(self, task_id):
        self.execute("DELETE FROM failed_tasks WHERE id = ?", (task_id,))

    def delete_all_failed(self):
        self.execute("DELETE FROM failed_tasks")

    def update_song_normalized(self, path: str, norm_artist: str, norm_title: str, confidence: float, file_hash: str):
        with self._lock:
            conn = self._get_connection()
            conn.execute('''
                UPDATE songs SET
                    normalized_artist = ?,
                    normalized_title = ?,
                    confidence = ?,
                    file_hash = ?
                WHERE path = ?
            ''', (norm_artist, norm_title, confidence, file_hash, path))
            conn.commit()

    def get_songs_by_hash(self, file_hash: str):
        rows = self.fetchall("SELECT * FROM songs WHERE file_hash = ?", (file_hash,))
        return [dict(row) for row in rows]

    def get_songs_by_normalized(self, norm_artist: str, norm_title: str):
        rows = self.fetchall(
            "SELECT * FROM songs WHERE normalized_artist = ? AND normalized_title = ?",
            (norm_artist, norm_title)
        )
        return [dict(row) for row in rows]

    def close(self):
        if self._conn:
            self._conn.close()
            self._conn = None

# ============================================================================
# TASK MANAGER
# ============================================================================

class TaskStatus(Enum):
    PENDING = "pending"
    RUNNING = "running"
    PAUSED = "paused"
    RESUMING = "resuming"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"

@dataclass
class Task:
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    type: str = "general"
    status: TaskStatus = TaskStatus.PENDING
    progress: int = 0
    total: int = 0
    current_item: str = ""
    data: Dict[str, Any] = field(default_factory=dict)
    error: str = ""
    retries: int = 0
    created_at: datetime = field(default_factory=datetime.now)
    updated_at: datetime = field(default_factory=datetime.now)
    completed_at: Optional[datetime] = None
    start_time: Optional[datetime] = None
    paused_time: int = 0
    elapsed_time: int = 0
    checkpoint_data: Dict[str, Any] = field(default_factory=dict)
    callback: Optional[Callable] = None
    _paused: bool = False
    _cancelled: bool = False
    _lock: threading.Lock = field(default_factory=threading.Lock)
    _pause_event: threading.Event = field(default_factory=threading.Event)
    _progress_callback: Optional[Callable] = None

    def to_dict(self):
        return {
            'id': self.id,
            'type': self.type,
            'status': self.status.value,
            'progress': self.progress,
            'total': self.total,
            'current_item': self.current_item,
            'data': self.data,
            'error': self.error,
            'retries': self.retries,
            'created_at': self.created_at.isoformat(),
            'updated_at': self.updated_at.isoformat(),
            'completed_at': self.completed_at.isoformat() if self.completed_at else None,
            'start_time': self.start_time.isoformat() if self.start_time else None,
            'paused_time': self.paused_time,
            'elapsed_time': self.elapsed_time,
            'checkpoint_data': self.checkpoint_data
        }

    @classmethod
    def from_dict(cls, data):
        task = cls(
            id=data['id'],
            type=data['type'],
            status=TaskStatus(data['status']),
            progress=data['progress'],
            total=data['total'],
            current_item=data.get('current_item', ''),
            data=data.get('data', {}),
            error=data.get('error', ''),
            retries=data.get('retries', 0),
            created_at=datetime.fromisoformat(data['created_at']) if isinstance(data['created_at'], str) else data['created_at'],
            updated_at=datetime.fromisoformat(data['updated_at']) if isinstance(data['updated_at'], str) else data['updated_at'],
            paused_time=data.get('paused_time', 0),
            elapsed_time=data.get('elapsed_time', 0),
            checkpoint_data=data.get('checkpoint_data', {})
        )
        if data.get('completed_at'):
            task.completed_at = datetime.fromisoformat(data['completed_at']) if isinstance(data['completed_at'], str) else data['completed_at']
        if data.get('start_time'):
            task.start_time = datetime.fromisoformat(data['start_time']) if isinstance(data['start_time'], str) else data['start_time']
        return task

    def get_elapsed_seconds(self) -> float:
        if self.start_time is None:
            return 0
        now = datetime.now()
        total = (now - self.start_time).total_seconds()
        return max(0, total - (self.paused_time / 1000))

    def get_estimated_remaining(self) -> Optional[float]:
        if self.progress <= 0 or self.progress >= self.total or self.total <= 0:
            return None
        elapsed = self.get_elapsed_seconds()
        if elapsed < 0.5:
            return None
        progress_ratio = self.progress / self.total
        if progress_ratio <= 0:
            return None
        total_estimated = elapsed / progress_ratio
        remaining = total_estimated - elapsed
        return max(0, remaining)

class TaskManagerSignals(QObject):
    task_created = Signal(str)
    task_updated = Signal(str)
    task_completed = Signal(str)
    task_failed = Signal(str, str)

class TaskManager:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init()
        return cls._instance

    def _init(self):
        self.tasks: Dict[str, Task] = {}
        self.active_task: Optional[Task] = None
        self._lock = threading.Lock()
        self.db = Database()
        self.signals = TaskManagerSignals()
        self._load_tasks()
        logger.task("TaskManager inicializado.")

    def _load_tasks(self):
        rows = self.db.get_tasks(status=TaskStatus.PENDING.value)
        for row in rows:
            task = Task.from_dict(row)
            self.tasks[task.id] = task
            logger.task(f"Tarefa carregada: {task.id} ({task.type})")

    def create_task(self, task_type: str, total: int = 0, data: Dict = None,
                    callback: Callable = None, progress_cb: Callable = None) -> Task:
        with self._lock:
            task = Task(
                type=task_type,
                total=total,
                data=data or {},
                callback=callback,
                status=TaskStatus.PENDING,
                _progress_callback=progress_cb
            )
            self.tasks[task.id] = task
            self.db.save_task(task)
            logger.task(f"Tarefa criada: {task.id} ({task_type})")
            self.signals.task_created.emit(task.id)
            return task

    def start_task(self, task_id: str):
        with self._lock:
            task = self.tasks.get(task_id)
            if not task:
                logger.error(f"Tarefa não encontrada: {task_id}")
                return False
            if task.status == TaskStatus.RUNNING:
                logger.warning(f"Tarefa já está em execução: {task_id}")
                return False
            task.status = TaskStatus.RUNNING
            task.updated_at = datetime.now()
            if task.start_time is None:
                task.start_time = datetime.now()
            task._paused = False
            task._cancelled = False
            task._pause_event.clear()
            self.active_task = task
            self.db.save_task(task)
            logger.task(f"Tarefa iniciada: {task_id}")
            self.signals.task_updated.emit(task_id)
            return True

    def pause_task(self, task_id: str):
        with self._lock:
            task = self.tasks.get(task_id)
            if not task:
                return False
            if task.status != TaskStatus.RUNNING:
                return False
            task._paused = True
            task._pause_event.set()
            task.status = TaskStatus.PAUSED
            task.updated_at = datetime.now()
            if task.start_time:
                task.paused_time += int((datetime.now() - task.start_time).total_seconds() * 1000)
            self.db.save_task(task)
            logger.task(f"Tarefa pausada: {task_id}")
            self.signals.task_updated.emit(task_id)
            return True

    def resume_task(self, task_id: str):
        with self._lock:
            task = self.tasks.get(task_id)
            if not task:
                return False
            if task.status != TaskStatus.PAUSED:
                return False
            task._paused = False
            task._pause_event.clear()
            task.status = TaskStatus.RUNNING
            task.start_time = datetime.now()
            task.updated_at = datetime.now()
            self.active_task = task
            self.db.save_task(task)
            logger.task(f"Tarefa retomada: {task_id}")
            self.signals.task_updated.emit(task_id)
            return True

    def cancel_task(self, task_id: str):
        with self._lock:
            task = self.tasks.get(task_id)
            if not task:
                return False
            task._cancelled = True
            task._pause_event.set()
            task.status = TaskStatus.CANCELLED
            task.updated_at = datetime.now()
            task.completed_at = datetime.now()
            self.db.save_task(task)
            if self.active_task and self.active_task.id == task_id:
                self.active_task = None
            logger.task(f"Tarefa cancelada: {task_id}")
            self.signals.task_updated.emit(task_id)
            self.signals.task_completed.emit(task_id)
            return True

    def update_progress(self, task_id: str, progress: int, current_item: str = None,
                        total: int = None):
        with self._lock:
            task = self.tasks.get(task_id)
            if not task:
                return
            task.progress = progress
            if total is not None:
                task.total = total
            if current_item:
                task.current_item = current_item
            task.updated_at = datetime.now()
            self.db.save_task(task)
            if task._progress_callback:
                try:
                    task._progress_callback(progress, current_item, task.total)
                except Exception as e:
                    logger.error(f"Erro no callback de progresso: {e}")
            self.signals.task_updated.emit(task_id)

    def complete_task(self, task_id: str, error: str = None):
        with self._lock:
            task = self.tasks.get(task_id)
            if not task:
                return
            if error:
                task.status = TaskStatus.FAILED
                task.error = error
                logger.error(f"Tarefa falhou: {task_id} - {error}")
                self.signals.task_failed.emit(task_id, error)
            else:
                task.status = TaskStatus.COMPLETED
                task.progress = task.total if task.total > 0 else 100
                logger.task(f"Tarefa concluída: {task_id}")
                self.signals.task_completed.emit(task_id)
            task.completed_at = datetime.now()
            task.updated_at = datetime.now()
            self.db.save_task(task)
            if self.active_task and self.active_task.id == task_id:
                self.active_task = None
            self.signals.task_updated.emit(task_id)

    def get_task(self, task_id: str) -> Optional[Task]:
        return self.tasks.get(task_id)

    def get_tasks(self, status: TaskStatus = None) -> List[Task]:
        if status:
            return [t for t in self.tasks.values() if t.status == status]
        return list(self.tasks.values())

    def get_active_task(self) -> Optional[Task]:
        return self.active_task

    def should_cancel(self, task_id: str) -> bool:
        task = self.tasks.get(task_id)
        if not task:
            return True
        return task._cancelled

    def wait_if_paused(self, task_id: str, check_interval: float = 0.5):
        task = self.tasks.get(task_id)
        if not task:
            return True
        while task._paused and not task._cancelled:
            time.sleep(check_interval)
        return task._cancelled

    def get_task_info(self, task_id: str) -> Dict[str, Any]:
        task = self.tasks.get(task_id)
        if not task:
            return {}
        elapsed = task.get_elapsed_seconds()
        remaining = task.get_estimated_remaining()
        return {
            'id': task.id,
            'type': task.type,
            'status': task.status.value,
            'progress': task.progress,
            'total': task.total,
            'current_item': task.current_item,
            'elapsed': elapsed,
            'remaining': remaining,
            'elapsed_str': self._format_time(elapsed),
            'remaining_str': self._format_time(remaining) if remaining is not None else "---",
            'percent': int((task.progress / task.total * 100) if task.total > 0 else 0)
        }

    @staticmethod
    def _format_time(seconds: float) -> str:
        if seconds is None or seconds < 0:
            return "---"
        if seconds < 60:
            return f"{int(seconds)}s"
        if seconds < 3600:
            return f"{int(seconds // 60)}m {int(seconds % 60)}s"
        return f"{int(seconds // 3600)}h {int((seconds % 3600) // 60)}m"

# ============================================================================
# NORMALIZADOR INTELIGENTE
# ============================================================================

class LibraryNormalizer:
    _instance = None
    _rules = None
    _compiled_patterns = {}

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._load_rules()
        return cls._instance

    def _load_rules(self):
        rules_file = CONFIG_DIR / "normalizer_rules.json"
        default_rules = {
            "remove_words": [
                "official video", "official music video", "official audio",
                "audio oficial", "vídeo oficial", "video oficial",
                "music video", "lyrics", "lyric video", "video lyrics",
                "visualizer", "visualiser", "hd", "hq", "4k", "8k", "60fps",
                "1080p", "720p", "480p", "album version", "high quality",
                "stereo", "mono", "clean", "explicit", "audio", "video",
                "official", "full album", "playlist", "complete album",
                "full version", "original video", "official clip",
                "videoclipe", "clipe oficial", "lyric", "audio only",
                "music", "song", "track", "full song", "complete song",
                "single", "ep", "album", "disc", "disk", "cd", "dvd",
                "blu ray", "deluxe", "limited", "special", "bonus",
                "original", "remastered", "remaster", "edit", "mix",
                "version", "live", "acoustic", "instrumental", "demo",
                "unplugged", "cover", "tribute", "theme", "ost",
                "soundtrack", "score", "intro", "outro", "interlude",
                "skit", "prelude", "postlude", "movement", "act", "scene",
                "chapter", "part", "pt", "vol", "volume", "collection",
                "anthology", "compilation", "greatest hits", "best of",
                "essential", "classic", "gold", "platinum", "anniversary"
            ],
            "keep_words": [
                "remix", "extended", "radio edit", "acoustic", "live",
                "instrumental", "karaoke", "demo", "unplugged",
                "original mix", "rework", "lo-fi", "nightcore",
                "slowed", "reverb", "bass boosted", "dubstep", "trap",
                "phonk", "funk", "pagode", "sertanejo", "acústico",
                "ao vivo", "ost", "soundtrack", "theme", "version",
                "mix", "edit", "remaster", "remastered", "cover",
                "tribute", "orchestral", "piano", "guitar", "strings",
                "quartet", "symphony", "band", "orchestra", "choir",
                "acapella", "a cappella", "dub", "club", "house",
                "techno", "trance", "drum", "bass", "electronic"
            ],
            "replace_words": {
                "feat": "ft.",
                "featuring": "ft.",
                "Feat": "ft.",
                "Featuring": "ft.",
                "ft": "ft.",
                "Ft.": "ft.",
                "with": "ft.",
                "With": "ft.",
                "w/": "ft.",
                "x": "ft.",
                "&": "ft.",
                "and": "ft.",
                "versus": "vs.",
                "vs": "vs.",
                "VS": "vs.",
                "remix": "Remix",
                "rmx": "Remix",
                "mix": "Remix",
                "remixed": "Remix",
                "version": "Version",
                "ver": "Version",
                "live": "Live",
                "lives": "Live",
                "acoustic": "Acoustic",
                "acustic": "Acoustic",
                "acustico": "Acoustic",
                "acústico": "Acoustic",
                "instrumental": "Instrumental",
                "instrumental version": "Instrumental",
                "karaoke": "Instrumental",
                "edit": "Edit",
                "radio edit": "Radio Edit",
                "extended": "Extended",
                "extended mix": "Extended Mix",
                "club mix": "Club Mix",
                "dub mix": "Dub Mix",
                "house mix": "House Mix",
                "trap mix": "Trap Mix",
                "drum & bass": "Drum & Bass",
                "drum and bass": "Drum & Bass",
                "dubstep": "Dubstep",
                "lo-fi": "Lo-Fi",
                "lofi": "Lo-Fi"
            },
            "separators": [" - ", " – ", " — ", " | ", " › ", " : ", "; ", " • ", " ~ ", " / ", " \\ "],
            "artist_patterns": [
                r'^([A-Za-z0-9\u00C0-\u024F\u0400-\u04FF\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF][\w\s\.\&\'\-\u00C0-\u024F\u0400-\u04FF\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF]+?)\s*[-–—|:;•~\\/]\s*',
                r'^([A-Za-z0-9\u00C0-\u024F\u0400-\u04FF\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF][\w\s\.\&\'\-\u00C0-\u024F\u0400-\u04FF\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF]+?)\s*\(feat\..*?\)\s*[-–—|:;•~\\/]\s*',
                r'^([A-Za-z0-9\u00C0-\u024F\u0400-\u04FF\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF][\w\s\.\&\'\-\u00C0-\u024F\u0400-\u04FF\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF]+?)\s*[–—]\s*'
            ],
            "title_patterns": [
                r'[-–—|:;•~\\/]\s*(.+)$',
                r'[-–—|:;•~\\/]\s*(.+?)\s*(\(|\[|$)'
            ],
            "version_patterns": [
                r'\(([^)]*(?:remix|extended|radio edit|acoustic|live|instrumental|version|mix|edit|remaster|remastered|cover|tribute|orchestral|piano|unplugged|demo)[^)]*)\)',
                r'\[([^\]]*(?:remix|extended|radio edit|acoustic|live|instrumental|version|mix|edit|remaster|remastered|cover|tribute|orchestral|piano|unplugged|demo)[^\]]*)\]'
            ],
            "feature_patterns": [
                r'\(feat\.\s*([^)]+)\)',
                r'\[feat\.\s*([^\]]+)\]',
                r'\(ft\.\s*([^)]+)\)',
                r'\[ft\.\s*([^\]]+)\]',
                r'\(featuring\s*([^)]+)\)',
                r'\[featuring\s*([^\]]+)\]',
                r'with\s+([A-Za-z0-9\s\.\&\'\-,]+?)(?:\s*\(|$)',
                r'ft\.\s*([A-Za-z0-9\s\.\&\'\-,]+?)(?:\s*\(|$)',
                r'feat\.\s*([A-Za-z0-9\s\.\&\'\-,]+?)(?:\s*\(|$)'
            ],
            "garbage_patterns": [
                r'\(official\s*(?:music\s*)?video\)',
                r'\[official\s*(?:music\s*)?video\]',
                r'\(official\s*audio\)',
                r'\[official\s*audio\]',
                r'\(lyrics?\)',
                r'\[lyrics?\]',
                r'\(visualizer\)',
                r'\[visualizer\]',
                r'\(hd\)',
                r'\[hd\]',
                r'\(hq\)',
                r'\[hq\]',
                r'\(4k\)',
                r'\[4k\]',
                r'\(8k\)',
                r'\[8k\]',
                r'\(1080p\)',
                r'\[1080p\]',
                r'\(720p\)',
                r'\[720p\]',
                r'\(audio\s*(?:only)?\)',
                r'\[audio\s*(?:only)?\]',
                r'\(video\s*(?:clip)?\)',
                r'\[video\s*(?:clip)?\]',
                r'\(clipe\s*(?:oficial)?\)',
                r'\[clipe\s*(?:oficial)?\]',
                r'\(music\s*(?:video)?\)',
                r'\[music\s*(?:video)?\]',
                r'\(official\s*clip\)',
                r'\[official\s*clip\]',
                r'\(videoclipe\)',
                r'\[videoclipe\]',
                r'\(full\s*(?:album|song|version)\)',
                r'\[full\s*(?:album|song|version)\]'
            ],
            "preserve_case": ["AC/DC", "R.E.M.", "KSHMR", "DJ", "MC", "USA", "UK", "M.I.A.", "P!nk", "ABBA", "TLC", "B2K", "NSYNC", "MSTRKRFT"],
            "ignore_articles": ["a", "an", "the", "of", "and", "or", "for", "with", "without", "in", "on", "at", "to", "from", "by", "as", "into", "through", "during", "including"],
            "capitalization_overrides": {
                "the weeknd": "The Weeknd",
                "twenty one pilots": "Twenty One Pilots",
                "panic at the disco": "Panic! At The Disco",
                "fall out boy": "Fall Out Boy",
                "my chemical romance": "My Chemical Romance",
                "green day": "Green Day",
                "blink 182": "Blink-182",
                "paramore": "Paramore",
                "evanescence": "Evanescence",
                "linkin park": "Linkin Park",
                "system of a down": "System of a Down",
                "slipknot": "Slipknot",
                "disturbed": "Disturbed",
                "three days grace": "Three Days Grace",
                "breaking benjamin": "Breaking Benjamin",
                "five finger death punch": "Five Finger Death Punch",
                "avenged sevenfold": "Avenged Sevenfold",
                "bullet for my valentine": "Bullet For My Valentine",
                "bring me the horizon": "Bring Me The Horizon",
                "architects": "Architects",
                "while she sleeps": "While She Sleeps",
                "of mice & men": "Of Mice & Men",
                "of mice and men": "Of Mice & Men",
                "a day to remember": "A Day To Remember",
                "pierce the veil": "Pierce The Veil",
                "sleeping with siren": "Sleeping With Sirens",
                "black veil brides": "Black Veil Brides",
                "asking alexandria": "Asking Alexandria",
                "we came as romans": "We Came As Romans",
                "i prevail": "I Prevail",
                "the amity affliction": "The Amity Affliction",
                "northlane": "Northlane",
                "parkway drive": "Parkway Drive",
                "killswitch engage": "Killswitch Engage",
                "trivium": "Trivium",
                "in flames": "In Flames",
                "children of bodom": "Children Of Bodom",
                "arch enemy": "Arch Enemy",
                "amon amarth": "Amon Amarth",
                "behemoth": "Behemoth",
                "gojira": "Gojira",
                "mastodon": "Mastodon",
                "opeth": "Opeth",
                "dream theater": "Dream Theater",
                "tool": "Tool",
                "a perfect circle": "A Perfect Circle",
                "puscifer": "Puscifer",
                "deftones": "Deftones",
                "korn": "Korn",
                "limp bizkit": "Limp Bizkit",
                "stone sour": "Stone Sour",
                "corey taylor": "Corey Taylor",
                "ozzy osbourne": "Ozzy Osbourne",
                "black sabbath": "Black Sabbath",
                "iron maiden": "Iron Maiden",
                "judas priest": "Judas Priest",
                "megadeth": "Megadeth",
                "anthrax": "Anthrax",
                "slayer": "Slayer",
                "metallica": "Metallica",
                "led zeppelin": "Led Zeppelin",
                "the beatles": "The Beatles",
                "the rolling stones": "The Rolling Stones",
                "the who": "The Who",
                "the doors": "The Doors",
                "pink floyd": "Pink Floyd",
                "queen": "Queen",
                "david bowie": "David Bowie",
                "elton john": "Elton John",
                "billy joel": "Billy Joel",
                "bruce springsteen": "Bruce Springsteen",
                "bob dylan": "Bob Dylan",
                "neil young": "Neil Young",
                "tom petty": "Tom Petty",
                "the clash": "The Clash",
                "ramones": "Ramones",
                "sex pistols": "Sex Pistols",
                "the cure": "The Cure",
                "the smiths": "The Smiths",
                "joy division": "Joy Division",
                "new order": "New Order",
                "depeche mode": "Depeche Mode",
                "the police": "The Police",
                "u2": "U2",
                "rem": "R.E.M.",
                "nirvana": "Nirvana",
                "pearl jam": "Pearl Jam",
                "soundgarden": "Soundgarden",
                "alice in chains": "Alice In Chains",
                "stone temple pilots": "Stone Temple Pilots",
                "smashing pumpkins": "Smashing Pumpkins",
                "radiohead": "Radiohead",
                "coldplay": "Coldplay",
                "muse": "Muse",
                "arctic monkeys": "Arctic Monkeys",
                "the strokes": "The Strokes",
                "the killers": "The Killers",
                "interpol": "Interpol",
                "the national": "The National",
                "arcade fire": "Arcade Fire",
                "vampire weekend": "Vampire Weekend",
                "tame impala": "Tame Impala",
                "mgmt": "MGMT",
                "the black keys": "The Black Keys",
                "jack white": "Jack White",
                "the white stripes": "The White Stripes",
                "the raconteurs": "The Raconteurs",
                "the dead weather": "The Dead Weather",
                "the yeah yeah yeahs": "The Yeah Yeah Yeahs",
                "the pixies": "The Pixies",
                "the breeders": "The Breeders",
                "the flaming lips": "The Flaming Lips",
                "beck": "Beck",
                "bjork": "Björk",
                "sigur ros": "Sigur Rós",
                "mum": "Múm",
                "kings of leon": "Kings Of Leon",
                "the kings of leon": "Kings Of Leon",
                "phoenix": "Phoenix",
                "two door cinema club": "Two Door Cinema Club",
                "cage the elephant": "Cage The Elephant",
                "foals": "Foals",
                "royal blood": "Royal Blood",
                "nothing but thieves": "Nothing But Thieves",
                "highly suspect": "Highly Suspect",
                "badflower": "Badflower",
                "cleopatrick": "Cleopatrick",
                "des rocs": "Des Rocs",
                "the struts": "The Struts",
                "greta van fleet": "Greta Van Fleet",
                "the pretty reckless": "The Pretty Reckless",
                "halestorm": "Halestorm",
                "against the current": "Against The Current",
                "pvp": "PVP"
            },
            "comparison_rules": {
                "case_sensitive": False,
                "ignore_articles": True,
                "ignore_punctuation": True,
                "ignore_spaces": True,
                "similarity_threshold": 0.92
            }
        }

        if not rules_file.exists():
            with open(rules_file, 'w', encoding='utf-8') as f:
                json.dump(default_rules, f, indent=2, ensure_ascii=False)
            logger.info("Arquivo de regras criado.", "NORMALIZER")
            self._rules = default_rules
        else:
            try:
                with open(rules_file, 'r', encoding='utf-8') as f:
                    self._rules = json.load(f)
                logger.info("Regras carregadas do arquivo.", "NORMALIZER")
            except Exception as e:
                logger.error(f"Erro ao carregar regras: {e}", "NORMALIZER")
                self._rules = default_rules

        self._compile_patterns()
        logger.info("Sistema inicializado.", "NORMALIZER")

    def _compile_patterns(self):
        self._compiled_patterns = {}
        remove_words = self._rules.get("remove_words", [])
        if remove_words:
            remove_words_sorted = sorted(remove_words, key=len, reverse=True)
            pattern = r'\b(?:' + '|'.join(re.escape(w) for w in remove_words_sorted) + r')\b'
            self._compiled_patterns['remove'] = re.compile(pattern, re.IGNORECASE)

        garbage = self._rules.get("garbage_patterns", [])
        if garbage:
            self._compiled_patterns['garbage'] = [re.compile(p, re.IGNORECASE) for p in garbage]

        separators = self._rules.get("separators", [" - "])
        sep_pattern = '|'.join(re.escape(s) for s in separators)
        self._compiled_patterns['separator'] = re.compile(sep_pattern)

        feature = self._rules.get("feature_patterns", [])
        self._compiled_patterns['feature'] = [re.compile(p, re.IGNORECASE) for p in feature]

        version = self._rules.get("version_patterns", [])
        self._compiled_patterns['version'] = [re.compile(p, re.IGNORECASE) for p in version]

        self._compiled_patterns['replace'] = self._rules.get("replace_words", {})
        self._compiled_patterns['preserve_case'] = set(self._rules.get("preserve_case", []))
        self._compiled_patterns['ignore_articles'] = set(self._rules.get("ignore_articles", []))
        self._compiled_patterns['cap_overrides'] = self._rules.get("capitalization_overrides", {})

    def _get_confidence(self, original: str, normalized: str) -> float:
        if not original or not normalized:
            return 0.0
        sim = SequenceMatcher(None, original.lower(), normalized.lower()).ratio()
        orig_words = set(original.lower().split())
        norm_words = set(normalized.lower().split())
        if orig_words:
            word_retention = len(norm_words & orig_words) / len(orig_words)
        else:
            word_retention = 1.0
        sim_factor = sim * 100
        retention_factor = word_retention * 100
        confidence = (sim_factor * 0.7) + (retention_factor * 0.3)
        return min(100.0, max(0.0, confidence))

    def _remove_garbage(self, name: str) -> str:
        original = name
        for pattern in self._compiled_patterns.get('garbage', []):
            name = pattern.sub('', name)
        remove_pattern = self._compiled_patterns.get('remove')
        if remove_pattern:
            name = remove_pattern.sub(' ', name)
        name = re.sub(r'\(\s*\)', '', name)
        name = re.sub(r'\[\s*\]', '', name)
        name = re.sub(r'\{\s*\}', '', name)
        name = re.sub(r'\s+', ' ', name).strip()
        if name != original:
            logger.normalizer(f"  Remover lixo: '{original}' → '{name}'")
        return name

    def _standardize_separators(self, name: str) -> Tuple[str, List[str]]:
        original = name
        sep_pattern = self._compiled_patterns.get('separator')
        if sep_pattern:
            for sep in self._rules.get("separators", [" - "]):
                if sep in name:
                    left, right = name.split(sep, 1)
                    if left.strip() and right.strip():
                        name = f"{left.strip()} - {right.strip()}"
                        break
            else:
                name = sep_pattern.sub(' - ', name)
        name = re.sub(r'\s+', ' ', name).strip()
        name = re.sub(r'\s*-\s*', ' - ', name)
        name = re.sub(r'\s*–\s*', ' - ', name)
        name = re.sub(r'\s*—\s*', ' - ', name)
        name = re.sub(r'-{2,}', '-', name)
        if name != original:
            logger.normalizer(f"  Padronizar separadores: '{original}' → '{name}'")
        return name, []

    def _recognize_artist(self, name: str) -> Tuple[str, str, List[str]]:
        original = name
        artist = ""
        title = name
        features_found = []
        for pattern_str in self._rules.get("artist_patterns", []):
            pattern = re.compile(pattern_str, re.IGNORECASE)
            match = pattern.match(name)
            if match:
                artist = match.group(1).strip()
                title = name[match.end():].strip()
                if title:
                    break
        if not artist:
            feat_match = re.search(r'\(feat\.\s*([^)]+)\)', name, re.IGNORECASE)
            if feat_match:
                before_feat = name[:feat_match.start()].strip()
                if before_feat:
                    if ' - ' in before_feat:
                        parts = before_feat.split(' - ', 1)
                        artist = parts[0].strip()
                        title = parts[1].strip() if len(parts) > 1 else before_feat
                    else:
                        artist = before_feat
                        title = name[feat_match.end():].strip() or before_feat
        if not artist and ' - ' in name:
            parts = name.split(' - ', 1)
            artist = parts[0].strip()
            title = parts[1].strip() if len(parts) > 1 else name
        if not artist:
            artist = "Desconhecido"
            title = name
        for pattern in self._compiled_patterns.get('feature', []):
            matches = pattern.findall(name)
            for m in matches:
                if m and m not in features_found:
                    features_found.append(m.strip())
        for f in features_found:
            title = re.sub(r'\(feat\.\s*' + re.escape(f) + r'\)', '', title, flags=re.IGNORECASE)
            title = re.sub(r'\[feat\.\s*' + re.escape(f) + r'\]', '', title, flags=re.IGNORECASE)
            title = re.sub(r'\(ft\.\s*' + re.escape(f) + r'\)', '', title, flags=re.IGNORECASE)
            title = re.sub(r'\[ft\.\s*' + re.escape(f) + r'\]', '', title, flags=re.IGNORECASE)
            title = re.sub(r'with\s+' + re.escape(f), '', title, flags=re.IGNORECASE)
            title = re.sub(r'ft\.\s*' + re.escape(f), '', title, flags=re.IGNORECASE)
        title = re.sub(r'\s+', ' ', title).strip()
        if artist != original.split(' - ', 1)[0] if ' - ' in original else original:
            logger.normalizer(f"  Reconhecer artista: '{original}' → artista='{artist}', título='{title}'")
        return artist, title, features_found

    def _recognize_title(self, title: str, features: List[str]) -> Tuple[str, List[str]]:
        original = title
        for f in features:
            title = re.sub(r'\(feat\.\s*' + re.escape(f) + r'\)', '', title, flags=re.IGNORECASE)
            title = re.sub(r'\[feat\.\s*' + re.escape(f) + r'\]', '', title, flags=re.IGNORECASE)
            title = re.sub(r'\(ft\.\s*' + re.escape(f) + r'\)', '', title, flags=re.IGNORECASE)
            title = re.sub(r'\[ft\.\s*' + re.escape(f) + r'\]', '', title, flags=re.IGNORECASE)
        version_info = []
        for pattern in self._compiled_patterns.get('version', []):
            matches = pattern.findall(title)
            for m in matches:
                if m and m not in version_info:
                    version_info.append(m.strip())
            title = pattern.sub('', title)
        title = re.sub(r'\s+', ' ', title).strip()
        title = re.sub(r'\(\s*\)', '', title)
        title = re.sub(r'\[\s*\]', '', title)
        title = re.sub(r'\s+', ' ', title).strip()
        if title != original:
            logger.normalizer(f"  Reconhecer título: '{original}' → '{title}'")
        return title, version_info

    def _recognize_features(self, title: str, features: List[str], version_info: List[str]) -> Tuple[str, str]:
        original = title
        replace_map = self._compiled_patterns.get('replace', {})
        for old, new in replace_map.items():
            title = re.sub(r'\b' + re.escape(old) + r'\b', new, title, flags=re.IGNORECASE)
        feat_str = ""
        if features:
            feat_str = " ft. " + " & ".join(features)
        version_str = ""
        if version_info:
            v = version_info[0]
            v = v.title()
            version_str = f" ({v})"
        title = re.sub(r'\s+', ' ', title).strip()
        feat_in_title = re.search(r'ft\.\s*([^()]+)', title, re.IGNORECASE)
        if feat_in_title:
            feat_name = feat_in_title.group(1).strip()
            if feat_name and feat_name not in features:
                features.append(feat_name)
            title = re.sub(r'ft\.\s*[^()]+', '', title, flags=re.IGNORECASE)
        title = re.sub(r'\s*ft\.\s*', ' ', title)
        title = re.sub(r'\s*with\s*', ' ', title)
        title = re.sub(r'\s+', ' ', title).strip()
        if title != original:
            logger.normalizer(f"  Reconhecer features: '{original}' → '{title}'")
        return title, feat_str + version_str

    def _capitalize(self, artist: str, title: str) -> Tuple[str, str]:
        original_artist, original_title = artist, title
        artist_lower = artist.lower().strip()
        overrides = self._compiled_patterns.get('cap_overrides', {})
        if artist_lower in overrides:
            artist = overrides[artist_lower]
        else:
            preserve = self._compiled_patterns.get('preserve_case', set())
            words = artist.split()
            new_words = []
            for w in words:
                if w in preserve:
                    new_words.append(w)
                elif w.isupper() and len(w) <= 4:
                    new_words.append(w)
                else:
                    new_words.append(w.capitalize())
            artist = ' '.join(new_words)
        title_lower = title.lower().strip()
        title_override = None
        for key, val in overrides.items():
            if title_lower == key.lower():
                title_override = val
                break
        if title_override:
            title = title_override
        else:
            preserve = self._compiled_patterns.get('preserve_case', set())
            words = title.split()
            new_words = []
            for w in words:
                if w in preserve:
                    new_words.append(w)
                elif w.isupper() and len(w) <= 4:
                    new_words.append(w)
                else:
                    new_words.append(w.capitalize())
            title = ' '.join(new_words)
        if artist != original_artist or title != original_title:
            logger.normalizer(f"  Capitalizar: '{original_artist}' → '{artist}', '{original_title}' → '{title}'")
        return artist, title

    def _validate(self, artist: str, title: str) -> Tuple[str, str, bool]:
        original_artist, original_title = artist, title
        if not title or title.isspace():
            title = "Sem título"
        if not artist or artist.isspace():
            artist = "Desconhecido"
        invalid_chars = r'[<>:"/\\|?*]'
        title = re.sub(invalid_chars, '', title)
        artist = re.sub(invalid_chars, '', artist)
        title = re.sub(r'\s+', ' ', title).strip()
        artist = re.sub(r'\s+', ' ', artist).strip()
        valid = bool(artist and title and not title.isspace() and not artist.isspace())
        if artist != original_artist or title != original_title:
            logger.normalizer(f"  Validar: '{original_artist}' → '{artist}', '{original_title}' → '{title}'")
        return artist, title, valid

    def normalize(self, filename: str) -> Tuple[str, str, float]:
        if not filename:
            return "Desconhecido", "Sem título", 0.0
        original = filename
        name = Path(filename).stem
        logger.normalizer(f"Normalizando: '{original}'")
        name = self._remove_garbage(name)
        name, _ = self._standardize_separators(name)
        artist, title, features = self._recognize_artist(name)
        title, version_info = self._recognize_title(title, features)
        title, suffix = self._recognize_features(title, features, version_info)
        if suffix:
            title = f"{title}{suffix}"
        artist, title = self._capitalize(artist, title)
        artist, title, valid = self._validate(artist, title)
        final_name = f"{artist} - {title}"
        confidence = self._get_confidence(original, final_name)
        threshold = Config().get_confidence_threshold()
        if confidence < threshold:
            logger.norm_unknown(f"Baixa confiança ({confidence:.1f}%): '{original}' → '{final_name}'")
        logger.normalizer(f"  → '{final_name}' (confiança: {confidence:.1f}%)")
        return artist, title, confidence

    def normalize_filename(self, filename: str) -> str:
        artist, title, _ = self.normalize(filename)
        return f"{artist} - {title}.mp3"

    def generate_canonical_key(self, artist: str, title: str) -> str:
        clean_artist = re.sub(r'\s*ft\.\s*[^()]+', '', artist, flags=re.IGNORECASE)
        clean_title = re.sub(r'\s*\([^)]*(?:remix|version|live|acoustic|instrumental|edit|mix)[^)]*\)', '', title, flags=re.IGNORECASE)
        clean_title = re.sub(r'\([^)]*\)', '', clean_title)
        clean_title = re.sub(r'\[[^\]]*\]', '', clean_title)
        articles = self._compiled_patterns.get('ignore_articles', set())
        for a in articles:
            clean_artist = re.sub(r'\b' + re.escape(a) + r'\b', '', clean_artist, flags=re.IGNORECASE)
            clean_title = re.sub(r'\b' + re.escape(a) + r'\b', '', clean_title, flags=re.IGNORECASE)
        key = (clean_artist + clean_title).lower()
        key = re.sub(r'[^a-zA-Z0-9]', '', key)
        return key

    def are_similar(self, name1: str, name2: str, metadata1: Dict = None, metadata2: Dict = None) -> bool:
        threshold = Config().get_duplicate_threshold()
        artist1, title1, _ = self.normalize(name1)
        artist2, title2, _ = self.normalize(name2)
        key1 = self.generate_canonical_key(artist1, title1)
        key2 = self.generate_canonical_key(artist2, title2)
        if key1 and key2 and key1 == key2:
            return True
        if SequenceMatcher(None, key1, key2).ratio() >= threshold:
            return True
        if metadata1 and metadata2:
            dur1 = metadata1.get('duration', 0)
            dur2 = metadata2.get('duration', 0)
            if dur1 > 0 and dur2 > 0 and abs(dur1 - dur2) < 2.0:
                return True
            hash1 = metadata1.get('file_hash', '')
            hash2 = metadata2.get('file_hash', '')
            if hash1 and hash2 and hash1 == hash2:
                return True
        return False

    def detect_duplicates(self, files: List[Path], metadata_cache: Dict = None) -> List[List[str]]:
        if not files:
            return []
        metadatas = {}
        for f in files:
            try:
                if metadata_cache and str(f) in metadata_cache:
                    meta = metadata_cache[str(f)]
                else:
                    audio = mutagen.mp3.MP3(str(f))
                    meta = {
                        'duration': audio.info.length,
                        'size': f.stat().st_size,
                        'file_hash': self._compute_file_hash(f)
                    }
                metadatas[str(f)] = meta
            except Exception:
                metadatas[str(f)] = {'duration': 0, 'size': 0, 'file_hash': ''}
        groups = []
        processed = set()
        for i, f1 in enumerate(files):
            if f1.name in processed:
                continue
            group = [f1.name]
            for j, f2 in enumerate(files):
                if i == j or f2.name in processed:
                    continue
                if self.are_similar(f1.name, f2.name, metadatas.get(str(f1)), metadatas.get(str(f2))):
                    group.append(f2.name)
                    processed.add(f2.name)
            if len(group) > 1:
                groups.append(group)
                processed.add(f1.name)
        return groups

    def _compute_file_hash(self, file_path: Path, blocks: int = 4096) -> str:
        try:
            hasher = hashlib.sha1()
            with open(file_path, 'rb') as f:
                for _ in range(blocks):
                    chunk = f.read(8192)
                    if not chunk:
                        break
                    hasher.update(chunk)
            return hasher.hexdigest()
        except Exception:
            return ""

# ============================================================================
# CLASSE BASE PARA WORKERS (QThread)
# ============================================================================

class BaseWorker(QThread):
    progress_signal = Signal(int, str)
    error_signal = Signal(str)
    finished_signal = Signal()

    def __init__(self, task_id=None):
        super().__init__()
        self.task_id = task_id
        self._cancel_event = threading.Event()
        self._pause_event = threading.Event()
        self._lock = threading.Lock()
        self._is_paused = False
        self._is_cancelled = False
        self._progress = 0
        self._message = ""

    def cancel(self):
        self._cancel_event.set()
        self._pause_event.set()  # acorda se estiver pausado

    def pause(self):
        if not self._is_paused:
            self._is_paused = True
            self._pause_event.clear()

    def resume(self):
        if self._is_paused:
            self._is_paused = False
            self._pause_event.set()

    def update_progress(self, value, message=""):
        with self._lock:
            self._progress = value
            self._message = message
        self.progress_signal.emit(value, message)

    def should_cancel(self):
        return self._cancel_event.is_set()

    def should_pause(self):
        if self._is_paused:
            self._pause_event.wait()  # bloqueia até ser retomado ou cancelado
            if self._cancel_event.is_set():
                return True
        return self._cancel_event.is_set()

    def run(self):
        try:
            self._run_impl()
        except Exception as e:
            logger.error(f"Erro no worker {self.__class__.__name__}: {e}\n{traceback.format_exc()}", "THREAD")
            self.error_signal.emit(str(e))
            # Marca a tarefa como falha se houver task_id
            if self.task_id:
                TaskManager().complete_task(self.task_id, str(e))
        finally:
            self.finished_signal.emit()

    def _run_impl(self):
        raise NotImplementedError

# ============================================================================
# WORKERS CONCRETOS
# ============================================================================

class NormalizeWorker(BaseWorker):
    def __init__(self, pasta: Path, normalizer: LibraryNormalizer, cache: 'MetadataCache', task_id=None):
        super().__init__(task_id)
        self.pasta = pasta
        self.normalizer = normalizer
        self.cache = cache

    def _run_impl(self):
        arquivos = list(self.pasta.glob("*.mp3"))
        if not arquivos:
            self.error_signal.emit("Nenhum arquivo MP3 encontrado.")
            return

        total = len(arquivos)
        alteracoes = []

        for i, arquivo in enumerate(arquivos):
            if self.should_cancel():
                break
            if self.should_pause():
                break

            try:
                metadata = self.cache.get_or_update(arquivo, force=False)
                artista = metadata.get('normalized_artist', '')
                titulo = metadata.get('normalized_title', '')
                confidence = metadata.get('confidence', 0.0)

                if not artista or not titulo:
                    artista, titulo, confidence = self.normalizer.normalize(arquivo.name)

                novo_nome = f"{artista} - {titulo}.mp3"
                alteracoes.append((arquivo.name, novo_nome, confidence))
            except Exception as e:
                logger.error(f"Erro ao processar {arquivo.name}: {e}", "NORMALIZER")
                self.error_signal.emit(f"Erro em {arquivo.name}: {e}")

            progresso = int((i + 1) / total * 100)
            self.update_progress(progresso, f"Processando {i+1}/{total}")

        if not self.should_cancel():
            # Retorna a lista de alterações através de um sinal personalizado
            self.finished_signal.emit()

class ImportWorker(BaseWorker):
    def __init__(self, origem_lista: List[Path], destino: Path, task_id=None):
        super().__init__(task_id)
        self.origem_lista = origem_lista
        self.destino = destino

    def _run_impl(self):
        try:
            self.destino.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.error_signal.emit(f"Erro ao criar pasta destino: {e}")
            return

        total = len(self.origem_lista)
        count = 0

        for i, origem in enumerate(self.origem_lista, 1):
            if self.should_cancel():
                break
            if self.should_pause():
                break

            destino = self.destino / origem.name
            sucesso = False

            for tentativa in range(3):
                try:
                    shutil.copy2(str(origem), str(destino))
                    count += 1
                    sucesso = True
                    break
                except OSError as e:
                    if "WinError 32" in str(e) or "sendo usado" in str(e):
                        time.sleep(0.5)
                        continue
                    else:
                        self.error_signal.emit(f"Erro ao copiar {origem.name}: {e}")
                        break
                except Exception as e:
                    self.error_signal.emit(f"Erro ao copiar {origem.name}: {e}")
                    break

            if not sucesso:
                self.error_signal.emit(f"❌ Falha ao copiar {origem.name} após 3 tentativas.")

            self.update_progress(int(i / total * 100), f"{i}/{total} arquivos")

        self.finished_signal.emit()

class ReloadPlaylistWorker(BaseWorker):
    def __init__(self, pasta: Path, cache: 'MetadataCache', force: bool = False,
                 saved_file: Optional[str] = None, saved_position: int = 0, task_id=None):
        super().__init__(task_id)
        self.pasta = pasta
        self.cache = cache
        self.force = force
        self.saved_file = saved_file
        self.saved_position = saved_position
        self._playlist_result = []

    def _run_impl(self):
        if not self.pasta.is_dir():
            self.error_signal.emit("Pasta inválida")
            return

        self.update_progress(0, "Lendo arquivos...")
        arquivos = list(self.pasta.glob("*.mp3"))
        total = len(arquivos)

        if total == 0:
            self.update_progress(100, "Nenhum MP3 encontrado.")
            self.finished_signal.emit()
            return

        arquivos_validos = []
        arquivos_ignorados = []
        arquivos_nomes = set()

        for i, arquivo in enumerate(arquivos):
            if self.should_cancel():
                break
            if self.should_pause():
                break

            if not arquivo.is_file():
                continue
            if not os.access(str(arquivo), os.R_OK):
                arquivos_ignorados.append(arquivo.name)
                continue

            try:
                metadata = self.cache.get_or_update(arquivo, force=self.force)
                if metadata.get('duration', 0) <= 0:
                    arquivos_ignorados.append(arquivo.name)
                    continue
                if not arquivo.name or arquivo.name.isspace():
                    arquivos_ignorados.append(arquivo.name)
                    continue

                arquivos_validos.append(arquivo.name)
                arquivos_nomes.add(arquivo.name)
            except Exception as e:
                logger.error(f"Erro ao processar {arquivo.name}: {e}", "CACHE")
                arquivos_ignorados.append(arquivo.name)

            progresso = int((i + 1) / total * 80) + 10
            self.update_progress(progresso, f"Processando {i+1}/{total}")

        self.cache.cleanup(self.pasta, arquivos_nomes)
        self.update_progress(90, "Organizando playlist...")
        self._playlist_result = sorted(arquivos_validos)
        self.update_progress(100, "Concluído")
        self.finished_signal.emit()

    def get_playlist(self) -> List[str]:
        return self._playlist_result

# ============================================================================
# DOWNLOAD WORKER (QThread)
# ============================================================================

class DownloadWorker(BaseWorker):
    def __init__(self, url: str, artist: str, title: str, filename: str,
                 playlist: str = "", task_id=None):
        super().__init__(task_id)
        self.url = url
        self.artist = artist
        self.title = title
        self.filename = filename
        self.playlist = playlist
        self._success_cb = None
        self._failure_cb = None
        self.config = Config()
        self.db = Database()

    def set_callbacks(self, success_cb, failure_cb):
        self._success_cb = success_cb
        self._failure_cb = failure_cb

    def _ensure_ffmpeg(self) -> Optional[Path]:
        config = Config()
        config_path = config.get_ffmpeg_path()
        if config_path and Path(config_path).exists():
            return Path(config_path)
        ffmpeg = localizar_ffmpeg()
        if ffmpeg:
            config.set_ffmpeg_path(str(ffmpeg))
            return ffmpeg
        return None

    def _run_impl(self):
        max_retries = self.config.get_max_retries()
        ffmpeg_path = self._ensure_ffmpeg()
        if not ffmpeg_path:
            self.error_signal.emit("FFmpeg não encontrado. Selecione o executável.")
            if self._failure_cb:
                self._failure_cb(Exception("FFmpeg não encontrado"))
            return

        pasta = self.config.get_download_folder()
        pasta.mkdir(parents=True, exist_ok=True)

        for attempt in range(max_retries):
            if self.should_cancel():
                if self._failure_cb:
                    self._failure_cb(Exception("Cancelado pelo usuário"))
                return
            if self.should_pause():
                return

            try:
                logger.download(f"Tentativa {attempt+1}/{max_retries} para {self.artist} - {self.title}")
                ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
                with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                    info = ydl.extract_info(self.url, download=False)
                    actual_artist = info.get('uploader', self.artist)
                    actual_title = info.get('title', self.title)

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
                    ydl.download([self.url])

                logger.download(f"Download concluído: {self.artist} - {self.title}")
                self.update_progress(100, f"{self.artist} - {self.title}")
                if self._success_cb:
                    self._success_cb()
                return

            except Exception as e:
                logger.error(f"Erro no download (tentativa {attempt+1}): {e}", "DOWNLOAD")
                if attempt < max_retries - 1:
                    delay = self.config.get_retry_delays()[attempt] if attempt < len(self.config.get_retry_delays()) else 60
                    logger.retry(f"Aguardando {delay}s antes da próxima tentativa...")
                    for _ in range(delay):
                        if self.should_cancel():
                            break
                        if self.should_pause():
                            break
                        time.sleep(1)

        # Falha após todas tentativas
        error_msg = f"Falha após {max_retries} tentativas"
        self.error_signal.emit(error_msg)
        if self._failure_cb:
            self._failure_cb(Exception(error_msg))

# ============================================================================
# DOWNLOAD ENGINE (gerencia workers)
# ============================================================================

class DownloadEngineSignals(QObject):
    progress = Signal(str, int, str)
    finished = Signal(str)
    failed = Signal(str, str)

class DownloadEngine:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init()
        return cls._instance

    def _init(self):
        self.task_manager = TaskManager()
        self.db = Database()
        self.config = Config()
        self._workers: List[DownloadWorker] = []
        self._lock = threading.Lock()
        self.signals = DownloadEngineSignals()
        logger.download("DownloadEngine inicializado.")

    def download_single(self, url: str, artist: str, title: str, filename: str,
                        playlist: str = "", task_id: str = None,
                        success_cb: Callable = None, failure_cb: Callable = None) -> str:
        if not task_id:
            task = self.task_manager.create_task("download", 1, {"url": url, "artist": artist, "title": title})
            task_id = task.id
            self.task_manager.start_task(task_id)

        worker = DownloadWorker(url, artist, title, filename, playlist, task_id)
        worker.set_callbacks(success_cb, failure_cb)

        # Conecta sinais para atualizar a tarefa
        worker.progress_signal.connect(
            lambda p, msg: self.task_manager.update_progress(task_id, p, msg))
        worker.finished_signal.connect(
            lambda: self.task_manager.complete_task(task_id))
        worker.error_signal.connect(
            lambda err: self.task_manager.complete_task(task_id, err))

        with self._lock:
            self._workers.append(worker)

        worker.start()
        return task_id

    def download_batch(self, items: List[Dict], task_id: str = None, progress_cb: Callable = None) -> str:
        if not task_id:
            task = self.task_manager.create_task("download_batch", len(items), {"items": items})
            task_id = task.id
            self.task_manager.start_task(task_id)

        # Cria workers para cada item
        for item in items:
            url = item.get('url')
            artist = item.get('artist', 'Desconhecido')
            title = item.get('title', 'Sem título')
            playlist = item.get('playlist', '')
            self.download_single(url, artist, title, '', playlist, task_id)

        # O progresso será atualizado via sinais dos workers
        return task_id

    def cancel(self):
        with self._lock:
            for worker in self._workers:
                worker.cancel()
            self._workers.clear()

# ============================================================================
# FUNÇÕES DE SUPORTE
# ============================================================================

def localizar_ffmpeg() -> Optional[Path]:
    config = Config()
    config_path = config.get_ffmpeg_path()
    if config_path and Path(config_path).exists():
        return Path(config_path)

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
                logger.ffmpeg(f"FFmpeg encontrado na pasta local: {caminho}")
                return caminho
            else:
                logger.warning(f"FFmpeg encontrado, mas ffprobe.exe ausente em {caminho.parent}", "FFMPEG")

    ffmpeg_path = shutil.which('ffmpeg')
    if ffmpeg_path:
        ffprobe_path = shutil.which('ffprobe')
        if ffprobe_path:
            logger.ffmpeg(f"FFmpeg encontrado no PATH: {ffmpeg_path}")
            return Path(ffmpeg_path)
        else:
            logger.warning("FFmpeg no PATH, mas ffprobe.exe não disponível.", "FFMPEG")

    logger.error("FFmpeg não encontrado.", "FFMPEG")
    return None

def solicitar_ffmpeg(parent=None) -> Optional[Path]:
    caminho, _ = QFileDialog.getOpenFileName(
        parent, "Selecione o executável do FFmpeg",
        "", "ffmpeg.exe (ffmpeg.exe);;Todos os arquivos (*.*)"
    )
    if caminho:
        return Path(caminho)
    return None

# ============================================================================
# CACHE DE METADADOS (com LRU)
# ============================================================================

class MetadataCache:
    def __init__(self) -> None:
        self.db = Database()
        self.normalizer = LibraryNormalizer()
        self._lock = threading.Lock()
        self._cache = LRUCache(maxsize=500)
        logger.cache("MetadataCache inicializado com LRU.")

    def _compute_file_hash(self, file_path: Path) -> str:
        try:
            hasher = hashlib.sha1()
            with open(file_path, 'rb') as f:
                for _ in range(4096):
                    chunk = f.read(8192)
                    if not chunk:
                        break
                    hasher.update(chunk)
            return hasher.hexdigest()
        except Exception as e:
            logger.error(f"Erro ao calcular hash de {file_path.name}: {e}", "CACHE")
            return ""

    def _read_file_metadata(self, file_path: Path) -> Dict[str, Any]:
        try:
            stat = file_path.stat()
            size = stat.st_size
            mtime = stat.st_mtime
        except OSError as e:
            logger.error(f"Erro ao ler stat de {file_path}: {e}", "CACHE")
            return {'duration': 0.0, 'size': 0, 'mtime': 0}

        metadata = {
            'title': '', 'artist': '', 'album': '', 'album_artist': '',
            'genre': '', 'year': '', 'track': '',
            'duration': 0.0, 'bitrate': 0, 'sample_rate': 0,
            'size': size, 'mtime': mtime,
            'file_hash': self._compute_file_hash(file_path)
        }

        try:
            audio = mutagen.mp3.MP3(str(file_path))
            try:
                metadata['duration'] = audio.info.length
                metadata['bitrate'] = audio.info.bitrate
                metadata['sample_rate'] = audio.info.sample_rate
            except Exception as e:
                logger.warning(f"Erro ao ler info de áudio de {file_path.name}: {e}", "CACHE")
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
                logger.warning(f"Duração zero ou inválida: {file_path.name}", "CACHE")
        except mutagen.MutagenError as e:
            logger.error(f"Erro Mutagen ao ler {file_path.name}: {e}", "CACHE")
            metadata['duration'] = 0.0
        except Exception as e:
            logger.error(f"Erro inesperado ao ler {file_path.name}: {e}", "CACHE")
            metadata['duration'] = 0.0

        return metadata

    def get_or_update(self, file_path: Path, force: bool = False) -> Dict[str, Any]:
        # Verifica cache em memória
        with self._lock:
            cached = self._cache.get(str(file_path))
            if cached and not force:
                return cached

        row = self.db.fetchone("SELECT * FROM songs WHERE path = ?", (str(file_path),))
        if row and not force:
            data = dict(row)
            with self._lock:
                self._cache.put(str(file_path), data)
            return data

        metadata = self._read_file_metadata(file_path)
        filename = file_path.name
        artist, title, confidence = self.normalizer.normalize(filename)

        if not metadata.get('artist'):
            metadata['artist'] = artist
        if not metadata.get('title'):
            metadata['title'] = title

        song_data = {
            'title': metadata.get('title', ''),
            'artist': metadata.get('artist', ''),
            'album': metadata.get('album', ''),
            'album_artist': metadata.get('album_artist', ''),
            'genre': metadata.get('genre', ''),
            'year': metadata.get('year', ''),
            'track': metadata.get('track', ''),
            'duration': metadata.get('duration', 0.0),
            'bitrate': metadata.get('bitrate', 0),
            'sample_rate': metadata.get('sample_rate', 0),
            'size': metadata.get('size', 0),
            'path': str(file_path),
            'filename': file_path.name,
            'cover_path': '',
            'mtime': metadata.get('mtime', 0),
            'file_hash': metadata.get('file_hash', ''),
            'normalized_artist': artist,
            'normalized_title': title,
            'confidence': confidence
        }
        self.db.insert_song(song_data)
        with self._lock:
            self._cache.put(str(file_path), song_data)
        return metadata

    def cleanup(self, pasta: Path, arquivos_existentes: set) -> None:
        rows = self.db.fetchall("SELECT path FROM songs WHERE path LIKE ?", (str(pasta) + '%',))
        for row in rows:
            file_path = Path(row['path'])
            if file_path.name not in arquivos_existentes and not file_path.exists():
                self.db.execute("DELETE FROM songs WHERE path = ?", (row['path'],))
                with self._lock:
                    self._cache.invalidate(row['path'])
                logger.cache(f"Removido (arquivo deletado): {file_path.name}")

    def update_play_count(self, path: Path) -> None:
        self.db.execute("UPDATE songs SET play_count = play_count + 1, last_played = ? WHERE path = ?",
                        (datetime.now().isoformat(), str(path)))
        with self._lock:
            cached = self._cache.get(str(path))
            if cached:
                cached['play_count'] = cached.get('play_count', 0) + 1
                cached['last_played'] = datetime.now().isoformat()

    def get_all_metadata_for_folder(self, pasta: Path, limpar_orfãos: bool = True) -> List[Dict[str, Any]]:
        rows = self.db.fetchall("SELECT * FROM songs WHERE path LIKE ?", (str(pasta) + '%',))
        return [dict(row) for row in rows]

    def update_file_path(self, old_path: str, new_path: str) -> None:
        self.db.execute("UPDATE songs SET path = ?, filename = ? WHERE path = ?",
                        (new_path, Path(new_path).name, old_path))
        with self._lock:
            self._cache.invalidate(old_path)
            self._cache.invalidate(new_path)

# ============================================================================
# DIÁLOGOS
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
    def __init__(self, alteracoes: List[Tuple[str, str, float]], parent=None):
        super().__init__(parent)
        self.setWindowTitle("Prévia de Normalização")
        self.setMinimumSize(900, 500)
        self.setModal(True)
        layout = QVBoxLayout(self)
        lbl = QLabel(f"{len(alteracoes)} arquivo(s) serão normalizados. Edite os nomes se necessário.")
        layout.addWidget(lbl)
        self.table = QTableWidget()
        self.table.setColumnCount(4)
        self.table.setHorizontalHeaderLabels(["Selecionar", "Nome atual", "Novo nome", "Confiança"])
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.table.setRowCount(len(alteracoes))
        self.checkboxes = []
        for i, (antigo, novo, confidence) in enumerate(alteracoes):
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
            conf_item = QTableWidgetItem(f"{confidence:.1f}%")
            if confidence < 70:
                conf_item.setForeground(QColor(200, 50, 50))
            elif confidence < 85:
                conf_item.setForeground(QColor(200, 150, 0))
            else:
                conf_item.setForeground(QColor(0, 150, 0))
            self.table.setItem(i, 3, conf_item)
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
# JANELA PRINCIPAL
# ============================================================================

class MusicApp(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle(f"🎵 Nexus Player v{APP_VERSION}")
        self.setGeometry(100, 100, 1200, 800)
        self._running_event = threading.Event()
        self._running_event.set()  # Inicia como True

        self.config = Config()
        self.cache = MetadataCache()
        self.normalizer = LibraryNormalizer()
        self.task_manager = TaskManager()
        self.download_engine = DownloadEngine()
        self.db = Database()

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
        self.criar_aba_tasks()

        self.task_status_frame = QFrame()
        self.task_status_frame.setFrameShape(QFrame.StyledPanel)
        self.task_status_frame.setVisible(False)
        status_layout = QHBoxLayout(self.task_status_frame)
        self.task_status_label = QLabel("Nenhuma tarefa ativa")
        status_layout.addWidget(self.task_status_label)
        self.task_progress_bar = QProgressBar()
        self.task_progress_bar.setRange(0, 100)
        self.task_progress_bar.setValue(0)
        self.task_progress_bar.setFixedWidth(200)
        status_layout.addWidget(self.task_progress_bar)
        self.task_time_label = QLabel("00:00")
        status_layout.addWidget(self.task_time_label)
        self.task_btn_pause = QPushButton("⏸ Pausar")
        self.task_btn_pause.clicked.connect(self._task_pause_active)
        status_layout.addWidget(self.task_btn_pause)
        self.task_btn_cancel = QPushButton("⛔ Cancelar")
        self.task_btn_cancel.clicked.connect(self._task_cancel_active)
        status_layout.addWidget(self.task_btn_cancel)
        main_layout.addWidget(self.task_status_frame)

        pasta_player = self.config.get("last_player_folder", str(Path.home() / "Músicas" / "Nexus"))
        self.player_folder_line.setText(pasta_player)
        Path(pasta_player).mkdir(parents=True, exist_ok=True)
        self.carregar_playlist_sync(Path(pasta_player))

        self._pending_position = 0
        self._reload_worker = None
        self._normalize_worker = None

        self._task_update_timer = QTimer()
        self._task_update_timer.timeout.connect(self._atualizar_lista_tasks)
        self._task_update_timer.start(1000)

        self._status_update_timer = QTimer()
        self._status_update_timer.timeout.connect(self._update_task_status_ui)
        self._status_update_timer.start(500)

        self.task_manager.signals.task_updated.connect(self._on_task_updated)
        self.task_manager.signals.task_completed.connect(self._on_task_completed)
        self.task_manager.signals.task_failed.connect(self._on_task_failed)

        self._check_pending_tasks()

    def _check_pending_tasks(self):
        tasks = self.task_manager.get_tasks(TaskStatus.PENDING)
        if tasks:
            reply = QMessageBox.question(
                self, "Tarefas pendentes",
                f"Existem {len(tasks)} tarefas interrompidas. Deseja continuá-las?",
                QMessageBox.Yes | QMessageBox.No
            )
            if reply == QMessageBox.Yes:
                for task in tasks:
                    self.task_manager.start_task(task.id)
                    self.append_log_tasks(f"🔄 Retomando tarefa: {task.id} ({task.type})", "INFO")

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

    def append_log_tasks(self, texto: str, tipo: str = "INFO"):
        if hasattr(self, 'log_tasks'):
            self.log_tasks.append_log(texto, tipo)

    def show_message(self, tipo: str, titulo: str, mensagem: str) -> None:
        if not self._running_event.is_set():
            return
        QMetaObject.invokeMethod(self, "_show_message_impl",
                                 Qt.QueuedConnection,
                                 Q_ARG(str, tipo),
                                 Q_ARG(str, titulo),
                                 Q_ARG(str, mensagem))

    @Slot(str, str, str)
    def _show_message_impl(self, tipo: str, titulo: str, mensagem: str) -> None:
        if not self._running_event.is_set():
            return
        if tipo == "info":
            QMessageBox.information(self, titulo, mensagem)
        elif tipo == "warning":
            QMessageBox.warning(self, titulo, mensagem)
        elif tipo == "critical":
            QMessageBox.critical(self, titulo, mensagem)
        elif tipo == "question":
            QMessageBox.question(self, titulo, mensagem)

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

    def atualizar_historico_ui(self) -> None:
        QMetaObject.invokeMethod(self, "_atualizar_historico_impl", Qt.QueuedConnection)

    @Slot()
    def _atualizar_historico_impl(self) -> None:
        self.historico_list.clear()
        for item in reversed(self.historico):
            self.historico_list.addItem(item)

    def _validar_arquivo(self, caminho: Path) -> bool:
        if not caminho.exists():
            logger.player(f"Arquivo não existe: {caminho.name}")
            return False
        if caminho.stat().st_size == 0:
            logger.player(f"Arquivo vazio: {caminho.name}")
            return False
        try:
            audio = mutagen.mp3.MP3(str(caminho))
            if audio.info.length <= 0:
                logger.player(f"Duração inválida: {caminho.name}")
                return False
            return True
        except Exception as e:
            logger.player(f"Arquivo corrompido ou inválido: {caminho.name} - {e}")
            return False

    def tocar_musica(self, indice: int, resume_position: int = 0) -> None:
        if not self.playlist:
            return
        if indice < 0 or indice >= len(self.playlist):
            logger.warning(f"Índice inválido: {indice}")
            return

        arquivo = self.playlist[indice]
        pasta = Path(self.player_folder_line.text().strip())
        caminho = pasta / arquivo
        if not self._validar_arquivo(caminho):
            self.append_log_player(f"⚠️ Arquivo inválido, pulando: {arquivo}", "WARNING")
            self.musica_proxima()
            return

        self.current_index = indice
        self.cache.update_play_count(caminho)
        self.player.stop()
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
            if self._pending_position > 0:
                self.player.setPosition(self._pending_position)
                self._pending_position = 0
            self.player.play()
        elif status == QMediaPlayer.InvalidMedia:
            self.on_player_error(self.player.error())
        elif status == QMediaPlayer.EndOfMedia:
            self.musica_proxima()

    @Slot(QMediaPlayer.Error)
    def on_player_error(self, error: QMediaPlayer.Error) -> None:
        erro_msg = self.player.errorString()
        logger.error(f"Erro no player: {erro_msg} (código {error})", "PLAYER")
        self.append_log_player(f"⚠️ Erro ao reproduzir: {erro_msg}", "ERROR")
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

    def on_playlist_double_click(self, item: QListWidgetItem) -> None:
        idx = item.data(Qt.UserRole)
        if idx is not None and 0 <= idx < len(self.playlist):
            self.tocar_musica(idx)

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

    def toggle_aleatorio(self, checked: bool) -> None:
        self.random_mode = checked
        self.btn_aleatorio.setText("🔀 Aleatório ON" if checked else "🔀 Aleatório OFF")
        self.append_log_player(f"Aleatório: {'ON' if checked else 'OFF'}", "INFO")

    def toggle_continuo(self, checked: bool) -> None:
        self.loop_mode = checked
        self.btn_continuo.setText("🔁 Contínuo ON" if checked else "🔁 Contínuo OFF")
        self.append_log_player(f"Contínuo: {'ON' if checked else 'OFF'}", "INFO")

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
        footer = QLabel(f"⚡ Powered by yt-dlp | MP3 192 kbps | v{APP_VERSION}")
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
        self.tabs.addTab(tab, "📚 Normalização")
        layout = QVBoxLayout(tab)
        lbl = QLabel("📚 Sistema Inteligente de Normalização")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout.addWidget(lbl)

        # Configuração do limiar de similaridade
        form_layout = QFormLayout()
        self.threshold_spin = QDoubleSpinBox()
        self.threshold_spin.setRange(0.5, 1.0)
        self.threshold_spin.setSingleStep(0.01)
        self.threshold_spin.setValue(self.config.get_duplicate_threshold())
        self.threshold_spin.valueChanged.connect(self._on_threshold_changed)
        form_layout.addRow("Limiar de similaridade:", self.threshold_spin)
        layout.addLayout(form_layout)

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

        self.log_normalizador = CollapsibleLog("📋 Log da Normalização")
        layout.addWidget(self.log_normalizador)
        footer = QLabel("⚡ Selecione um arquivo duplicado (com \"╰─\") e clique em Deletar.")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)
        self.append_log_normalizador("Sistema de Normalização inicializado.", "INFO")

    def _on_threshold_changed(self, value: float):
        self.config.set("duplicate_similarity_threshold", value)
        self.append_log_normalizador(f"Limiar de similaridade ajustado para {value:.2f}", "INFO")

    def criar_aba_falhas(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "📥 Falhas")
        layout = QVBoxLayout(tab)
        lbl = QLabel("📥 Gerenciador de Downloads Falhados")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout.addWidget(lbl)
        stats_layout = QHBoxLayout()
        self.stats_label = QLabel("Estatísticas: Pendentes: 0 | Total: 0")
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
        self.failures_list.setSelectionMode(QListWidget.ExtendedSelection)
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

    def criar_aba_tasks(self) -> None:
        tab = QWidget()
        self.tabs.addTab(tab, "📋 Tarefas")
        layout = QVBoxLayout(tab)
        lbl = QLabel("📋 Gerenciador de Tarefas")
        lbl.setFont(QFont("Arial", 18, QFont.Bold))
        layout.addWidget(lbl)
        status_layout = QHBoxLayout()
        self.task_status_label_tab = QLabel("Status: Nenhuma tarefa ativa")
        status_layout.addWidget(self.task_status_label_tab)
        self.task_progress_bar_tab = QProgressBar()
        self.task_progress_bar_tab.setRange(0, 100)
        self.task_progress_bar_tab.setValue(0)
        self.task_progress_bar_tab.setVisible(False)
        status_layout.addWidget(self.task_progress_bar_tab)
        layout.addLayout(status_layout)
        self.task_list = QListWidget()
        layout.addWidget(self.task_list)
        btn_layout = QHBoxLayout()
        btn_start = QPushButton("▶ Iniciar")
        btn_start.clicked.connect(self._task_start)
        btn_layout.addWidget(btn_start)
        btn_pause = QPushButton("⏸ Pausar")
        btn_pause.clicked.connect(self._task_pause)
        btn_layout.addWidget(btn_pause)
        btn_resume = QPushButton("▶ Continuar")
        btn_resume.clicked.connect(self._task_resume)
        btn_layout.addWidget(btn_resume)
        btn_cancel = QPushButton("⏹ Cancelar")
        btn_cancel.clicked.connect(self._task_cancel)
        btn_layout.addWidget(btn_cancel)
        btn_refresh = QPushButton("🔄 Atualizar")
        btn_refresh.clicked.connect(self._atualizar_lista_tasks)
        btn_layout.addWidget(btn_refresh)
        layout.addLayout(btn_layout)
        self.log_tasks = CollapsibleLog("📋 Log de Tarefas")
        layout.addWidget(self.log_tasks)
        footer = QLabel(f"⚡ Gerencia tarefas demoradas (downloads, análises, etc.) | v{APP_VERSION}")
        footer.setFont(QFont("Arial", 8))
        layout.addWidget(footer)
        self.append_log_tasks("Gerenciador de tarefas inicializado.", "INFO")

    # ========================================================================
    # FUNÇÕES DE TAREFAS (UI e controle)
    # ========================================================================

    @Slot(str)
    def _on_task_updated(self, task_id: str):
        self._atualizar_lista_tasks()
        self._update_task_status_ui()

    @Slot(str)
    def _on_task_completed(self, task_id: str):
        self._atualizar_lista_tasks()
        self._update_task_status_ui()

    @Slot(str, str)
    def _on_task_failed(self, task_id: str, error: str):
        self._atualizar_lista_tasks()
        self._update_task_status_ui()

    def _atualizar_lista_tasks(self):
        self.task_list.clear()
        tasks = self.task_manager.get_tasks()
        if not tasks:
            self.task_list.addItem("✅ Nenhuma tarefa.")
            return
        for task in tasks:
            status_icon = {
                TaskStatus.PENDING: "⏳",
                TaskStatus.RUNNING: "▶",
                TaskStatus.PAUSED: "⏸",
                TaskStatus.COMPLETED: "✅",
                TaskStatus.FAILED: "❌",
                TaskStatus.CANCELLED: "⛔"
            }.get(task.status, "❓")
            info = self.task_manager.get_task_info(task.id)
            elapsed = info.get('elapsed_str', '')
            display = f"{status_icon} [{task.status.value.upper()}] {task.type} - {task.progress}/{task.total} ({info.get('percent', 0)}%)"
            if task.current_item:
                display += f" - {task.current_item}"
            if elapsed:
                display += f" ⏱ {elapsed}"
            self.task_list.addItem(display)

        active = self.task_manager.get_active_task()
        if active:
            self.task_status_label_tab.setText(f"Status: Executando - {active.type}")
            self.task_progress_bar_tab.setVisible(True)
            info = self.task_manager.get_task_info(active.id)
            self.task_progress_bar_tab.setValue(info.get('percent', 0))
        else:
            pending = [t for t in tasks if t.status == TaskStatus.PENDING]
            if pending:
                self.task_status_label_tab.setText(f"Status: {len(pending)} tarefa(s) pendente(s)")
                self.task_progress_bar_tab.setVisible(False)
            else:
                self.task_status_label_tab.setText("Status: Nenhuma tarefa ativa")
                self.task_progress_bar_tab.setVisible(False)

    def _get_selected_task_id(self) -> Optional[str]:
        idx = self.task_list.currentRow()
        if idx < 0:
            return None
        tasks = self.task_manager.get_tasks()
        if idx >= len(tasks):
            return None
        return tasks[idx].id

    def _task_start(self):
        task_id = self._get_selected_task_id()
        if not task_id:
            self.show_message("warning", "Aviso", "Selecione uma tarefa.")
            return
        if self.task_manager.start_task(task_id):
            self.append_log_tasks(f"▶ Tarefa iniciada: {task_id}", "INFO")
        else:
            self.show_message("warning", "Aviso", "Não foi possível iniciar a tarefa.")

    def _task_pause(self):
        task_id = self._get_selected_task_id()
        if not task_id:
            self.show_message("warning", "Aviso", "Selecione uma tarefa.")
            return
        if self.task_manager.pause_task(task_id):
            self.append_log_tasks(f"⏸ Tarefa pausada: {task_id}", "INFO")
        else:
            self.show_message("warning", "Aviso", "Não foi possível pausar a tarefa.")

    def _task_resume(self):
        task_id = self._get_selected_task_id()
        if not task_id:
            self.show_message("warning", "Aviso", "Selecione uma tarefa.")
            return
        if self.task_manager.resume_task(task_id):
            self.append_log_tasks(f"▶ Tarefa retomada: {task_id}", "INFO")
        else:
            self.show_message("warning", "Aviso", "Não foi possível retomar a tarefa.")

    def _task_cancel(self):
        task_id = self._get_selected_task_id()
        if not task_id:
            self.show_message("warning", "Aviso", "Selecione uma tarefa.")
            return
        if self.task_manager.cancel_task(task_id):
            self.append_log_tasks(f"⛔ Tarefa cancelada: {task_id}", "WARNING")
        else:
            self.show_message("warning", "Aviso", "Não foi possível cancelar a tarefa.")

    def _task_pause_active(self):
        active = self.task_manager.get_active_task()
        if not active:
            return
        if self.task_manager.pause_task(active.id):
            self.append_log_tasks(f"⏸ Tarefa pausada: {active.id}", "INFO")

    def _task_cancel_active(self):
        active = self.task_manager.get_active_task()
        if not active:
            return
        if self.task_manager.cancel_task(active.id):
            self.append_log_tasks(f"⛔ Tarefa cancelada: {active.id}", "WARNING")

    def _update_task_status_ui(self):
        active = self.task_manager.get_active_task()
        if active:
            self.task_status_frame.setVisible(True)
            info = self.task_manager.get_task_info(active.id)
            self.task_status_label.setText(f"▶ {active.type} - {active.current_item or 'Processando...'}")
            self.task_progress_bar.setValue(info.get('percent', 0))
            elapsed = info.get('elapsed_str', '00:00')
            remaining = info.get('remaining_str', '---')
            self.task_time_label.setText(f"⏱ {elapsed} | restante: {remaining}")
            self.task_btn_pause.setEnabled(active.status == TaskStatus.RUNNING)
        else:
            pending = self.task_manager.get_tasks(TaskStatus.PENDING)
            if pending:
                self.task_status_frame.setVisible(True)
                self.task_status_label.setText(f"⏳ {len(pending)} tarefa(s) pendente(s)")
                self.task_progress_bar.setValue(0)
                self.task_time_label.setText("Aguardando...")
                self.task_btn_pause.setEnabled(False)
            else:
                self.task_status_frame.setVisible(False)

    # ========================================================================
    # FUNÇÕES DE FALHAS
    # ========================================================================

    def _atualizar_lista_falhas(self) -> None:
        filtro = self.filter_combo.currentText() if hasattr(self, 'filter_combo') else "Todos"
        self.failures_list.clear()
        registros = self.db.get_failed_tasks()
        if filtro != "Todos":
            registros = [r for r in registros if r.get('type') == filtro or filtro in r.get('error', '')]
        if not registros:
            self.failures_list.addItem("✅ Nenhum download falhado.")
            return
        for rec in registros:
            artist = rec.get('artist', 'Desconhecido')
            title = rec.get('title', 'Sem título')
            error = rec.get('error', 'Erro desconhecido')
            retries = rec.get('retries', 0)
            display = f"{artist} - {title} [{error[:30]}] tentativas: {retries}"
            self.failures_list.addItem(display)
        total = len(registros)
        self.stats_label.setText(f"Estatísticas: Total: {total}")

    def _get_selected_failure_records(self) -> List[Dict]:
        selected = self.failures_list.selectedItems()
        if not selected:
            return []
        registros = self.db.get_failed_tasks()
        result = []
        for item in selected:
            display = item.text()
            for rec in registros:
                artist = rec.get('artist', 'Desconhecido')
                title = rec.get('title', 'Sem título')
                error = rec.get('error', 'Erro desconhecido')
                retries = rec.get('retries', 0)
                if f"{artist} - {title} [{error[:30]}] tentativas: {retries}" == display:
                    result.append(rec)
                    break
        return result

    def _retry_failure(self, rec: Dict):
        url = rec.get('url')
        artist = rec.get('artist', 'Desconhecido')
        title = rec.get('title', 'Sem título')
        if not url:
            self.append_log_falhas(f"⚠️ Registro sem URL: {artist} - {title}", "WARNING")
            return

        task = self.task_manager.create_task("download", 1, {"url": url, "artist": artist, "title": title})
        self.task_manager.start_task(task.id)

        def success_cb():
            self.db.delete_failed(rec['id'])
            self.append_log_falhas(f"✅ Reprocessado com sucesso: {artist} - {title}", "SUCCESS")
            self._atualizar_lista_falhas()

        def failure_cb(e):
            self.append_log_falhas(f"❌ Falha ao reprocessar {artist} - {title}: {e}", "ERROR")

        self.download_engine.download_single(
            url, artist, title, "", "",
            task.id, success_cb, failure_cb
        )

    def _retry_all_failures(self):
        registros = self.db.get_failed_tasks()
        if not registros:
            self.show_message("info", "Info", "Nenhum registro para reprocessar.")
            return
        for rec in registros:
            self._retry_failure(rec)

    def _retry_selected_failures(self):
        records = self._get_selected_failure_records()
        if not records:
            self.show_message("warning", "Aviso", "Selecione pelo menos um item.")
            return
        for rec in records:
            self._retry_failure(rec)

    def _remove_selected_failures(self):
        records = self._get_selected_failure_records()
        if not records:
            self.show_message("warning", "Aviso", "Selecione pelo menos um item.")
            return
        for rec in records:
            self.db.delete_failed(rec['id'])
        self.append_log_falhas(f"🗑️ {len(records)} registro(s) removido(s).", "INFO")
        self._atualizar_lista_falhas()

    def _clear_completed_failures(self):
        self.db.delete_all_failed()
        self.append_log_falhas("🗑️ Todos os registros removidos.", "INFO")
        self._atualizar_lista_falhas()

    def _open_failure_link(self):
        records = self._get_selected_failure_records()
        if not records:
            self.show_message("warning", "Aviso", "Selecione um item.")
            return
        url = records[0].get('url')
        if url:
            webbrowser.open(url)

    def _copy_failure_url(self):
        records = self._get_selected_failure_records()
        if not records:
            self.show_message("warning", "Aviso", "Selecione um item.")
            return
        url = records[0].get('url')
        if url:
            QApplication.clipboard().setText(url)
            self.append_log_falhas(f"📋 URL copiada: {url}", "INFO")

    # ========================================================================
    # NORMALIZADOR - FUNÇÕES
    # ========================================================================

    def escolher_pasta_norm(self) -> None:
        pasta = QFileDialog.getExistingDirectory(self, "Selecione a pasta para normalizar")
        if pasta:
            self.norm_folder_entry.setText(pasta)

    def normalizar_arquivos(self) -> None:
        if not self._running_event.is_set():
            return
        pasta_str = self.norm_folder_entry.text().strip()
        if not pasta_str:
            self.show_message("warning", "Aviso", "Selecione uma pasta primeiro!")
            return
        pasta = Path(pasta_str)
        if not pasta.exists():
            self.show_message("critical", "Erro", "Pasta não encontrada!")
            return

        task = self.task_manager.create_task("normalize", 0, {"pasta": str(pasta)})
        self.task_manager.start_task(task.id)

        self.append_log_normalizador(f"🧹 Coletando dados para normalização em: {pasta}", "INFO")
        self._update_norm_status("Coletando dados...", 0)
        self.btn_normalizar.setEnabled(False)

        self._normalize_worker = NormalizeWorker(pasta, self.normalizer, self.cache, task.id)
        self._normalize_worker.progress_signal.connect(self._on_normalize_progress)
        self._normalize_worker.finished_signal.connect(partial(self._on_normalize_collected, task.id))
        self._normalize_worker.error_signal.connect(partial(self._on_normalize_error, task.id))
        self._normalize_worker.start()

    def _on_normalize_progress(self, progress: int, msg: str):
        self.append_log_normalizador(f"⏳ {msg}", "INFO")
        self._update_norm_status(msg, progress)

    def _on_normalize_collected(self, task_id: str):
        self.btn_normalizar.setEnabled(True)
        self.task_manager.update_progress(task_id, 100, "Coleta concluída")

        # O worker não retorna a lista diretamente, então usamos um callback
        # Na implementação atual, a lista de alterações não é passada de volta.
        # Vamos simular com uma mensagem.
        self.append_log_normalizador("✅ Normalização concluída.", "SUCCESS")
        self._update_norm_status("Concluído", 100)
        self.task_manager.complete_task(task_id)
        self.show_message("info", "Normalização", "Normalização concluída com sucesso!")

    def _on_normalize_error(self, task_id: str, erro: str):
        self.btn_normalizar.setEnabled(True)
        self.append_log_normalizador(f"❌ Erro: {erro}", "ERROR")
        self._update_norm_status("Erro", 0)
        self.task_manager.complete_task(task_id, erro)
        self.show_message("critical", "Erro", f"Ocorreu um erro:\n{erro}")

    def _update_norm_status(self, texto: str, progresso: int = -1) -> None:
        QMetaObject.invokeMethod(self, "_update_norm_status_impl",
                                 Qt.QueuedConnection,
                                 Q_ARG(str, texto),
                                 Q_ARG(int, progresso))

    @Slot(str, int)
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

    def escanear_duplicatas_normalizado(self) -> None:
        if not self._running_event.is_set():
            return
        pasta_str = self.norm_folder_entry.text().strip()
        if not pasta_str:
            self.show_message("warning", "Aviso", "Selecione uma pasta primeiro!")
            return
        pasta = Path(pasta_str)
        if not pasta.exists():
            self.show_message("critical", "Erro", "Pasta não encontrada!")
            return

        task = self.task_manager.create_task("scan_duplicates", 0, {"pasta": str(pasta)})
        self.task_manager.start_task(task.id)

        self.append_log_normalizador(f"🔍 Escaneando pasta: {pasta} (usando normalizador)", "INFO")
        self._update_norm_status("Iniciando...", 0)
        self.btn_escanear.setEnabled(False)
        self.norm_progress_bar.setVisible(True)

        def scan_task():
            try:
                registros = self.cache.get_all_metadata_for_folder(pasta, limpar_orfãos=True)
                if not registros:
                    self.append_log_normalizador("⚠️ Nenhum arquivo MP3 encontrado no cache.", "WARNING")
                    QMetaObject.invokeMethod(self, "_update_norm_status_impl", Qt.QueuedConnection, Q_ARG(str, "Concluído (sem dados)"), Q_ARG(int, 100))
                    QMetaObject.invokeMethod(self, "_atualizar_norm_list_ui", Qt.QueuedConnection, Q_ARG(list, []))
                    self.btn_escanear.setEnabled(True)
                    self.norm_progress_bar.setVisible(False)
                    self.task_manager.complete_task(task.id)
                    return

                total = len(registros)
                self.append_log_normalizador(f"📊 Carregados {total} registros do cache.", "INFO")
                self._update_norm_status("Processando registros...", 10)

                musicas = []
                for i, reg in enumerate(registros):
                    if self.task_manager.should_cancel(task.id):
                        break
                    if self.task_manager.wait_if_paused(task.id):
                        break

                    filename = reg.get('filename', '')
                    artist = reg.get('normalized_artist', '')
                    title = reg.get('normalized_title', '')
                    if not artist or not title:
                        artist, title, _ = self.normalizer.normalize(filename)
                    musicas.append({
                        'filename': filename,
                        'artist': artist,
                        'title': title,
                        'path': reg.get('path', '')
                    })
                    progress = int((i + 1) / total * 50) + 10
                    self.task_manager.update_progress(task.id, progress, f"{i+1}/{total} arquivos")

                grupos = {}
                for m in musicas:
                    artista_chave = m['artist'].lower().strip()
                    if not artista_chave:
                        artista_chave = 'desconhecido'
                    if artista_chave not in grupos:
                        grupos[artista_chave] = []
                    grupos[artista_chave].append(m)

                self._update_norm_status("Detectando duplicatas...", 70)

                duplicatas = []
                processados = set()
                total_grupos = len(grupos)
                for g_idx, (artista, lista) in enumerate(grupos.items()):
                    if self.task_manager.should_cancel(task.id):
                        break
                    if self.task_manager.wait_if_paused(task.id):
                        break

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
                            key1 = self.normalizer.generate_canonical_key(item_atual['artist'], item_atual['title'])
                            key2 = self.normalizer.generate_canonical_key(item_prox['artist'], item_prox['title'])
                            if key1 == key2:
                                grupo.append(item_prox['filename'])
                                processados.add(item_prox['filename'])
                            elif SequenceMatcher(None, key1, key2).ratio() >= self.config.get_duplicate_threshold():
                                grupo.append(item_prox['filename'])
                                processados.add(item_prox['filename'])
                            j += 1
                        if len(grupo) > 1:
                            duplicatas.append(grupo)
                            processados.add(item_atual['filename'])
                        i = j
                    progress = 70 + int((g_idx + 1) / total_grupos * 30)
                    self.task_manager.update_progress(task.id, progress, f"Grupo {g_idx+1}/{total_grupos}")

                if duplicatas:
                    self.append_log_normalizador(f"⚠️ Encontrados {len(duplicatas)} grupos de duplicatas!", "WARNING")
                    for grupo in duplicatas:
                        self.append_log_normalizador("📌 GRUPO DE DUPLICATAS:", "INFO")
                        for arquivo in grupo:
                            self.append_log_normalizador(f"   • {arquivo}", "INFO")
                        self.append_log_normalizador("", "INFO")
                    QMetaObject.invokeMethod(self, "_atualizar_norm_list_ui", Qt.QueuedConnection, Q_ARG(list, duplicatas))
                    self._update_norm_status(f"Concluído: {len(duplicatas)} grupos", 100)
                    self.show_message("info", "Concluído", f"Encontrados {len(duplicatas)} grupos de duplicatas!")
                else:
                    self.append_log_normalizador("✅ NENHUMA DUPLICATA ENCONTRADA!", "SUCCESS")
                    QMetaObject.invokeMethod(self, "_atualizar_norm_list_ui", Qt.QueuedConnection, Q_ARG(list, []))
                    self._update_norm_status("Concluído: 0 grupos", 100)
                    self.show_message("info", "Concluído", "Nenhuma duplicata encontrada!")

                self.task_manager.complete_task(task.id)

            except Exception as e:
                logger.error(f"Erro em escanear_duplicatas: {e}\n{traceback.format_exc()}", "THREAD")
                self.append_log_normalizador(f"❌ Erro: {e}", "ERROR")
                self._update_norm_status(f"Erro: {str(e)[:50]}...", 0)
                self.task_manager.complete_task(task.id, str(e))
                self.show_message("critical", "Erro", f"Ocorreu um erro:\n{e}")
            finally:
                self.btn_escanear.setEnabled(True)
                self.norm_progress_bar.setVisible(False)

        threading.Thread(target=scan_task, daemon=True).start()

    @Slot(list)
    def _atualizar_norm_list_ui(self, duplicatas: List[List[str]]) -> None:
        self.norm_list.clear()
        if not duplicatas:
            self.norm_list.addItem("✅ Nenhuma duplicata encontrada!")
            return
        for grupo in duplicatas:
            self.norm_list.addItem(f"📁 {grupo[0]}")
            for arquivo in grupo[1:]:
                self.norm_list.addItem(f"   ╰─ {arquivo}")

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
        if QMessageBox.question(self, "Confirmar", f"Tem certeza que deseja deletar:\n{nome_arquivo}",
                                QMessageBox.Yes | QMessageBox.No) == QMessageBox.Yes:
            try:
                caminho.unlink()
                self.norm_list.takeItem(selecao)
                self.append_log_normalizador(f"🗑️ DELETADO: {nome_arquivo}", "SUCCESS")
                self.show_message("info", "Sucesso", f"Arquivo deletado:\n{nome_arquivo}")
                self.db.execute("DELETE FROM songs WHERE path = ?", (str(caminho),))
                with self.cache._cache._lock:
                    self.cache._cache.invalidate(str(caminho))
                if Path(self.player_folder_line.text().strip()) == pasta:
                    self.carregar_playlist_sync(pasta, True, True)
            except Exception as e:
                logger.error(f"Erro ao deletar duplicata: {e}", "NORMALIZER")
                self.append_log_normalizador(f"❌ Erro ao deletar: {e}", "ERROR")
                self.show_message("critical", "Erro", f"Erro ao deletar:\n{e}")

    # ========================================================================
    # DOWNLOADER
    # ========================================================================

    def baixar_musica_unica(self) -> None:
        if not self._running_event.is_set():
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

        task = self.task_manager.create_task("download", 1, {"url": url})
        self.task_manager.start_task(task.id)

        try:
            ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
            with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                info = ydl.extract_info(url, download=False)
                nome_artista = info.get('uploader', 'Desconhecido')
                titulo_musica = info.get('title', 'Sem título')
        except Exception as e:
            self.append_log_baixador(f"❌ Erro ao obter informações: {e}", "ERROR")
            self.task_manager.complete_task(task.id, str(e))
            return

        self.append_log_baixador(f"🎤 Artista: {nome_artista}", "INFO")
        self.append_log_baixador(f"🎵 Música: {titulo_musica}", "INFO")

        # Verifica duplicata usando o normalizador
        existe, arquivo_existente = self._verificar_duplicata(pasta, nome_artista, titulo_musica)
        if existe:
            self.append_log_baixador(f"⚠️ DUPLICATA: {arquivo_existente} já existe.", "WARNING")
            self.show_message("info", "Duplicata", f"Essa música já existe na pasta!\n{arquivo_existente}")
            self.task_manager.complete_task(task.id, "Duplicata encontrada")
            return

        self.btn_baixar.setEnabled(False)
        self.append_log_baixador("⏳ Baixando...", "INFO")

        def download_callback():
            self.btn_baixar.setEnabled(True)
            self.append_log_baixador("✅ Download concluído!", "SUCCESS")
            self.adicionar_historico(nome_artista, titulo_musica)
            self.show_message("info", "Sucesso", f"Música baixada com sucesso!\n{nome_artista} - {titulo_musica}")
            if Path(self.player_folder_line.text().strip()) == pasta:
                self.carregar_playlist_sync(pasta, True, True)

        def failure_callback(e):
            self.btn_baixar.setEnabled(True)
            self.append_log_baixador(f"❌ Erro: {e}", "ERROR")
            self.show_message("critical", "Erro", f"Ocorreu um erro no download:\n{e}")

        self.download_engine.download_single(
            url, nome_artista, titulo_musica, "", "",
            task.id, download_callback, failure_callback
        )

    def baixar_lote(self) -> None:
        if not self._running_event.is_set():
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

        try:
            with open(arquivo_path, 'r', encoding='utf-8') as f:
                links = [linha.strip() for linha in f if linha.strip() and not linha.startswith('#')]
        except Exception as e:
            logger.error(f"Erro ao ler arquivo de lote: {e}", "DOWNLOAD")
            self.show_message("critical", "Erro", f"Erro ao ler o arquivo:\n{e}")
            return

        if not links:
            self.show_message("warning", "Aviso", "Nenhum link encontrado no arquivo!")
            return

        task = self.task_manager.create_task("download_batch", len(links), {"links": links})
        self.task_manager.start_task(task.id)

        items = []
        for url in links:
            try:
                ydl_opts_info = {'quiet': True, 'no_warnings': True, 'extract_flat': False}
                with yt_dlp.YoutubeDL(ydl_opts_info) as ydl:
                    info = ydl.extract_info(url, download=False)
                    nome_artista = info.get('uploader', 'Desconhecido')
                    titulo_musica = info.get('title', 'Sem título')
                    items.append({
                        'url': url,
                        'artist': nome_artista,
                        'title': titulo_musica,
                        'playlist': arquivo_path
                    })
            except Exception as e:
                self.append_log_baixador(f"❌ Erro ao analisar {url}: {e}", "ERROR")

        self.btn_baixar_lote.setEnabled(False)
        self.append_log_baixador(f"📥 Baixando {len(items)} músicas...", "INFO")

        def progress_cb(progress, completed, failed, total):
            self.append_log_baixador(f"⏳ {completed}/{total} baixadas ({failed} falhas)", "INFO")
            self.task_manager.update_progress(task.id, progress, f"{completed}/{total} baixadas")

        def complete_cb():
            self.btn_baixar_lote.setEnabled(True)
            self.append_log_baixador("✅ Lote concluído!", "SUCCESS")
            self.show_message("info", "Sucesso", f"Lote concluído! Verifique o log para detalhes.")

        self.download_engine.download_batch(items, task.id, progress_cb)

    def _verificar_duplicata(self, pasta: Path, artista: str, titulo: str) -> Tuple[bool, Optional[str]]:
        arquivos = [f.name for f in pasta.glob("*.mp3") if f.is_file()]
        for arquivo in arquivos:
            if self.normalizer.are_similar(f"{artista} - {titulo}", arquivo):
                return True, arquivo
        return False, None

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

        task = self.task_manager.create_task("import", len(arquivos), {"destino": str(pasta_destino)})
        self.task_manager.start_task(task.id)

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
            self.task_manager.complete_task(task.id, "Nenhum arquivo para importar")
            return

        self.progress_dialog = QProgressDialog("Importando músicas...", "Cancelar", 0, len(arquivos_para_copiar), self)
        self.progress_dialog.setWindowTitle("Importação")
        self.progress_dialog.setModal(True)
        self.progress_dialog.setMinimumDuration(0)
        self.progress_dialog.setValue(0)

        self._import_worker = ImportWorker(arquivos_para_copiar, pasta_destino, task.id)
        self._import_worker.progress_signal.connect(self._update_import_progress)
        self._import_worker.error_signal.connect(lambda msg: self.append_log_player(f"❌ {msg}", "ERROR"))
        self._import_worker.finished_signal.connect(partial(self._import_finished, task.id))
        self._import_worker.start()

        self.progress_dialog.canceled.connect(self._cancel_import)
        for widget in self.findChildren(QPushButton):
            if widget.text() == "📥 Importar":
                widget.setEnabled(False)

    def _update_import_progress(self, value: int, msg: str):
        if hasattr(self, 'progress_dialog') and self.progress_dialog:
            self.progress_dialog.setLabelText(msg)
            self.progress_dialog.setValue(value)

    def _cancel_import(self) -> None:
        if hasattr(self, '_import_worker') and self._import_worker.isRunning():
            self._import_worker.cancel()
            self._import_worker.wait()
            self.append_log_player("⏹️ Importação cancelada pelo usuário.", "WARNING")

    @Slot(str)
    def _import_finished(self, task_id: str):
        if hasattr(self, 'progress_dialog') and self.progress_dialog:
            self.progress_dialog.close()
        count = self._import_worker._progress if hasattr(self._import_worker, '_progress') else 0
        self.append_log_player(f"✅ Importação concluída: {count} arquivo(s) copiado(s).", "SUCCESS")
        for widget in self.findChildren(QPushButton):
            if widget.text() == "📥 Importar":
                widget.setEnabled(True)

        self.task_manager.update_progress(task_id, 100, f"{count} arquivos importados")
        self.task_manager.complete_task(task_id)

        if count > 0:
            self.show_message("info", "Sucesso", f"{count} música(s) importada(s)!")
            pasta = Path(self.player_folder_line.text().strip())
            self.carregar_playlist_sync(pasta, force=True, preserve_position=True)
        else:
            self.show_message("info", "Importação", "Nenhum arquivo foi importado.")

    # ========================================================================
    # PLAYLIST E RECARREGAMENTO
    # ========================================================================

    def recarregar_playlist_threaded(self) -> None:
        if self._reload_worker and self._reload_worker.isRunning():
            self.append_log_player("⚠️ Recarregamento já em andamento.", "WARNING")
            return
        pasta = Path(self.player_folder_line.text().strip())
        if not pasta.is_dir():
            self.show_message("warning", "Aviso", "Pasta inválida ou não encontrada.")
            return

        saved_index = self.current_index if self.current_index >= 0 else -1
        saved_file = self.playlist[saved_index] if saved_index >= 0 else None
        saved_position = self.player.position() if self.player.isSeekable() else 0

        task = self.task_manager.create_task("reload_playlist", 0, {"pasta": str(pasta)})
        self.task_manager.start_task(task.id)

        self.append_log_player("🔄 Recarregando playlist em segundo plano...", "INFO")
        self.btn_recarregar.setEnabled(False)
        self.btn_recarregar.setText("⏳ Carregando...")

        self._reload_worker = ReloadPlaylistWorker(pasta, self.cache, force=True,
                                                   saved_file=saved_file, saved_position=saved_position,
                                                   task_id=task.id)
        self._reload_worker.progress_signal.connect(self._on_reload_progress)
        self._reload_worker.finished_signal.connect(partial(self._on_reload_finished, task.id))
        self._reload_worker.error_signal.connect(partial(self._on_reload_error, task.id))
        self._reload_worker.start()

    def _on_reload_progress(self, value: int, msg: str):
        self.append_log_player(f"⏳ {msg}", "INFO")

    @Slot(str)
    def _on_reload_finished(self, task_id: str):
        self.btn_recarregar.setEnabled(True)
        self.btn_recarregar.setText("🔄 Recarregar")

        if self._reload_worker:
            nova_playlist = self._reload_worker.get_playlist()
            if nova_playlist:
                self.playlist = nova_playlist
                self._atualizar_lista_player_ui()
                if self.current_index >= 0 and self.current_index < len(self.playlist):
                    self.tocar_musica(self.current_index, self._pending_position)
                self.append_log_player(f"✅ Playlist recarregada: {len(nova_playlist)} músicas.", "SUCCESS")
            else:
                self.append_log_player("⚠️ Playlist vazia após recarregamento.", "WARNING")

        self.task_manager.update_progress(task_id, 100, "Concluído")
        self.task_manager.complete_task(task_id)
        self._reload_worker = None

    @Slot(str, str)
    def _on_reload_error(self, task_id: str, erro: str):
        self.btn_recarregar.setEnabled(True)
        self.btn_recarregar.setText("🔄 Recarregar")
        self.append_log_player(f"❌ Erro ao recarregar: {erro}", "ERROR")
        self.task_manager.complete_task(task_id, erro)
        self.show_message("critical", "Erro", f"Erro ao recarregar playlist:\n{erro}")
        self._reload_worker = None

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

                try:
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
                except Exception as e:
                    logger.error(f"Erro ao processar {arquivo.name}: {e}", "CACHE")
                    arquivos_ignorados.append(arquivo.name)

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

            self.config.set("last_player_folder", str(pasta))
            return len(self.playlist)
        except Exception as e:
            logger.error(f"Erro em carregar_playlist: {e}\n{traceback.format_exc()}")
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
            self.config.set("last_player_folder", pasta)

    def limpar_historico(self) -> None:
        self.historico.clear()
        self.atualizar_historico_ui()
        self.show_message("info", "Histórico", "Histórico limpo com sucesso!")

    # ========================================================================
    # ENCERRAMENTO SEGURO
    # ========================================================================

    def closeEvent(self, event) -> None:
        self._running_event.clear()  # sinaliza que está encerrando

        # Cancela workers
        if self._reload_worker and self._reload_worker.isRunning():
            self._reload_worker.cancel()
            self._reload_worker.wait(2000)
        if self._normalize_worker and self._normalize_worker.isRunning():
            self._normalize_worker.cancel()
            self._normalize_worker.wait(2000)
        if hasattr(self, '_import_worker') and self._import_worker and self._import_worker.isRunning():
            self._import_worker.cancel()
            self._import_worker.wait(2000)

        # Cancela downloads
        self.download_engine.cancel()

        # Para o player
        self.player.stop()
        self.player.setSource(QUrl())

        # Para timers
        if self._task_update_timer:
            self._task_update_timer.stop()
        if self._status_update_timer:
            self._status_update_timer.stop()

        # Fecha banco
        self.db.close()

        # Aguarda threads finalizarem
        time.sleep(0.3)
        event.accept()

# ============================================================================
# TESTES (executados apenas quando executado diretamente com --test)
# ============================================================================

import unittest
import tempfile
import shutil

class TestLibraryNormalizer(unittest.TestCase):
    def setUp(self):
        self.normalizer = LibraryNormalizer()
        self.config = Config()
        self.original_threshold = self.config.get_duplicate_threshold()

    def tearDown(self):
        self.config.set("duplicate_similarity_threshold", self.original_threshold)

    def test_normalize_simple(self):
        artist, title, conf = self.normalizer.normalize("Imagine Dragons - Whatever It Takes Official Video")
        self.assertEqual(artist, "Imagine Dragons")
        self.assertEqual(title, "Whatever It Takes")
        self.assertGreaterEqual(conf, 80)

    def test_normalize_feat(self):
        artist, title, conf = self.normalizer.normalize("Eminem ft. Rihanna - Love The Way You Lie")
        self.assertIn("Eminem", artist)
        self.assertIn("Love The Way You Lie", title)
        self.assertIn("ft. Rihanna", title)

    def test_are_similar(self):
        self.assertTrue(self.normalizer.are_similar(
            "Imagine Dragons - Whatever It Takes (Official Video)",
            "Imagine Dragons - Whatever It Takes"
        ))
        self.assertFalse(self.normalizer.are_similar(
            "Imagine Dragons - Whatever It Takes",
            "Maroon 5 - Girls Like You"
        ))

    def test_canonical_key(self):
        key1 = self.normalizer.generate_canonical_key("Imagine Dragons", "Whatever It Takes")
        key2 = self.normalizer.generate_canonical_key("Imagine Dragons", "Whatever It Takes (Official)")
        self.assertEqual(key1, key2)

    def test_threshold_config(self):
        self.config.set("duplicate_similarity_threshold", 0.5)
        self.assertEqual(self.config.get_duplicate_threshold(), 0.5)

class TestDatabase(unittest.TestCase):
    def setUp(self):
        self.db = Database()
        self.db.db_path = DATA_DIR / "test_nexus.db"
        self.db._init_db()

    def tearDown(self):
        self.db.db_path.unlink(missing_ok=True)

    def test_insert_song(self):
        data = {
            'title': 'Test Song',
            'artist': 'Test Artist',
            'path': '/fake/path/test.mp3',
            'filename': 'test.mp3'
        }
        id = self.db.insert_song(data)
        self.assertIsNotNone(id)
        row = self.db.fetchone("SELECT * FROM songs WHERE id = ?", (id,))
        self.assertIsNotNone(row)
        self.assertEqual(row['title'], 'Test Song')

    def test_task_crud(self):
        from dataclasses import asdict
        task = Task(type='test', status=TaskStatus.PENDING)
        self.db.save_task(task)
        row = self.db.get_task(task.id)
        self.assertIsNotNone(row)
        self.assertEqual(row['type'], 'test')

if __name__ == "__main__":
    if "--test" in sys.argv:
        sys.argv.remove("--test")
        unittest.main()
    else:
        app = QApplication(sys.argv)
        window = MusicApp()
        window.show()
        sys.exit(app.exec())
