from __future__ import annotations

import io
import json
import math
import shutil
import subprocess
import threading
import time
import tkinter as tk
from tkinter import colorchooser, filedialog, messagebox, ttk
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile

import numpy as np
import sounddevice as sd
import soundfile as sf

APP_NAME = "Vizualizator Python"
APP_VERSION = 1
SAMPLE_RATE = 44_100
CHANNELS = 1
MIN_POINT_DISTANCE = 5.0

COLORS = [
    "#171717", "#e53935", "#fb8c00", "#fdd835",
    "#43a047", "#00acc1", "#1e88e5", "#5e35b1",
    "#d81b60", "#ffffff",
]
WIDTHS = [2, 4, 6, 9, 13, 18]


class DrawAudioApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Vizualizator Python")
        self.root.geometry("1180x820")
        self.root.minsize(850, 620)

        # рисование
        self.strokes: list[dict] = []
        self.history: list[dict] = []
        self.next_line_id = 1
        self.canvas_base_width = 1000
        self.canvas_base_height = 450
        self.active_stroke: dict | None = None
        self.last_mouse_point: tuple[float, float] | None = None
        self.current_color = COLORS[0]
        self.current_width = 4
        self.tool = "draw"
        self.project_path: str | None = None
        self.loaded_project = False

        # синзронизация времени и записи
        self.recording = False
        self.input_stream: sd.InputStream | None = None
        self.record_wall_start: float | None = None
        self.timeline_origin: float | None = None
        self.session_elapsed = 0.0
        self.audio_trim_offset = 0.0
        self.audio_chunks: list[np.ndarray] = []
        self.audio_lock = threading.Lock()
        self.audio_data = np.zeros(0, dtype=np.float32)
        self.audio_sample_rate = SAMPLE_RATE
        self.audio_duration = 0.0

        # проигрыватель
        self.is_playing = False
        self.playback_started_at = 0.0
        self.playhead = 0.0
        self.total_duration = 0.0
        self._playback_after_id: str | None = None

        self.format_var = tk.StringVar(value="ogg")
        self.status_var = tk.StringVar(value="Нажмите «Новая запись», затем рисуйте и комментируйте рисунок.")
        self.time_var = tk.StringVar(value="00:00 / 00:00")

        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(100, self._update_canvas_dimensions)



    def _build_ui(self) -> None:
        outer = ttk.Frame(self.root, padding=(10, 8))
        outer.pack(fill="both", expand=True)

        controls = ttk.Frame(outer)
        controls.pack(fill="x", pady=(0, 7))

        self.record_button = ttk.Button(controls, text="● Новая запись", command=self.toggle_recording)
        self.record_button.pack(side="left", padx=(0, 6))
        ttk.Button(controls, text="Открыть ZIP", command=self.open_project).pack(side="left", padx=3)
        ttk.Button(controls, text="Сохранить ZIP", command=self.save_project).pack(side="left", padx=3)
        ttk.Button(controls, text="Экспорт JSON", command=self.export_json).pack(side="left", padx=3)

        ttk.Label(controls, text="Аудио:").pack(side="left", padx=(18, 4))
        format_box = ttk.Combobox(
            controls, textvariable=self.format_var, values=("mp3", "ogg"),
            state="readonly", width=6
        )
        format_box.pack(side="left")

        ttk.Separator(outer, orient="horizontal").pack(fill="x", pady=5)

        palette = ttk.Frame(outer)
        palette.pack(fill="x", pady=(0, 8))

        ttk.Label(palette, text="Инструмент:").pack(side="left", padx=(0, 5))
        self.tool_buttons: dict[str, ttk.Button] = {}
        for key, label in (("draw", "Кисть"), ("point", "Удалить точку"), ("line", "Удалить линию")):
            button = ttk.Button(palette, text=label, command=lambda k=key: self.set_tool(k))
            button.pack(side="left", padx=2)
            self.tool_buttons[key] = button

        ttk.Separator(palette, orient="vertical").pack(side="left", fill="y", padx=10)
        ttk.Label(palette, text="Цвет:").pack(side="left", padx=(0, 4))
        self.color_buttons: list[tk.Button] = []
        for color in COLORS:
            btn = tk.Button(
                palette, bg=color, activebackground=color, width=2, height=1,
                relief="solid", bd=1, command=lambda c=color: self.set_color(c)
            )
            btn.pack(side="left", padx=2)
            self.color_buttons.append(btn)
        tk.Button(palette, text="＋", width=2, command=self.choose_custom_color).pack(side="left", padx=2)

        ttk.Separator(palette, orient="vertical").pack(side="left", fill="y", padx=10)
        ttk.Label(palette, text="Толщина:").pack(side="left", padx=(0, 4))
        self.width_buttons: list[tk.Button] = []
        for width in WIDTHS:
            btn = tk.Button(
                palette, text=str(width), width=3,
                command=lambda w=width: self.set_width(w)
            )
            btn.pack(side="left", padx=2)
            self.width_buttons.append(btn)

        self._refresh_tool_palette()

        drawing_frame = ttk.LabelFrame(outer, text="Область рисования", padding=3)
        drawing_frame.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(drawing_frame, bg="white", highlightthickness=1, highlightbackground="#c8c8c8")
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<ButtonPress-1>", self.on_mouse_down)
        self.canvas.bind("<B1-Motion>", self.on_mouse_move)
        self.canvas.bind("<ButtonRelease-1>", self.on_mouse_up)
        self.canvas.bind("<Configure>", lambda _event: self.redraw_canvas())

        audio_frame = ttk.LabelFrame(outer, text="Аудиодорожка и воспроизведение", padding=5)
        audio_frame.pack(fill="x", pady=(8, 0))
        self.wave_canvas = tk.Canvas(audio_frame, height=118, bg="#fbfbfd", highlightthickness=1, highlightbackground="#dedee5")
        self.wave_canvas.pack(fill="x", expand=True)
        self.wave_canvas.bind("<Configure>", lambda _event: self.draw_waveform())

        playback_controls = ttk.Frame(audio_frame)
        playback_controls.pack(fill="x", pady=(5, 0))
        self.play_button = ttk.Button(playback_controls, text="▶ Воспроизвести", command=self.toggle_playback)
        self.play_button.pack(side="left")
        ttk.Button(playback_controls, text="⏮ С начала", command=self.restart_playback).pack(side="left", padx=5)
        ttk.Label(playback_controls, textvariable=self.time_var).pack(side="right")


    def _refresh_tool_palette(self) -> None:
        for key, button in self.tool_buttons.items():
            button.configure(style="SelectedTool.TButton" if key == self.tool else "TButton")
        for i, btn in enumerate(self.color_buttons):
            btn.configure(relief="sunken" if COLORS[i] == self.current_color else "solid", bd=2 if COLORS[i] == self.current_color else 1)
        for i, btn in enumerate(self.width_buttons):
            btn.configure(relief="sunken" if WIDTHS[i] == self.current_width else "raised")

    def _update_canvas_dimensions(self) -> None:
        if not self.strokes:
            self.canvas_base_width = max(1, self.canvas.winfo_width())
            self.canvas_base_height = max(1, self.canvas.winfo_height())

    def set_tool(self, tool: str) -> None:
        self.tool = tool
        self._refresh_tool_palette()
        labels = {"draw": "Кисть выбрана.", "point": "Кликните рядом с точкой, чтобы удалить её.", "line": "Кликните по линии, чтобы удалить её целиком."}
        self.status_var.set(labels[tool])

    def set_color(self, color: str) -> None:
        self.current_color = color
        self._refresh_tool_palette()

    def choose_custom_color(self) -> None:
        selected = colorchooser.askcolor(color=self.current_color, title="Выберите цвет линии")
        if selected and selected[1]:
            self.current_color = selected[1]
            self._refresh_tool_palette()

    def set_width(self, width: int) -> None:
        self.current_width = width
        self._refresh_tool_palette()



    # запись
    def toggle_recording(self) -> None:
        if self.recording:
            self.stop_recording()
        else:
            self.start_recording()

    def start_recording(self) -> None:
        if self.is_playing:
            self.pause_playback()
        if self.recording:
            return
        self._clear_document()
        self.audio_data = np.zeros(0, dtype=np.float32)
        self.audio_duration = 0.0
        self.audio_sample_rate = SAMPLE_RATE
        self.audio_chunks = []
        self.record_wall_start = time.perf_counter()
        self.timeline_origin = None
        self.session_elapsed = 0.0
        self.audio_trim_offset = 0.0
        self.loaded_project = False
        try:
            self.input_stream = sd.InputStream(
                samplerate=SAMPLE_RATE,
                channels=CHANNELS,
                dtype="float32",
                blocksize=1024,
                callback=self._audio_callback,
            )
            self.input_stream.start()
        except Exception as exc:
            self.input_stream = None
            self.record_wall_start = None
            messagebox.showerror(
                "Не удалось включить микрофон",
                "Проверьте подключение микрофона и разрешение Windows на доступ к нему.\n\n"
                f"Подробности: {exc}"
            )
            self.status_var.set("Запись не началась: микрофон недоступен.")
            return

        self.recording = True
        self.record_button.configure(text="■ Остановить запись")
        self.status_var.set("Идёт запись микрофона. Первый штрих станет нулевой точкой времени.")
        self.play_button.configure(state="disabled")

    def _audio_callback(self, indata: np.ndarray, frames: int, time_info, status) -> None:
        if status:
            pass
        with self.audio_lock:
            self.audio_chunks.append(indata[:, 0].copy())

    def stop_recording(self, silent: bool = False) -> None:
        if not self.recording:
            return
        end_time = time.perf_counter()
        if self.timeline_origin is not None:
            self.session_elapsed = max(0.0, end_time - self.timeline_origin)
        if self.input_stream is not None:
            try:
                self.input_stream.stop()
                self.input_stream.close()
            except Exception:
                pass
            self.input_stream = None
        with self.audio_lock:
            chunks = self.audio_chunks[:]
            self.audio_chunks.clear()
        if chunks:
            raw = np.concatenate(chunks).astype(np.float32, copy=False)
            if self.timeline_origin is not None and self.record_wall_start is not None:
                self.audio_trim_offset = max(0.0, self.timeline_origin - self.record_wall_start)
                first_frame = min(len(raw), int(round(self.audio_trim_offset * SAMPLE_RATE)))
                raw = raw[first_frame:]
            self.audio_data = raw
        else:
            self.audio_data = np.zeros(0, dtype=np.float32)
        self.audio_duration = len(self.audio_data) / float(self.audio_sample_rate)
        self.recording = False
        self.record_button.configure(text="● Новая запись")
        self.play_button.configure(state="normal")
        self.total_duration = max(self.audio_duration, self._last_drawing_time())
        self.playhead = 0.0
        self.draw_waveform()
        self.status_var.set(
            f"Запись остановлена. Аудио: {self._format_time(self.audio_duration)}. "
            f"Точек: {sum(len(s['points']) for s in self.strokes)}."
        )
        if not silent:
            self.root.update_idletasks()

    #рисование
    def on_mouse_down(self, event) -> None:
        x, y = float(event.x), float(event.y)
        if self.tool == "draw":
            if not self.recording:
                self.status_var.set("Чтобы рисовать и записывать голос, нажмите «Новая запись».")
                return
            now = time.perf_counter()
            if self.timeline_origin is None:
                self.timeline_origin = now
                point_time = 0.0
            else:
                point_time = max(0.0, now - self.timeline_origin)
            stroke = {"id": self.next_line_id, "points": []}
            self.next_line_id += 1
            self.strokes.append(stroke)
            self.active_stroke = stroke
            self.last_mouse_point = (x, y)
            self._append_point(stroke, x, y, point_time)
            self.redraw_canvas()
        elif self.tool == "point":
            self.delete_nearest_point(x, y)
        elif self.tool == "line":
            self.delete_nearest_line(x, y)

    def on_mouse_move(self, event) -> None:
        if self.tool != "draw" or self.active_stroke is None or not self.recording:
            return
        x, y = float(event.x), float(event.y)
        if self.last_mouse_point is None:
            self.last_mouse_point = (x, y)
            return
        distance = math.hypot(x - self.last_mouse_point[0], y - self.last_mouse_point[1])
        if distance >= MIN_POINT_DISTANCE:
            point_time = 0.0 if self.timeline_origin is None else max(0.0, time.perf_counter() - self.timeline_origin)
            self._append_point(self.active_stroke, x, y, point_time)
            self.last_mouse_point = (x, y)
            self.redraw_canvas()

    def on_mouse_up(self, event) -> None:
        if self.active_stroke is not None:
            x, y = float(event.x), float(event.y)
            if self.last_mouse_point is not None:
                distance = math.hypot(x - self.last_mouse_point[0], y - self.last_mouse_point[1])
                if distance >= MIN_POINT_DISTANCE:
                    point_time = 0.0 if self.timeline_origin is None else max(0.0, time.perf_counter() - self.timeline_origin)
                    self._append_point(self.active_stroke, x, y, point_time)
            self.active_stroke = None
            self.last_mouse_point = None
            self.redraw_canvas()

    def _append_point(self, stroke: dict, x: float, y: float, point_time: float) -> None:
        point_id = max((p["id"] for p in stroke["points"]), default=-1) + 1
        stroke["points"].append({
            "id": point_id,
            "x": round(x, 2),
            "y": round(y, 2),
            "t": round(float(point_time), 4),
            "width": int(self.current_width),
            "color": self.current_color,
        })

    def redraw_canvas(self, upto_time: float | None = None) -> None:
        if not hasattr(self, "canvas"):
            return
        self.canvas.delete("all")
        w = max(1, self.canvas.winfo_width())
        h = max(1, self.canvas.winfo_height())
        sx = w / max(1, self.canvas_base_width)
        sy = h / max(1, self.canvas_base_height)
        for stroke in self.strokes:
            visible = [p for p in stroke["points"] if upto_time is None or p["t"] <= upto_time]
            if not visible:
                continue
            first = visible[0]
            r = max(1.0, float(first["width"]) / 2.0)
            x0, y0 = first["x"] * sx, first["y"] * sy
            self.canvas.create_oval(x0-r, y0-r, x0+r, y0+r, fill=first["color"], outline=first["color"])
            for previous, current in zip(visible, visible[1:]):
                self.canvas.create_line(
                    previous["x"] * sx, previous["y"] * sy,
                    current["x"] * sx, current["y"] * sy,
                    fill=current["color"], width=current["width"],
                    capstyle=tk.ROUND, joinstyle=tk.ROUND,
                )

    def _canvas_scale(self) -> tuple[float, float]:
        return (
            self.canvas.winfo_width() / max(1, self.canvas_base_width),
            self.canvas.winfo_height() / max(1, self.canvas_base_height),
        )

    def delete_nearest_point(self, x: float, y: float) -> None:
        sx, sy = self._canvas_scale()
        best: tuple[float, dict, dict] | None = None
        for stroke in self.strokes:
            for point in stroke["points"]:
                px, py = point["x"] * sx, point["y"] * sy
                distance = math.hypot(px - x, py - y)
                if best is None or distance < best[0]:
                    best = (distance, stroke, point)
        if best is None or best[0] > 16:
            self.status_var.set("Рядом с курсором нет точки для удаления.")
            return
        _, stroke, point = best
        event_time = self.current_event_time()
        line_id, point_id = stroke["id"], point["id"]
        stroke["points"].remove(point)
        if not stroke["points"]:
            self.strokes.remove(stroke)
        self._log_history(event_time, "delete_point", line_id, point_id)
        self.redraw_canvas()
        self.status_var.set(f"Удалена точка {point_id} линии {line_id}.")

    def delete_nearest_line(self, x: float, y: float) -> None:
        sx, sy = self._canvas_scale()
        best: tuple[float, dict] | None = None
        for stroke in self.strokes:
            points = stroke["points"]
            if not points:
                continue
            if len(points) == 1:
                distance = math.hypot(points[0]["x"] * sx - x, points[0]["y"] * sy - y)
            else:
                distance = min(
                    self._point_segment_distance(
                        x, y,
                        a["x"] * sx, a["y"] * sy,
                        b["x"] * sx, b["y"] * sy,
                    )
                    for a, b in zip(points, points[1:])
                )
            if best is None or distance < best[0]:
                best = (distance, stroke)
        if best is None or best[0] > 18:
            self.status_var.set("Рядом с курсором нет линии для удаления.")
            return
        _, stroke = best
        line_id = stroke["id"]
        event_time = self.current_event_time()
        self.strokes.remove(stroke)
        self._log_history(event_time, "delete_line", line_id, None)
        self.redraw_canvas()
        self.status_var.set(f"Удалена линия {line_id}.")

    @staticmethod
    def _point_segment_distance(px: float, py: float, x1: float, y1: float, x2: float, y2: float) -> float:
        dx, dy = x2 - x1, y2 - y1
        if dx == 0 and dy == 0:
            return math.hypot(px - x1, py - y1)
        u = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / (dx * dx + dy * dy)))
        return math.hypot(px - (x1 + u * dx), py - (y1 + u * dy))

    def current_event_time(self) -> float:
        if self.recording and self.timeline_origin is not None:
            return max(0.0, time.perf_counter() - self.timeline_origin)
        if self.loaded_project:
            return self.playhead
        return self.session_elapsed

    def _log_history(self, event_time: float, action: str, line_id: int, point_id: int | None) -> None:
        seconds = int(round(event_time))
        if action == "delete_point":
            text = f"time {seconds} del ln {line_id} pt {point_id}"
        else:
            text = f"time {seconds} del ln {line_id}"
        self.history.append({
            "time": round(float(event_time), 4),
            "action": action,
            "line_id": line_id,
            "point_id": point_id,
            "text": text,
        })

    def _document_dict(self, audio_filename: str | None = None) -> dict:
        return {
            "app": APP_NAME,
            "version": APP_VERSION,
            "canvas": {"width": self.canvas_base_width, "height": self.canvas_base_height},
            "audio": {
                "file": audio_filename,
                "format": Path(audio_filename).suffix.lstrip(".") if audio_filename else None,
                "sample_rate": int(self.audio_sample_rate),
                "channels": 1,
                "duration": round(float(self.audio_duration), 4),
            },
            "strokes": self.strokes,
            "history": self.history,
        }

    def export_json(self) -> None:
        if self.recording:
            self.stop_recording()
        path = filedialog.asksaveasfilename(
            title="Сохранить рисунок в JSON", defaultextension=".json",
            filetypes=(("JSON", "*.json"),),
        )
        if not path:
            return
        try:
            data = self._document_dict(None)
            Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            self.status_var.set(f"JSON сохранён: {path}")
        except Exception as exc:
            messagebox.showerror("Ошибка сохранения", str(exc))

    def save_project(self) -> None:
        if self.recording:
            self.stop_recording()
        if len(self.audio_data) == 0:
            messagebox.showwarning("Нет аудио", "В записи нет аудиоданных. Сначала создайте запись с микрофоном.")
            return
        output_format = self.format_var.get().lower()
        path = filedialog.asksaveasfilename(
            title="Сохранить проект", defaultextension=".zip",
            initialfile="рисунок_с_аудио.zip",
            filetypes=(("Архив DrawAudio", "*.zip"),),
        )
        if not path:
            return
        try:
            audio_bytes = self._encode_audio(output_format)
            audio_name = f"audio.{output_format}"
            document = self._document_dict(audio_name)
            with ZipFile(path, "w", compression=ZIP_DEFLATED) as archive:
                archive.writestr("drawing.json", json.dumps(document, ensure_ascii=False, indent=2))
                archive.writestr(audio_name, audio_bytes)
                archive.writestr("history.txt", "\n".join(item["text"] for item in self.history))
            self.project_path = path
            self.status_var.set(f"Проект сохранён: {path}")
        except FileNotFoundError:
            messagebox.showerror(
                "Не найден FFmpeg"
            )
        except Exception as exc:
            messagebox.showerror("Ошибка сохранения проекта", str(exc))

    def open_project(self) -> None:
        path = filedialog.askopenfilename(
            title="Открыть проект DrawAudio",
            filetypes=(("Архив DrawAudio", "*.zip"), ("Все файлы", "*.*")),
        )
        if not path:
            return
        try:
            if self.recording:
                self.stop_recording(silent=True)
            self.pause_playback()
            with ZipFile(path, "r") as archive:
                names = set(archive.namelist())
                if "drawing.json" not in names:
                    raise ValueError("В архиве отсутствует drawing.json.")
                document = json.loads(archive.read("drawing.json").decode("utf-8"))
                audio_info = document.get("audio", {})
                audio_name = audio_info.get("file")
                if not audio_name or audio_name not in names:
                    raise ValueError("В архиве отсутствует аудиофайл, указанный в drawing.json.")
                encoded_audio = archive.read(audio_name)

            decoded, sample_rate = self._decode_audio(encoded_audio)
            self.strokes = document.get("strokes", [])
            self.history = document.get("history", [])
            canvas_info = document.get("canvas", {})
            self.canvas_base_width = max(1, int(canvas_info.get("width", 1000)))
            self.canvas_base_height = max(1, int(canvas_info.get("height", 450)))
            self.next_line_id = max((s.get("id", 0) for s in self.strokes), default=0) + 1
            self.audio_data = decoded
            self.audio_sample_rate = sample_rate
            self.audio_duration = len(decoded) / float(sample_rate)
            self.total_duration = max(self.audio_duration, self._last_drawing_time())
            self.playhead = 0.0
            self.session_elapsed = self.total_duration
            self.loaded_project = True
            self.project_path = path
            self.record_button.configure(text="● Новая запись")
            self.play_button.configure(state="normal")
            self.redraw_canvas(upto_time=0.0)
            self.draw_waveform()
            self.status_var.set(f"Открыт проект: {Path(path).name}. Нажмите «Воспроизвести».")
        except FileNotFoundError:
            messagebox.showerror("Не найден FFmpeg", "Для чтения MP3/OGG нужен FFmpeg.")
        except Exception as exc:
            messagebox.showerror("Не удалось открыть проект", str(exc))

    def _encode_audio(self, output_format: str) -> bytes:
        if output_format not in ("mp3", "ogg"):
            raise ValueError("Формат аудио должен быть MP3 или OGG.")
        wav_buffer = io.BytesIO()
        sf.write(wav_buffer, self.audio_data, self.audio_sample_rate, format="WAV", subtype="PCM_16")
        codec_args = ["-codec:a", "libmp3lame", "-q:a", "3"] if output_format == "mp3" else ["-codec:a", "libvorbis", "-q:a", "5"]
        command = [
            "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", "pipe:0",
            *codec_args, "-f", output_format, "pipe:1",
        ]
        result = subprocess.run(command, input=wav_buffer.getvalue(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        if result.returncode != 0:
            raise RuntimeError("FFmpeg не смог закодировать звук: " + result.stderr.decode("utf-8", "replace"))
        return result.stdout

    @staticmethod
    def _decode_audio(encoded_audio: bytes) -> tuple[np.ndarray, int]:
        command = ["ffmpeg", "-hide_banner", "-loglevel", "error", "-i", "pipe:0", "-f", "wav", "pipe:1"]
        result = subprocess.run(command, input=encoded_audio, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        if result.returncode != 0:
            raise RuntimeError("FFmpeg не смог прочитать аудио: " + result.stderr.decode("utf-8", "replace"))
        samples, sample_rate = sf.read(io.BytesIO(result.stdout), dtype="float32", always_2d=True)
        mono = samples.mean(axis=1).astype(np.float32, copy=False)
        return mono, int(sample_rate)

    # проигрыватель
    def toggle_playback(self) -> None:
        if self.is_playing:
            self.pause_playback()
        else:
            self.start_playback()

    def start_playback(self) -> None:
        if self.recording:
            messagebox.showinfo("Запись ещё идёт", "Сначала остановите запись, затем запускайте воспроизведение.")
            return
        if self.total_duration <= 0:
            self.total_duration = max(self.audio_duration, self._last_drawing_time())
        if self.playhead >= self.total_duration:
            self.playhead = 0.0
        if len(self.audio_data):
            start_frame = max(0, min(len(self.audio_data), int(self.playhead * self.audio_sample_rate)))
            audio_part = self.audio_data[start_frame:]
            if len(audio_part):
                try:
                    sd.play(audio_part, samplerate=self.audio_sample_rate, blocking=False)
                except Exception as exc:
                    messagebox.showerror("Ошибка воспроизведения", f"Не удалось воспроизвести аудио: {exc}")
                    return
        self.is_playing = True
        self.playback_started_at = time.perf_counter() - self.playhead
        self.play_button.configure(text="Ⅱ Пауза")
        self._playback_tick()

    def pause_playback(self) -> None:
        if self.is_playing:
            self.is_playing = False
            try:
                sd.stop()
            except Exception:
                pass
            if self._playback_after_id is not None:
                self.root.after_cancel(self._playback_after_id)
                self._playback_after_id = None
            self.play_button.configure(text="▶ Воспроизвести")

    def restart_playback(self) -> None:
        self.pause_playback()
        self.playhead = 0.0
        self.redraw_canvas(upto_time=0.0 if self.loaded_project else None)
        self.draw_waveform()
        self.time_var.set(f"00:00 / {self._format_time(self.total_duration)}")
        self.start_playback()

    def _playback_tick(self) -> None:
        if not self.is_playing:
            return
        self.playhead = max(0.0, time.perf_counter() - self.playback_started_at)
        self.redraw_canvas(upto_time=self.playhead)
        self.draw_waveform()
        self.time_var.set(f"{self._format_time(self.playhead)} / {self._format_time(self.total_duration)}")
        if self.playhead >= self.total_duration:
            self.pause_playback()
            self.playhead = self.total_duration
            self.redraw_canvas(upto_time=self.total_duration)
            self.draw_waveform()
            self.status_var.set("Воспроизведение завершено.")
            return
        self._playback_after_id = self.root.after(30, self._playback_tick)

    def draw_waveform(self) -> None:
        if not hasattr(self, "wave_canvas"):
            return
        c = self.wave_canvas
        c.delete("all")
        w = max(10, c.winfo_width())
        h = max(10, c.winfo_height())
        mid = h // 2
        c.create_line(0, mid, w, mid, fill="#d6d6df")
        if len(self.audio_data):
            usable = max(1, w - 20)
            buckets = min(usable, 1400)
            chunks = np.array_split(self.audio_data, buckets)
            peaks = [float(np.max(np.abs(chunk))) if len(chunk) else 0.0 for chunk in chunks]
            max_peak = max(peaks, default=0.0) or 1.0
            for i, peak in enumerate(peaks):
                x = 10 + i
                amplitude = (peak / max_peak) * (h * 0.40)
                c.create_line(x, mid - amplitude, x, mid + amplitude, fill="#6551b8", width=2)
        else:
            c.create_text(w // 2, mid, text="Здесь появится звуковая дорожка после записи", fill="#85858d")
        duration = max(self.total_duration, self.audio_duration, self._last_drawing_time(), 0.001)
        play_x = 10 + (w - 20) * min(1.0, self.playhead / duration)
        c.create_line(play_x, 5, play_x, h - 5, fill="#e05272", width=2)
        c.create_text(10, 8, anchor="nw", text="0:00", fill="#777")
        c.create_text(w - 10, 8, anchor="ne", text=self._format_time(duration), fill="#777")

    def _last_drawing_time(self) -> float:
        return max((p["t"] for s in self.strokes for p in s["points"]), default=0.0)

    @staticmethod
    def _format_time(seconds: float) -> str:
        seconds = max(0, int(seconds))
        minutes, secs = divmod(seconds, 60)
        hours, minutes = divmod(minutes, 60)
        return f"{hours:02d}:{minutes:02d}:{secs:02d}" if hours else f"{minutes:02d}:{secs:02d}"

    def _clear_document(self) -> None:
        self.strokes = []
        self.history = []
        self.next_line_id = 1
        self.active_stroke = None
        self.last_mouse_point = None
        self.canvas_base_width = max(1, self.canvas.winfo_width())
        self.canvas_base_height = max(1, self.canvas.winfo_height())
        self.playhead = 0.0
        self.total_duration = 0.0
        self.redraw_canvas()
        self.draw_waveform()
        self.time_var.set("00:00 / 00:00")

    def on_close(self) -> None:
        if self.recording:
            self.stop_recording(silent=True)
        self.pause_playback()
        self.root.destroy()


def main() -> None:
    root = tk.Tk()
    style = ttk.Style(root)
    try:
        style.theme_use("clam")
    except tk.TclError:
        pass
    style.configure("SelectedTool.TButton", relief="sunken")
    DrawAudioApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()