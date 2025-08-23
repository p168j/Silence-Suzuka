#!/usr/bin/env python3
"""
Audio Monitor Application - Modern UI with ttkbootstrap
============================================================================
SETUP INSTRUCTIONS:
============================================================================
This application requires several external libraries to be installed.
You can install them using pip. Open your terminal or command prompt and
run the following commands:

1.  pip install ttkbootstrap
2.  pip install tkinterdnd2
3.  pip install sounddevice
4.  pip install numpy
5.  pip install selenium
6.  pip install webdriver-manager
7.  pip install pandas
8.  pip install undetected-chromedriver
9.  pip install pystray
10. pip install Pillow
11. pip install pynput  # Required for AFK detection on macOS/Linux
12. pip install requests # For thumbnail fetching
13. pip install matplotlib seaborn # For heatmap visualization

You also need to have Google Chrome installed on your system for the
web monitoring features to work.

**IMPORTANT AUDIO SETUP**: For this script to work, you must enable a
"loopback" audio device on your computer, such as "Stereo Mix" on Windows,
or use a tool like VoiceMeeter. You will then need to select that device
in the app's dropdown menu.

============================================================================
"""

print("Starting Silence Suzuka...")

import tkinter as tk
from tkinter import messagebox, scrolledtext, filedialog, simpledialog
import ttkbootstrap as ttk
from ttkbootstrap.tooltip import ToolTip
import threading
import time
import sounddevice as sd
import numpy as np
import undetected_chromedriver as uc
from selenium.common.exceptions import WebDriverException, JavascriptException, TimeoutException, NoSuchElementException
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
import json
import os
import sys
import subprocess
import platform
import tempfile
import socket
import traceback
import uuid
import re
from datetime import datetime, date, timedelta
import logging
from itertools import cycle
import random
import pandas as pd
from pystray import MenuItem as item, Icon as icon, Menu
from PIL import Image, ImageDraw, ImageTk
import copy
import requests
from io import BytesIO
from collections import deque

# --- NEW: Imports for Heatmap ---
try:
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    from matplotlib.figure import Figure
    import matplotlib.animation as animation
    import seaborn as sns
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False
    print("Matplotlib not installed. Advanced visualizations will be disabled.")


# Platform-specific imports for AFK detection
if sys.platform == "win32":
    import ctypes
    from ctypes import wintypes
    pynput_mouse = pynput_keyboard = None
else:
    try:
        from pynput import mouse as pynput_mouse, keyboard as pynput_keyboard
    except ImportError:
        print("Pynput not installed. AFK feature will be disabled on this OS. Run 'pip install pynput'")
        pynput_mouse = pynput_keyboard = None


# --- Constants ---
CONFIG_FILE = 'config.json'
STATS_FILE = 'stats.json'
LOG_FILE = 'audio_monitor.log'
THEMES = ['litera', 'darkly', 'superhero'] # Light, Dark, Vibrant

# --- Setup Logging ---
try:
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[logging.FileHandler(LOG_FILE, encoding='utf-8')]
    )
except Exception as e:
    print(f"Error setting up logging: {e}")

# --- Helper Functions ---
def get_japanese_font():
    """Selects a suitable font for Japanese characters based on the OS."""
    if sys.platform == "win32":
        return "Noto Sans JP"
    elif sys.platform == "darwin":
        return "Hiragino Kaku Gothic ProN"
    else:
        return "TkDefaultFont"

class AudioMonitorApp:
    """The main class for the audio monitoring application with a modern UI."""
    def __init__(self, root):
        self.root = root
        # --- Custom styles for the Enhanced Navigation Panel ---
        style = ttk.Style()
    
        
        # --- Initialize Tkinter Variables ---
        self.theme_var = tk.StringVar(value=self.root.style.theme_use())
        self.headless_var = tk.BooleanVar(value=True)
        self.random_list_var = tk.BooleanVar(value=False)
        self.save_timestamp_var = tk.BooleanVar(value=True)
        self.unmute_var = tk.BooleanVar(value=False)
        self.auto_skip_var = tk.BooleanVar(value=True)
        self.sync_video_pause_var = tk.BooleanVar(value=True)
        self.keep_browser_open_var = tk.BooleanVar(value=True)
        self.delay_minutes_var = tk.DoubleVar(value=5.0)
        self.silence_minutes_var = tk.DoubleVar(value=2.0) # SMART DEFAULT
        self.sound_threshold_var = tk.DoubleVar(value=0.5)
        self.silence_threshold_var = tk.DoubleVar(value=0.1) 
        self.audio_gain_var = tk.DoubleVar(value=1.0) 
        self.expand_playlists_var = tk.BooleanVar(value=False) 
        self.shuffle_within_playlists_var = tk.BooleanVar(value=False)
        self.use_mpv_var = tk.BooleanVar(value=False)
        self.profile_path_var = tk.StringVar()
        self.profile_name_var = tk.StringVar()
        self.mpv_path_var = tk.StringVar()
        self.recursive_folder_var = tk.BooleanVar(value=True)
        self.fetch_titles_var = tk.BooleanVar(value=True)
        self.app_geometry_var = tk.StringVar()
        self.browser_geometry_var = tk.StringVar()
        self.audio_device_var = tk.StringVar()
        self.afk_enabled_var = tk.BooleanVar(value=False)
        self.afk_timeout_minutes_var = tk.DoubleVar(value=5.0)
        self.show_afk_status_var = tk.BooleanVar(value=True)
        self.autostart_var = tk.BooleanVar(value=False) 
        self.countdown_var = tk.StringVar() 
        self.treat_playlists_as_videos_var = tk.BooleanVar(value=False)
        self.sequential_playlists_var = tk.BooleanVar(value=True)
        self.true_random_on_skip_var = tk.BooleanVar(value=False)
        self.main_queue = []
        self.main_queue_index = 0
        self.current_item_type = None
        self.playlist_exhausted = False
        self.jump_entry_var = tk.StringVar()
        self.slider_var = tk.IntVar(value=1)
        self.current_video_title_var = tk.StringVar(value="")
        self.nav_frame = None # Changed from nav_controls_frame
        self.finished_percentage_var = tk.IntVar(value=95)
        self.tree_items = []
        self.audio_level = 0
        self.active_profile_name = tk.StringVar()
        self.search_var = tk.StringVar()
        self.playlist_mode_var = tk.StringVar(value="Custom")
        self.smart_shuffle_var = tk.BooleanVar(value=False)
        self.log_visible = tk.BooleanVar(value=False)
        self.now_playing_progress_var = tk.DoubleVar(value=0)
        self.now_playing_title_var = tk.StringVar(value="Nothing Playing")
        self.search_var.trace("w", self.filter_treeview)
        self.always_show_nav_panel_var = tk.BooleanVar(value=False)
        self.always_show_nav_panel_var.trace("w", self.update_playlist_info)
        
        # --- Initialize State Variables ---
        self.ignore_timestamps_for_session = False
        self.current_playlist_videos = []
        self.current_playlist_index = 0
        self.schedule_id = None
        self.is_monitoring = False
        self.is_paused = False
        self.monitor_thread = None
        self.browser = None
        self.mpv_process = None
        self.current_url = None
        self.mpv_ipc_path = None
        self.monitoring_start_time = None
        self.monitoring_paused_time = 0
        self.pause_start_time = None
        self.monitored_time_started = False
        self.video_load_time = 0
        self.last_audio_trigger = time.time()
        self.last_stats_update_time = time.time()
        self.stats = {}
        self.log_text = None
        self.tray_icon = None
        self.url_to_title_map = {}
        self.audio_devices = {}
        self.silence_start_time = None
        self.is_afk = False 
        self.last_countdown_update = 0
        self.expanded_video_pool = []
        self.all_tree_items = []
        self.subscriptions = []
        self.thumbnail_cache = {}
        self.preview_window = None
        self.preview_job = None
        self.now_playing_thumbnail_photo = None # To prevent garbage collection
        self.setup_complete_event = threading.Event() # FIX: For robust startup
        self.skip_event = threading.Event()
        self.skip_to_next_in_playlist = False
        self.playlist_exhausted = False
        self.custom_settings_frame = None # To hold the custom settings frame widget
        self.keybind_window = None # To ensure only one help window opens
        self.last_sort_column = None
        self.last_sort_reverse = False
        self.keybind_window = None # To ensure only one help window opens
        # --- ENHANCED: Audio visualization variables ---
        self.visualization_mode_var = tk.StringVar(value="bar")
        self.audio_buffer = deque(maxlen=4410)  # 0.1 second buffer at 44100 Hz
        self.frequency_buffer = deque(maxlen=100)
        self.is_silence_detected = False
        self.waveform_figure = None
        self.waveform_canvas = None
        self.waveform_line = None
        self.spectrum_bars = None
        self.visualization_animation = None
        self.previous_playlist_mode = "Custom" # To store the mode before a change
        
        # --- FIX: Debounce variables for flicker-free silence indicator ---
        self.silence_debounce_time = 0.2 # 200ms
        self.last_sound_time = time.time()
        self.last_silence_time = time.time()
        self.current_indicator_state = False # False = Active, True = Silence

        # --- Startup Order ---
        self.create_widgets()
        self.populate_audio_devices()
        self.load_stats()
        
        # Welcome dialog for first-time users
        if not os.path.exists(CONFIG_FILE):
            self.show_first_time_welcome()
        
        # Set the theme change listener BEFORE loading the config
        self.theme_var.trace('w', self.on_theme_change)
        
        # Now, when load_config sets the theme, on_theme_change will fire and apply styles
        self.load_config() 
        
        self.update_window_title() # Initial title set
        
        # --- Keyboard Shortcuts ---
        self.root.bind('<F1>', self.show_keybinds)
        self.root.bind('<space>', self.toggle_play_pause)
        self.root.bind('<Escape>', lambda e: self.stop_monitoring())
        self.root.bind('<Delete>', lambda e: self.remove_selected_url())
        
        # Navigation
        self.root.bind('<Right>', lambda e: self.next_video())
        self.root.bind('<Left>', lambda e: self.previous_video())
        self.root.bind('<Control-Right>', lambda e: self.skip_videos(5))
        self.root.bind('<Control-Left>', lambda e: self.skip_videos(-5))

        # Playlist Management
        self.root.bind('<Control-a>', lambda e: self.add_url_to_treeview())
        self.root.bind('<Control-A>', lambda e: self.add_url_to_treeview()) # For caps lock
        self.root.bind('<Control-s>', lambda e: self.save_playlist())
        self.root.bind('<Control-S>', lambda e: self.save_playlist())
        self.root.bind('<Control-o>', lambda e: self.load_playlist())
        self.root.bind('<Control-O>', lambda e: self.load_playlist())

        # UI Interaction
        self.root.bind('<Control-f>', lambda e: self.search_entry.focus_set())
        self.root.bind('<Control-F>', lambda e: self.search_entry.focus_set())
        self.root.bind('<Control-n>', lambda e: self.video_link_entry.focus_set())
        self.root.bind('<Control-N>', lambda e: self.video_link_entry.focus_set())
        self.root.bind('l', lambda e: self.toggle_log())
        self.root.bind('L', lambda e: self.toggle_log())
        
        if self.app_geometry_var.get():
            try:
                self.root.geometry(self.app_geometry_var.get())
            except tk.TclError:
                self.log("Invalid app window geometry in config, using default.", "orange")
                self.set_default_geometry()
        else:
            self.set_default_geometry()
            
        self.root.protocol("WM_DELETE_WINDOW", self.hide_window)
        self.setup_system_tray()
        self.start_audio_preview()
        self.start_afk_detector()
        self.update_flicker_free_indicator() # Start the flicker-free loop
        
        # Set initial state of checkboxes on startup
        self.on_playlist_mode_change()
        self.update_playlist_info() # Refresh panel visibility on startup

        print("Application initialized successfully!")
        self.log("Application ready with a modern UI!")

        if self.autostart_var.get():
            self.root.after(1000, self.start_monitoring_with_resume)
            
    def get_video_title(self, url):
        """ENHANCED: Gets the actual title of a video from the map or URL."""
        if not url:
            return "N/A"
        
        # Check if we have a saved title
        title = self.url_to_title_map.get(url)
        
        # Clean up the title if we have one
        if title and title not in ["Fetching Title...", "Title Unavailable", "Title Fetch Failed"]:
            # Expanded list of suffixes to remove for cleaner titles
            suffixes_to_remove = [
                '哔哩哔哩视频', ' - 哔哩哔哩', '-哔哩哔哩', '_bilibili', '| bilibili', '哔哩哔哩',
                ' - YouTube', '| YouTube'
            ]
            for site_name in suffixes_to_remove:
                if title.lower().endswith(site_name.lower()):
                    title = title[:-len(site_name)]
                    break
            return title.strip(' _|-')
        
        # Fallback to basename for local files or URL
        if self.is_local_file(url):
            return os.path.basename(url)
        
        # For URLs without saved titles, return a cleaned version
        return url.split('/')[-1][:50] if '/' in url else url[:50]
        
    def always_expand_playlists(self, urls):
        """MODIFIED: Expand the first playlist in the queue using a temporary headless browser."""
        if not urls:
            return []

        first_url = urls[0]
        url_type = self.get_url_type(first_url)
        
        # Only expand if it's a playlist and not treat_playlists_as_videos
        if url_type == "Playlist" and not self.treat_playlists_as_videos_var.get():
            self.log(f"Expanding first playlist headlessly: {first_url}", "blue")
            try:
                options = uc.ChromeOptions()
                options.add_argument("--headless=new")
                options.add_argument("--mute-audio")
                with uc.Chrome(options=options, patcher_force_close=True) as temp_browser:
                    videos = self.get_playlist_videos(temp_browser, first_url)
                
                if not videos or (len(videos) == 1 and videos[0] == first_url):
                    self.log("Playlist expansion failed or returned no videos. Playing as single item.", "orange")
                    return urls # Fallback to original list
                else:
                    self.log(f"Expanded playlist into {len(videos)} videos.", "green")
                    # Replace the original playlist URL with the expanded video list
                    return videos + urls[1:]
            except Exception as e:
                self.log(f"Could not set up headless browser for playlist expansion: {e}", "red")
                return urls # Fallback to original list on error
        else:
            return urls
        
    def toggle_play_pause(self, event=None):
        """Handles the spacebar press to toggle play/pause/resume."""
        if not self.is_monitoring:
            self.start_monitoring_with_resume()
        elif self.is_paused:
            self.resume_monitoring()
        else:
            self.pause_monitoring()

    def update_window_title(self):
        """Dynamically updates the main window's title bar with actual video title."""
        if self.is_monitoring:
            display_name = self.get_video_title(self.current_url)
            title = f"▶️ Playing - {display_name[:40]}"
            if len(display_name) > 40:
                title += "..."
            self.root.title(title)
        else:
            count = len(self.get_items_from_display())
            self.root.title(f"Silence Suzuka - {count} videos ready")

    def set_default_geometry(self):
        """Sets the default size and position for the main window."""
        # REFACTORED: Default to a more vertical-friendly aspect ratio
        width = 800
        height = self.root.winfo_screenheight() - 90 
        x_pos = (self.root.winfo_screenwidth() // 2) - (width // 2)
        self.root.geometry(f"{width}x{height}+{x_pos}+20")
    
    def show_context_menu(self, event):
        """Displays the context menu when a user right-clicks on the Treeview."""
        item_id = self.url_tree.identify_row(event.y)
        if item_id:
            self.url_tree.selection_set(item_id)
            self.context_menu.tk_popup(event.x_root, event.y_root)

    def on_tree_motion(self, event):
        """Called when the mouse moves over the treeview."""
        if self.preview_job:
            self.root.after_cancel(self.preview_job)
            self.preview_job = None

        item_id = self.url_tree.identify_row(event.y)
        if item_id:
            self.preview_job = self.root.after(500, self.show_preview, item_id)
        else:
            self.hide_preview()

    def on_tree_leave(self, event):
        """Called when the mouse leaves the treeview."""
        if self.preview_job:
            self.root.after_cancel(self.preview_job)
            self.preview_job = None
        self.hide_preview()

    def copy_link(self):
        """Copies the URL of the selected item to the clipboard."""
        selected_item = self.url_tree.selection()
        if selected_item:
            item_id = selected_item[0]
            url = self.url_tree.item(item_id, 'values')[1]
            self.root.clipboard_clear()
            self.root.clipboard_append(url)
            self.log(f"Copied link to clipboard: {url}", 'blue')

    def _autosave_settings(self, *args):
        """
        A simple wrapper to call save_profile for autosaving.
        This is triggered by UI element commands, bindings, and variable traces.
        """
        if self.active_profile_name.get():
            self.save_profile()

    def on_theme_change(self, *args):
        """Called when the theme dropdown changes."""
        theme_name = self.theme_var.get()
        self.root.style.theme_use(theme_name)
        self._apply_custom_font_styles() # Re-apply custom fonts
        self.update_visualization_theme()
        
        # --- START: NEWLY ADDED CODE ---
        # Adjust countdown label color for better theme contrast
        if theme_name in ['darkly', 'superhero']:
            # Use 'light' style for better visibility on dark backgrounds
            self.countdown_label.config(bootstyle="light")
        else:
            # Use the default 'secondary' style for light themes
            self.countdown_label.config(bootstyle="secondary")
        # --- END: NEWLY ADDED CODE ---

        self._autosave_settings()

    def _apply_custom_font_styles(self):
        """Applies a consistent, language-aware font to key widgets after a theme change."""
        font_name = "Arial"
        self.root.style.configure('Treeview', font=(font_name, 12))
        self.root.style.configure('Treeview.Heading', font=(font_name, 10, 'bold'))
        self.root.style.configure('primary.Treeview', font=(font_name, 12))
        self.root.style.configure('primary.Treeview.Heading', font=(font_name, 10, 'bold'))

    # ==================================================================================
    # --- REFACTOR: Main create_widgets method for the "Control Tower" layout ---
    # ==================================================================================
    def create_widgets(self):
        """Create all the UI elements for the application using a top-bottom layout."""
        # --- Main Layout Frames ---
        # Top frame for the "Dashboard" (always visible controls)
        # It has a fixed height, so it doesn't expand.
        dashboard_frame = ttk.Frame(self.root, padding=(10, 10, 10, 0))
        dashboard_frame.pack(fill=tk.X, side=tk.TOP)

        # Bottom frame for the "Library & Settings" (tabbed interface)
        # It expands to fill the remaining space.
        main_content_frame = ttk.Frame(self.root, padding=10)
        main_content_frame.pack(fill=tk.BOTH, expand=True)

        # --- 1. Build the Dashboard (Top Frame) ---
        self.dashboard_frame = dashboard_frame # Store reference for Now Playing card
        
        # Now Playing Card will be packed into the dashboard when monitoring starts
        self.now_playing_frame = ttk.Labelframe(self.dashboard_frame, text="Now Playing", padding=10)
        self.now_playing_frame.pack(fill=tk.X, pady=(0, 5))
        now_playing_content = ttk.Frame(self.now_playing_frame)
        now_playing_content.pack(fill=tk.BOTH, expand=True)
        self.now_playing_thumbnail_label = ttk.Label(now_playing_content)
        self.now_playing_thumbnail_label.pack(side=tk.LEFT, padx=(0, 10))
        self.set_placeholder_thumbnail()
        info_frame = ttk.Frame(now_playing_content)
        info_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.now_playing_title_label = ttk.Label(info_frame, textvariable=self.now_playing_title_var, font=(get_japanese_font(), 14, 'bold'))
        self.now_playing_title_label.pack(anchor='w', fill=tk.X)
        self.now_playing_progress = ttk.Progressbar(info_frame, variable=self.now_playing_progress_var, maximum=100)
        self.now_playing_progress.pack(fill=tk.X, pady=5)
        self.now_playing_play_pause_btn = ttk.Button(now_playing_content, text="⏸️", command=self.toggle_play_pause, bootstyle="secondary", width=3)
        self.now_playing_play_pause_btn.pack(side=tk.RIGHT, padx=(10, 0))

        # Main Play/Pause/Stop Buttons
        self.root.style.configure('big.TButton', font=(get_japanese_font(), 12, 'bold'))
        button_frame = ttk.Frame(self.dashboard_frame)
        button_frame.pack(fill=tk.X, pady=5, ipady=5)
        self.start_btn = ttk.Button(button_frame, text="▶️ PLAY", command=self.start_monitoring_with_resume, bootstyle="success", style='big.TButton')
        self.start_btn.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=2)
        ToolTip(self.start_btn, "Start playing from last session (Space)")
        self.pause_btn = ttk.Button(button_frame, text="⏸️ PAUSE", command=self.pause_monitoring, state=tk.DISABLED, bootstyle="warning", style='big.TButton')
        self.pause_btn.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=2)
        ToolTip(self.pause_btn, "Pause playback (Space)")
        self.stop_btn = ttk.Button(button_frame, text="⏹️ STOP", command=self.stop_monitoring, state=tk.DISABLED, bootstyle="danger", style='big.TButton')
        self.stop_btn.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=2)
        ToolTip(self.stop_btn, "Stop playback (Esc)")

        # Status Display
        status_frame = ttk.Labelframe(self.dashboard_frame, text="Status", padding="10")
        status_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        status_top = ttk.Frame(status_frame)
        status_top.pack(fill=tk.X)
        self.status_label = ttk.Label(status_top, text="Status: 🎧 Listening", font=(get_japanese_font(), 12, 'bold'))
        self.status_label.pack(side=tk.LEFT)
        self.countdown_label = ttk.Label(status_top, textvariable=self.countdown_var, font=(get_japanese_font(), 11, 'italic'), bootstyle="secondary")
        self.countdown_label.pack(side=tk.LEFT, padx=10)
        ToolTip(self.countdown_label, text="When silence is detected for the duration set in Settings, this timer will begin. The next video will automatically play when the countdown is complete.")
        self.silence_indicator = ttk.Label(status_top, text="", font=(get_japanese_font(), 11))
        self.silence_indicator.pack(side=tk.LEFT, padx=10)
        self.time_label = ttk.Label(status_top, text="Time: 0h 0m 0s", font=(get_japanese_font(), 12))
        self.time_label.pack(side=tk.RIGHT)
        self.visualization_container = ttk.Frame(status_frame, height=60)
        self.visualization_container.pack(fill=tk.X, pady=(5, 0))
        self.visualization_container.pack_propagate(False)
        self.sound_bar_canvas = None # Will be populated by switch_visualization
        log_toggle_frame = ttk.Frame(status_frame)
        log_toggle_frame.pack(fill=tk.X, pady=(5,0))
        self.toggle_log_btn = ttk.Button(log_toggle_frame, text="Show Logs ▼", command=self.toggle_log, bootstyle="light-outline")
        self.toggle_log_btn.pack(side=tk.LEFT)
        self.log_text = scrolledtext.ScrolledText(status_frame, state='disabled', height=10, wrap=tk.WORD, font=(get_japanese_font(), 10))

        # --- 2. Build the Main Content Area (Bottom Frame with Tabs) ---
        notebook = ttk.Notebook(main_content_frame)
        notebook.pack(fill=tk.BOTH, expand=True)

        # -- Tab 1: Playlist --
        playlist_tab = ttk.Frame(notebook, padding=(0, 10, 0, 0))
        notebook.add(playlist_tab, text="Playlist")
        
        self.url_frame = ttk.Labelframe(playlist_tab, text="Playlist 📝", padding="10")
        self.url_frame.pack(fill=tk.BOTH, pady=5, expand=True)
        search_frame = ttk.Frame(self.url_frame)
        search_frame.pack(fill=tk.X, pady=(0, 5))
        self.search_entry = ttk.Entry(search_frame, textvariable=self.search_var)
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ToolTip(self.search_entry, "Filter playlist by title or URL")
        self.root.style.configure('Treeview', font=(get_japanese_font(), 12), rowheight=35)
        self.root.style.configure('Treeview.Heading', font=(get_japanese_font(), 10, 'bold'))
        columns = ("status", "title", "url", "type")
        self.url_tree = ttk.Treeview(self.url_frame, columns=columns, show="headings", bootstyle="primary", height=10)
        
        # --- Column Headers (with sorting commands) ---
        self.url_tree.heading("status", text="📊", command=lambda: self.sort_treeview_column("status", False))
        self.url_tree.heading("title", text="Title", command=lambda: self.sort_treeview_column("title", False))
        self.url_tree.heading("url", text="Source") # Not sortable
        self.url_tree.heading("type", text="Type", command=lambda: self.sort_treeview_column("type", False))
        
        # --- Column Configuration ---
        self.url_tree.column("status", stretch=False, width=40, anchor=tk.CENTER)
        self.url_tree.column("title", stretch=True, minwidth=300, width=500, anchor=tk.W)
        self.url_tree.column("url", stretch=True, minwidth=100, anchor=tk.W)
        self.url_tree.column("type", stretch=False, minwidth=60, width=80, anchor=tk.CENTER)
        self.url_tree.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        self.url_tree.bind("<Double-1>", self.on_double_click_item)
        self.url_tree.bind("<Button-3>", self.show_context_menu)
        self.url_tree.bind("<Motion>", self.on_tree_motion)
        self.url_tree.bind("<Leave>", self.on_tree_leave)
        self.url_tree.bind("<ButtonPress-1>", self.on_drag_start)
        self.url_tree.bind("<B1-Motion>", self.on_drag_motion)
        self.url_tree.bind("<ButtonRelease-1>", self.on_drag_release)
        self._drag_data = {"item": None, "y": 0}
        
        # Context Menu
        self.context_menu = tk.Menu(self.root, tearoff=0)
        self.context_menu.add_command(label="▶️ Play Next", command=self.play_next)
        self.context_menu.add_command(label="📋 Copy Link", command=self.copy_link)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="✔️ Mark as Watched", command=self.mark_as_watched)
        self.context_menu.add_command(label="✖️ Mark as Unwatched", command=self.mark_as_unwatched)
        
        # Playlist Input and Management Buttons
        input_frame = ttk.Frame(playlist_tab)
        input_frame.pack(fill=tk.X, pady=(0, 5))
        self.video_link_entry = ttk.Entry(input_frame)
        self.video_link_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        ToolTip(self.video_link_entry, "Paste a video/playlist URL or local file path here")
        self.add_url_btn = ttk.Button(input_frame, text="Add", command=self.add_url_to_treeview, bootstyle="success")
        self.add_url_btn.pack(side=tk.LEFT, padx=2)
        self.add_folder_btn = ttk.Button(input_frame, text="Add Folder", command=self.add_folder_to_treeview, bootstyle="info")
        self.add_folder_btn.pack(side=tk.LEFT, padx=2)
        self.browse_file_btn = ttk.Button(input_frame, text="Browse File", command=self.browse_file, bootstyle="info")
        self.browse_file_btn.pack(side=tk.LEFT, padx=2)
        
        playlist_button_frame = ttk.Frame(playlist_tab)
        playlist_button_frame.pack(fill=tk.X, pady=5)
        self.remove_url_btn = ttk.Button(playlist_button_frame, text="Remove", command=self.remove_selected_url, bootstyle="danger")
        self.remove_url_btn.pack(side=tk.LEFT, padx=5)
        self.save_playlist_btn = ttk.Button(playlist_button_frame, text="Save List", command=self.save_playlist, bootstyle="primary-outline")
        self.save_playlist_btn.pack(side=tk.LEFT, padx=5)
        self.load_playlist_btn = ttk.Button(playlist_button_frame, text="Load List", command=self.load_playlist, bootstyle="info-outline")
        self.load_playlist_btn.pack(side=tk.LEFT, padx=5)
        ttk.Button(playlist_button_frame, text="🗑️ Clear All", command=self.clear_all_urls, bootstyle="danger-outline").pack(side=tk.LEFT, padx=5)
        
        # --- START: NEWLY ADDED WIDGETS ---
        main_playlist_mode_combo = ttk.Combobox(playlist_button_frame, textvariable=self.playlist_mode_var,
                                                values=["Sequential", "Shuffle All", "True Random", "Smart Shuffle", "Custom"],
                                                state="readonly",
                                                width=15)
        main_playlist_mode_combo.pack(side=tk.RIGHT, padx=5)
        ToolTip(main_playlist_mode_combo, "Select a playback mode preset")
        main_playlist_mode_combo.bind("<<ComboboxSelected>>", self.on_playlist_mode_change)

        ttk.Label(playlist_button_frame, text="Playlist Mode:").pack(side=tk.RIGHT)
        # --- END: NEWLY ADDED WIDGETS ---

        ttk.Button(playlist_button_frame, text="📊 View Statistics", command=self.view_stats, bootstyle="info-outline").pack(side=tk.RIGHT, padx=5)

        # --- START: BALANCED COMPACT NAVIGATION PANEL ---
        self.nav_frame = ttk.Labelframe(playlist_tab, text="Navigation", padding=5)
        
        # Main container for the single-line layout
        enhanced_main = ttk.Frame(self.nav_frame)
        enhanced_main.pack(fill=tk.X)

        # Create a centered frame that will hold all controls
        controls_container = ttk.Frame(enhanced_main)
        controls_container.pack(expand=True)

        # Left-side buttons
        ttk.Button(
            controls_container, 
            text="◀◀ -10", 
            command=lambda: self.skip_videos(-10),
            bootstyle="dark-outline"
        ).pack(side=tk.LEFT, padx=2)
        
        ttk.Button(
            controls_container, 
            text="◀ -5", 
            command=lambda: self.skip_videos(-5),
            bootstyle="dark-outline"
        ).pack(side=tk.LEFT, padx=2)
        
        self.prev_btn = ttk.Button(
            controls_container, 
            text="◀ Prev", 
            command=self.previous_video, 
            state=tk.DISABLED, 
            bootstyle="primary"
        )
        self.prev_btn.pack(side=tk.LEFT, padx=(2, 15))

        # Center jump control - no expand, just normal packing
        jump_container = ttk.Frame(controls_container)
        jump_container.pack(side=tk.LEFT, padx=10)

        ttk.Label(jump_container, text="Jump to:").pack(side=tk.LEFT, padx=(0, 5))
        
        self.jump_entry = ttk.Entry(
            jump_container, 
            textvariable=self.jump_entry_var, 
            width=5, 
            justify='center',
            bootstyle="primary"
        )
        self.jump_entry.pack(side=tk.LEFT)
        self.jump_entry.bind('<Return>', self.on_jump_entry)
        self.jump_entry.bind('<KP_Enter>', self.on_jump_entry)
        
        self.total_videos_label = ttk.Label(jump_container, text="/ --")
        self.total_videos_label.pack(side=tk.LEFT, padx=3)
        
        ttk.Button(
            jump_container, 
            text="Go", 
            command=self.on_jump_entry, 
            bootstyle="primary"
        ).pack(side=tk.LEFT, padx=(3, 0))

        # Right-side buttons
        self.next_btn = ttk.Button(
            controls_container, 
            text="Next ▶", 
            command=self.next_video, 
            state=tk.DISABLED, 
            bootstyle="primary"
        )
        self.next_btn.pack(side=tk.LEFT, padx=(15, 2))
        
        ttk.Button(
            controls_container, 
            text="+5 ▶", 
            command=lambda: self.skip_videos(5),
            bootstyle="dark-outline"
        ).pack(side=tk.LEFT, padx=2)
        
        ttk.Button(
            controls_container, 
            text="+10 ▶▶", 
            command=lambda: self.skip_videos(10),
            bootstyle="dark-outline"
        ).pack(side=tk.LEFT, padx=2)

        # Simple progress bar
        self.nav_progress_var = tk.DoubleVar(value=0)
        self.nav_progress = ttk.Progressbar(
            self.nav_frame, 
            variable=self.nav_progress_var, 
            maximum=100,
            bootstyle="info-striped"
        )
        self.nav_progress.pack(fill=tk.X, pady=(5, 3))

        # Simple info label
        self.playlist_info_label = ttk.Label(
            self.nav_frame, 
            text="Playback stopped. Press Play to begin.", 
            font=(get_japanese_font(), 9)
        )
        self.playlist_info_label.pack(fill=tk.X, pady=(3, 0))
        
        # --- END: BALANCED COMPACT NAVIGATION PANEL ---

        # -- Tab 2: Settings --
        settings_tab = ttk.Frame(notebook, padding=10)
        notebook.add(settings_tab, text="Settings")
        
        # Call the refactored method to build the settings UI inside the tab
        self._create_settings_tab(settings_tab)
        
        # --- 3. Final Initialization ---
        self.root.after(100, self.initialize_visualization)
    def get_status_emoji(self, url):
        """Gets a status emoji based on the video's saved timestamp."""
        status = self.get_saved_timestamp_status(url)
        if status == "finished":
            return "✅"  # Watched
        elif isinstance(status, (int, float)) and status > 0:
            return "◐"  # In Progress
        else:
            return ""  # Unwatched

    def sort_treeview_column(self, col, reverse):
        """Sorts a treeview column when its header is clicked."""
        # Check if we are sorting the same column again to toggle direction
        if col == self.last_sort_column:
            reverse = not self.last_sort_reverse
        else:
            reverse = False

        # Get data from the column
        try:
            data_list = [(self.url_tree.set(k, col).lower(), k) for k in self.url_tree.get_children('')]
        except tk.TclError: # Fallback for columns with potential errors
            return

        # Sort the data
        data_list.sort(key=lambda t: t[0], reverse=reverse)

        # Rearrange items in the treeview
        for index, (val, k) in enumerate(data_list):
            self.url_tree.move(k, '', index)

        # Update the command for the next click to be reversed
        self.url_tree.heading(col, command=lambda: self.sort_treeview_column(col, not reverse))
        
        # Store the last sort state
        self.last_sort_column = col
        self.last_sort_reverse = reverse

    def update_item_status_in_treeview(self, url_to_update):
        """Finds a specific item in the treeview by URL and updates its status icon."""
        url_to_update = self._clean_url(url_to_update)
        new_status_emoji = self.get_status_emoji(url_to_update)
        
        for item_id in self.url_tree.get_children():
            values = self.url_tree.item(item_id, 'values')
            if values and len(values) > 2 and self._clean_url(values[2]) == url_to_update:
                # Rebuild the values tuple with the new status
                new_values = (new_status_emoji, values[1], values[2], values[3])
                self.url_tree.item(item_id, values=new_values)
                break # Stop after finding and updating the item    

    def show_keybinds(self, event=None):
        """Displays a Toplevel window with a list of all available keybinds, ensuring only one instance exists."""
        # --- START: MODIFICATION ---
        # If the window already exists, just bring it to the front and return.
        if self.keybind_window and self.keybind_window.winfo_exists():
            self.keybind_window.lift()
            return
        # --- END: MODIFICATION ---

        self.keybind_window = ttk.Toplevel(self.root)
        self.keybind_window.title("Keyboard Shortcuts")
        self.keybind_window.transient(self.root)
        self.keybind_window.grab_set()
        self.keybind_window.resizable(False, False)

        main_frame = ttk.Frame(self.keybind_window, padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)

        header = ttk.Label(main_frame, text="Keyboard Shortcuts", font=(get_japanese_font(), 16, 'bold'))
        header.pack(pady=(0, 15))

        keybinds = {
            "Playback Control": {
                "Spacebar": "Play / Pause / Resume",
                "Right Arrow": "Next Video in Playlist",
                "Left Arrow": "Previous Video in Playlist",
                "Ctrl + Right Arrow": "Jump Forward +5 Videos",
                "Ctrl + Left Arrow": "Jump Back -5 Videos",
                "Esc": "Stop Playback",
            },
            "Playlist Management": {
                "Ctrl + A": "Add URL from Input Box",
                "Delete": "Remove Selected Item(s)",
                "Ctrl + S": "Save Current Playlist",
                "Ctrl + O": "Load Playlist from File",
            },
            "UI Interaction": {
                "F1": "Show this Help Window",
                "Ctrl + F": "Focus Search/Filter Box",
                "Ctrl + N": "Focus 'Add URL' Input Box",
                "l (lowercase L)": "Toggle Log Panel Visibility",
            }
        }

        for category, shortcuts in keybinds.items():
            cat_frame = ttk.Labelframe(main_frame, text=category, padding=10)
            cat_frame.pack(fill=tk.X, pady=5)
            for key, desc in shortcuts.items():
                row = ttk.Frame(cat_frame)
                row.pack(fill=tk.X, pady=2)
                key_label = ttk.Label(row, text=key, width=20, font=(get_japanese_font(), 10, 'bold'))
                key_label.pack(side=tk.LEFT)
                desc_label = ttk.Label(row, text=desc)
                desc_label.pack(side=tk.LEFT)

        # --- START: MODIFICATION ---
        # Helper function to properly handle closing the window
        def on_close():
            self.keybind_window.destroy()
            self.keybind_window = None

        close_btn = ttk.Button(main_frame, text="Close", command=on_close, bootstyle="primary")
        close_btn.pack(pady=(15, 0))
        # Set the protocol for the window's close button (the 'X')
        self.keybind_window.protocol("WM_DELETE_WINDOW", on_close)
        # --- END: MODIFICATION ---

    # ==================================================================================
    # --- REFACTOR: This method now builds the settings UI into a parent tab ---
    # ==================================================================================
    def _create_settings_tab(self, parent):
        """Creates the advanced settings UI inside the given parent widget."""
        # Create a notebook within the settings tab for better organization
        settings_notebook = ttk.Notebook(parent)
        settings_notebook.pack(fill=tk.BOTH, expand=True)

        # Create individual tabs for each settings category
        general_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(general_tab, text="General")
        playback_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(playback_tab, text="Playback")
        playlist_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(playlist_tab, text="Playlist")
        audio_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(audio_tab, text="Audio")
        profile_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(profile_tab, text="Profiles & Paths")
        subscriptions_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(subscriptions_tab, text="Subscriptions")
        
        # --- General Tab ---
        gen_frame = ttk.Labelframe(general_tab, text="Application Behavior", padding=10)
        gen_frame.pack(fill=tk.X, pady=5)
        self._create_check(gen_frame, "Auto-start Playing on Launch", self.autostart_var, "Automatically start playing when the application launches.")
        self._create_check(gen_frame, "Save Timestamps & Stats", self.save_timestamp_var, "Save the last video position and daily usage stats.")
        self._create_check(gen_frame, "Fetch Titles for Web URLs", self.fetch_titles_var, "Automatically fetch titles for web URLs. Can be slow.")
        self._create_check(gen_frame, "Always Show Navigation Panel", self.always_show_nav_panel_var, "Keeps the navigation panel visible even when playback is stopped.")

        theme_frame = ttk.Labelframe(general_tab, text="Appearance", padding=10)
        theme_frame.pack(fill=tk.X, pady=5)
        theme_menu = ttk.Combobox(theme_frame, textvariable=self.theme_var, values=THEMES, state="readonly", width=15)
        theme_menu.pack(side=tk.LEFT, padx=5)
        ToolTip(theme_menu, "Application Theme")
        ttk.Label(theme_frame, text="Theme:").pack(side=tk.LEFT)

        afk_frame = ttk.Labelframe(general_tab, text="AFK (Away From Keyboard) Detection", padding=10)
        afk_frame.pack(fill=tk.X, pady=5)
        if (sys.platform == "win32") or (pynput_mouse and pynput_keyboard):
            self._create_check(afk_frame, "Pause when AFK", self.afk_enabled_var, "Prevent autoplaying the next video if no mouse/keyboard activity is detected.")
            afk_entry = ttk.Entry(afk_frame, textvariable=self.afk_timeout_minutes_var, width=5)
            afk_entry.pack(side=tk.LEFT, padx=10)
            ToolTip(afk_entry, "AFK Timeout (minutes)")
            self.afk_timeout_minutes_var.trace("w", self._autosave_settings)
            self._create_check(afk_frame, "Show AFK status in UI", self.show_afk_status_var, "Display AFK status in the main status label.")
        else:
            ttk.Label(afk_frame, text="AFK feature disabled: requires 'pynput' library on this OS.", bootstyle="danger").pack(side=tk.LEFT, padx=5)

        # --- Playback Tab ---
        browser_frame = ttk.Labelframe(playback_tab, text="Browser Playback", padding=10)
        browser_frame.pack(fill=tk.X, pady=5)
        self._create_check(browser_frame, "Headless Mode", self.headless_var, "Run browser in the background without a visible window.")
        self._create_check(browser_frame, "Keep Browser Open on Stop", self.keep_browser_open_var, "If checked, the browser will not close when you click 'Stop Playing'.")
        self._create_check(browser_frame, "Unmute Video on Load", self.unmute_var, "Play video with sound (requires browser reload).")
        self._create_check(browser_frame, "Sync with Video's Native Pause/Play", self.sync_video_pause_var, "Automatically pause/resume playing when the video is paused/resumed in the player.")
        
        skip_frame = ttk.Labelframe(playback_tab, text="Video Progression", padding=10)
        skip_frame.pack(fill=tk.X, pady=5)
        self._create_check(skip_frame, "Auto-skip When Video Ends", self.auto_skip_var, "Automatically skip to the next URL when the current video ends.")
        percentage_frame = ttk.Frame(skip_frame)
        percentage_frame.pack(fill=tk.X, pady=5)
        ttk.Label(percentage_frame, text="Mark as 'finished' at (%):").pack(side=tk.LEFT, padx=(0, 5))
        self.percentage_entry = ttk.Entry(percentage_frame, textvariable=self.finished_percentage_var, width=5)
        self.percentage_entry.pack(side=tk.LEFT)
        ToolTip(self.percentage_entry, "Threshold to consider a video 'finished'")
        self.finished_percentage_var.trace("w", self._autosave_settings)

        mpv_playback_frame = ttk.Labelframe(playback_tab, text="MPV Player", padding=10)
        mpv_playback_frame.pack(fill=tk.X, pady=5)
        self._create_check(mpv_playback_frame, "Use MPV for Local Files", self.use_mpv_var, "Use MPV media player for local video files instead of browser.")

        self.custom_settings_frame = ttk.Labelframe(playlist_tab, text="Custom Playlist Settings", padding=10)
        self.custom_settings_frame.pack(fill=tk.X, pady=5)
        self._create_playlist_check(self.custom_settings_frame, "Expand All Playlists at Start", self.expand_playlists_var, "Scrape all videos from all playlists into one single list before starting.")
        self._create_playlist_check(self.custom_settings_frame, "Randomize Main List Order", self.random_list_var, "Randomize the order of items in the main list.")
        self._create_playlist_check(self.custom_settings_frame, "True Random on Skip/End", self.true_random_on_skip_var, "Picks a new random video from the entire pool on every skip/end.")
        self._create_playlist_check(self.custom_settings_frame, "Smart Shuffle (Unwatched First)", self.smart_shuffle_var, "Shuffles unwatched videos first, then plays watched videos.")
        self._create_playlist_check(self.custom_settings_frame, "Shuffle Videos Within Each Playlist", self.shuffle_within_playlists_var, "Shuffle the order of videos inside each playlist as it's played.")
        self._create_playlist_check(self.custom_settings_frame, "Play Playlists Sequentially", self.sequential_playlists_var, "Play each playlist completely before moving to the next item in the list.")
        self._create_playlist_check(self.custom_settings_frame, "Treat Playlists as Single Videos", self.treat_playlists_as_videos_var, "If checked, playlists will not be expanded and will be treated as single videos.")
        
        # --- Audio Tab ---
        audio_device_frame = ttk.Labelframe(audio_tab, text="Audio Input", padding=10)
        audio_device_frame.pack(fill=tk.X, pady=5)
        self.audio_device_menu = ttk.Combobox(audio_device_frame, textvariable=self.audio_device_var, state="readonly")
        self.audio_device_menu.pack(fill=tk.X, expand=True)
        ToolTip(self.audio_device_menu, "Audio Input Device (e.g., Stereo Mix)")
        self.audio_device_menu.bind("<<ComboboxSelected>>", self._autosave_settings)
        
        silence_frame = ttk.Labelframe(audio_tab, text="Silence Detection", padding=10)
        silence_frame.pack(fill=tk.X, pady=5)
        ttk.Label(silence_frame, text="Play next after (min):").pack(side=tk.LEFT, padx=(0, 5))
        self.silence_entry = ttk.Entry(silence_frame, textvariable=self.silence_minutes_var, width=5)
        self.silence_entry.pack(side=tk.LEFT)
        ToolTip(self.silence_entry, "How long to wait after silence before playing the next video")
        
        threshold_frame = ttk.Labelframe(audio_tab, text="Audio Levels", padding=10)
        threshold_frame.pack(fill=tk.X, pady=5)
        self.threshold_slider = self._create_slider_with_label(threshold_frame, "Sound Threshold:", self.sound_threshold_var, 0.1, 2.0, "How loud is 'sound'")
        self.silence_threshold_slider = self._create_slider_with_label(threshold_frame, "Noise Gate (Silence):", self.silence_threshold_var, 0.01, 0.5, "Ignore quiet background noise below this level")
        self.audio_gain_slider = self._create_slider_with_label(threshold_frame, "Audio Gain:", self.audio_gain_var, 0.1, 5.0, "Amplify the input audio signal")

        viz_frame = ttk.Labelframe(audio_tab, text="Visualization Mode", padding=10)
        viz_frame.pack(fill=tk.X, pady=5)
        ttk.Radiobutton(viz_frame, text="Simple Bar", variable=self.visualization_mode_var, value="bar", command=self.switch_visualization).pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(viz_frame, text="Waveform", variable=self.visualization_mode_var, value="waveform", command=self.switch_visualization).pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(viz_frame, text="Spectrum", variable=self.visualization_mode_var, value="spectrum", command=self.switch_visualization).pack(side=tk.LEFT, padx=5)

        # --- Profiles & Paths Tab ---
        profile_management_frame = ttk.Labelframe(profile_tab, text="Profile Management", padding="10")
        profile_management_frame.pack(fill=tk.X, pady=5)
        self.profile_combobox = ttk.Combobox(profile_management_frame, textvariable=self.active_profile_name, state="readonly")
        self.profile_combobox.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)
        ToolTip(self.profile_combobox, "Switch between saved setting profiles")
        self.profile_combobox.bind("<<ComboboxSelected>>", self.on_profile_select)
        ttk.Button(profile_management_frame, text="New", command=self.new_profile, bootstyle="info-outline").pack(side=tk.LEFT, padx=2)
        ttk.Button(profile_management_frame, text="Copy", command=self.copy_profile, bootstyle="info-outline").pack(side=tk.LEFT, padx=2)
        ttk.Button(profile_management_frame, text="Save", command=self.save_profile, bootstyle="success-outline").pack(side=tk.LEFT, padx=2)
        ttk.Button(profile_management_frame, text="Delete", command=self.delete_profile, bootstyle="danger-outline").pack(side=tk.LEFT, padx=2)
        
        paths_frame = ttk.Labelframe(profile_tab, text="Executable & Profile Paths", padding="10")
        paths_frame.pack(fill=tk.X, pady=5)
        chrome_profile_frame = ttk.Frame(paths_frame)
        chrome_profile_frame.pack(fill=tk.X, pady=2)
        ttk.Label(chrome_profile_frame, text="Chrome User Data:", width=18).pack(side=tk.LEFT)
        self.profile_path_entry = ttk.Entry(chrome_profile_frame, textvariable=self.profile_path_var)
        self.profile_path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        # --- START: NEWLY ADDED WIDGET ---
        ttk.Button(chrome_profile_frame, text="Browse", command=lambda: self.browse_folder_path(self.profile_path_var), bootstyle="secondary-outline").pack(side=tk.LEFT)
        # --- END: NEWLY ADDED WIDGET ---
        ToolTip(self.profile_path_entry, "Chrome User Data Directory (e.g., C:\\Users\\...\\AppData\\Local\\Google\\Chrome\\User Data)")
        self.profile_path_var.trace("w", self._autosave_settings)
        
        chrome_name_frame = ttk.Frame(paths_frame)
        chrome_name_frame.pack(fill=tk.X, pady=2)
        ttk.Label(chrome_name_frame, text="Chrome Profile Name:", width=18).pack(side=tk.LEFT)
        self.profile_name_entry = ttk.Entry(chrome_name_frame, textvariable=self.profile_name_var)
        self.profile_name_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ToolTip(self.profile_name_entry, "Chrome Profile Name (e.g., Profile 1)")
        self.profile_name_var.trace("w", self._autosave_settings)

        mpv_path_frame = ttk.Frame(paths_frame)
        mpv_path_frame.pack(fill=tk.X, pady=2)
        ttk.Label(mpv_path_frame, text="MPV Path:", width=18).pack(side=tk.LEFT)
        self.mpv_path_entry = ttk.Entry(mpv_path_frame, textvariable=self.mpv_path_var)
        self.mpv_path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        ToolTip(self.mpv_path_entry, "Path to MPV executable")
        self.mpv_path_var.trace("w", self._autosave_settings)
        ttk.Button(mpv_path_frame, text="Browse", command=self.browse_mpv_path, bootstyle="secondary-outline").pack(side=tk.LEFT)

        # --- Subscriptions Tab ---
        subs_frame = ttk.Labelframe(subscriptions_tab, text="Channel/Folder Subscriptions", padding=10)
        subs_frame.pack(fill=tk.BOTH, expand=True)
        self.subs_tree = ttk.Treeview(subs_frame, columns=("source", "type"), show="headings", height=5)
        self.subs_tree.heading("source", text="Source")
        self.subs_tree.heading("type", text="Type")
        self.subs_tree.pack(fill=tk.BOTH, expand=True, pady=(0,5))
        subs_buttons = ttk.Frame(subs_frame)
        subs_buttons.pack(fill=tk.X)
        ttk.Button(subs_buttons, text="Add", command=self.add_subscription, bootstyle="info-outline").pack(side=tk.LEFT, padx=2)
        ttk.Button(subs_buttons, text="Remove", command=self.remove_subscription, bootstyle="danger-outline").pack(side=tk.LEFT, padx=2)
        ttk.Button(subs_buttons, text="Refresh All", command=self.refresh_subscriptions, bootstyle="success-outline").pack(side=tk.RIGHT, padx=2)


    def _create_check(self, parent_widget, text, var, tip):
        """Creates a checkbutton with a tooltip and autosave command."""
        cb = ttk.Checkbutton(parent_widget, text=text, variable=var, bootstyle="primary", command=self._autosave_settings)
        cb.pack(anchor='w', padx=5, pady=2)
        ToolTip(cb, tip)

    def _create_playlist_check(self, parent_widget, text, var, tip):
        """Creates a playlist-specific checkbutton with a tooltip and autosave command."""
        cb = ttk.Checkbutton(parent_widget, text=text, variable=var, bootstyle="primary", command=self.on_custom_setting_change)
        cb.pack(anchor='w', padx=5, pady=2)
        ToolTip(cb, tip)

    def _create_slider_with_label(self, parent_widget, label_text, variable, from_, to, tip):
        """Creates a labeled slider with a tooltip and autosave command."""
        frame = ttk.Frame(parent_widget)
        frame.pack(fill=tk.X, expand=True, pady=5)
        label = ttk.Label(frame, text=label_text, width=18)
        label.pack(side=tk.LEFT, padx=(0, 10))
        slider = ttk.Scale(frame, from_=from_, to=to, variable=variable, command=self._autosave_settings)
        slider.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ToolTip(slider, tip)
        return slider    

    def initialize_visualization(self):
        """Initialize the audio visualization based on selected mode."""
        self.switch_visualization()

    def switch_visualization(self):
        """Switch between different visualization modes."""
        mode = self.visualization_mode_var.get()
        
        if self.visualization_animation:
            self.visualization_animation.event_source.stop()
            self.visualization_animation = None
        for widget in self.visualization_container.winfo_children():
            widget.destroy()
        
        self.waveform_figure = None
        self.spectrum_figure = None
        self.sound_bar_canvas = None

        if mode == "bar":
            self.sound_bar_canvas = tk.Canvas(self.visualization_container, height=20, 
                                              bg=self.root.style.colors.bg, highlightthickness=0)
            self.sound_bar_canvas.pack(fill=tk.BOTH, expand=True, pady=(20,20))
            self.update_sound_bar()
            
        elif mode == "waveform" and MATPLOTLIB_AVAILABLE:
            self.create_waveform_visualization()
            
        elif mode == "spectrum" and MATPLOTLIB_AVAILABLE:
            self.create_spectrum_visualization()
        else:
            if mode != "bar":
                self.log(f"Matplotlib not available for '{mode}' mode. Falling back to simple bar.", "orange")
                self.visualization_mode_var.set("bar")
                self.root.after(10, self.switch_visualization)

    def create_waveform_visualization(self):
        """Create a real-time waveform visualization."""
        self.waveform_figure = Figure(figsize=(12, 1.5), dpi=80)
        self.waveform_figure.patch.set_facecolor(self.root.style.colors.bg)
        
        self.waveform_ax = self.waveform_figure.add_subplot(111)
        self.waveform_ax.set_facecolor(self.root.style.colors.bg)
        self.waveform_ax.set_ylim([-1.5, 1.5]) 
        self.waveform_ax.set_xlim([0, 4410])
        self.waveform_ax.axis('off')
        self.waveform_figure.tight_layout(pad=0)

        x_data = np.arange(4410)
        y_data = np.zeros(4410)
        
        line_color = self.root.style.colors.success
        self.waveform_line, = self.waveform_ax.plot(x_data, y_data, color=line_color, linewidth=1)
        
        self.waveform_canvas = FigureCanvasTkAgg(self.waveform_figure, master=self.visualization_container)
        self.waveform_canvas.draw()
        self.waveform_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        self.visualization_animation = animation.FuncAnimation(
            self.waveform_figure, self.update_waveform, interval=50, cache_frame_data=False
        )

    def create_spectrum_visualization(self):
        """Create a frequency spectrum visualization."""
        self.spectrum_figure = Figure(figsize=(12, 1.5), dpi=80)
        self.spectrum_figure.patch.set_facecolor(self.root.style.colors.bg)
        
        self.spectrum_ax = self.spectrum_figure.add_subplot(111)
        self.spectrum_ax.set_facecolor(self.root.style.colors.bg)
        self.spectrum_ax.set_ylim([0, 50])
        self.spectrum_ax.set_xlim([-1, 20])
        self.spectrum_ax.axis('off')
        self.spectrum_figure.tight_layout(pad=0)

        x_pos = np.arange(20)
        heights = np.zeros(20)
        
        bar_color = self.root.style.colors.primary
        self.spectrum_bars = self.spectrum_ax.bar(x_pos, heights, color=bar_color, width=0.8)
        
        self.spectrum_canvas = FigureCanvasTkAgg(self.spectrum_figure, master=self.visualization_container)
        self.spectrum_canvas.draw()
        self.spectrum_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        self.visualization_animation = animation.FuncAnimation(
            self.spectrum_figure, self.update_spectrum, interval=50, cache_frame_data=False
        )

    def update_waveform(self, frame):
        """Update the waveform visualization."""
        if len(self.audio_buffer) > 0:
            audio_data = np.array(list(self.audio_buffer))
            
            if len(audio_data) < 4410:
                audio_data = np.pad(audio_data, (0, 4410 - len(audio_data)), 'constant')
            else:
                audio_data = audio_data[-4410:]
            
            self.waveform_line.set_ydata(audio_data)
            
            max_val = np.max(np.abs(audio_data)) if audio_data.size > 0 else 0
            if max_val > self.sound_threshold_var.get():
                line_color = self.root.style.colors.success
            elif max_val < self.silence_threshold_var.get():
                line_color = self.root.style.colors.danger
            else:
                line_color = self.root.style.colors.warning
            
            self.waveform_line.set_color(line_color)
            
            if self.waveform_canvas:
                self.waveform_canvas.draw()
        
        return [self.waveform_line]

    def update_spectrum(self, frame):
        """Update the frequency spectrum visualization."""
        if len(self.audio_buffer) > 1024:
            audio_data = np.array(list(self.audio_buffer))
            
            fft_data = np.fft.rfft(audio_data[-1024:])
            fft_magnitude = np.abs(fft_data)
            
            num_bands = 20
            bands = np.array_split(fft_magnitude, num_bands)
            band_levels = [np.mean(band) * 100 for band in bands]
            
            for bar, height in zip(self.spectrum_bars, band_levels):
                current_height = bar.get_height()
                new_height = max(0, current_height * 0.6 - 2, height * 0.4) 
                bar.set_height(min(new_height, 50))
                
                if new_height > 35:
                    bar.set_color(self.root.style.colors.danger)
                elif new_height > 20:
                    bar.set_color(self.root.style.colors.warning)
                else:
                    bar.set_color(self.root.style.colors.success)
            
            if self.spectrum_canvas:
                self.spectrum_canvas.draw()
        
        return self.spectrum_bars

    def update_visualization_theme(self):
        """Update visualization colors when theme changes."""
        self.switch_visualization()

    def update_silence_indicator(self, is_silence):
        """Update the silence detection indicator UI element."""
        if is_silence:
            self.silence_indicator.config(text="🔇 SILENCE DETECTED", bootstyle="danger")
        else:
            self.silence_indicator.config(text="🔊 AUDIO ACTIVE", bootstyle="success")

    def update_flicker_free_indicator(self):
        """FIX: Debounced logic to prevent rapid flickering of the silence indicator."""
        now = time.time()
        
        if not self.current_indicator_state and (now - self.last_sound_time > self.silence_debounce_time):
            self.current_indicator_state = True 
            self.update_silence_indicator(True)
            
        elif self.current_indicator_state and (now - self.last_silence_time > self.silence_debounce_time):
            self.current_indicator_state = False
            self.update_silence_indicator(False)

        self.root.after(100, self.update_flicker_free_indicator) 

    def set_placeholder_thumbnail(self):
        """Creates a default placeholder image for the Now Playing card."""
        color = getattr(self.root.style.colors, 'secondary', '#888')
        placeholder = Image.new('RGB', (120, 90), color)
        draw = ImageDraw.Draw(placeholder)
        text = "No Video"
        text_color = getattr(self.root.style.colors, 'fg', '#fff')
        draw.text((60, 45), text, fill=text_color, anchor="mm")
        self.now_playing_thumbnail_photo = ImageTk.PhotoImage(placeholder)
        self.now_playing_thumbnail_label.config(image=self.now_playing_thumbnail_photo)

    def toggle_log(self):
        """Shows or hides the log text widget."""
        if self.log_visible.get():
            self.log_text.pack_forget()
            self.toggle_log_btn.config(text="Show Logs ▼")
            self.log_visible.set(False)
        else:
            self.log_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
            self.toggle_log_btn.config(text="Hide Logs ▲")
            self.log_visible.set(True)

    def filter_treeview(self, *args):
        """Filters the main URL treeview based on the search query."""
        query = self.search_var.get().lower()
        
        self.url_tree.delete(*self.url_tree.get_children())
        
        for item in self.all_tree_items:
            if 'type:' in query:
                if item['type'].lower() != query.split('type:')[1].strip():
                    continue
            if 'watched:true' in query:
                if self.get_saved_timestamp_status(item['url']) != "finished":
                    continue
            elif 'watched:false' in query:
                if self.get_saved_timestamp_status(item['url']) == "finished":
                    continue

            title = item['title'].lower()
            url = item['url'].lower()
            if query.split('type:')[0].split('watched:')[0].strip() in title or query.split('type:')[0].split('watched:')[0].strip() in url:
                self.url_tree.insert("", tk.END, values=(item['title'], item['url'], item['type']))

    def play_next(self):
        """Moves the selected item to the top of the queue to be played next."""
        selected_items = self.url_tree.selection()
        if not selected_items:
            return
        
        selected_id = selected_items[0]
        selected_url = self.url_tree.item(selected_id, 'values')[1]

        item_to_move = None
        for i, item in enumerate(self.all_tree_items):
            if item['url'] == selected_url:
                item_to_move = self.all_tree_items.pop(i)
                break
        
        if item_to_move:
            if self.is_monitoring:
                self.main_queue.insert(self.main_queue_index + 1, item_to_move['url'])
                self.log(f"'{self.get_display_name(item_to_move['url'])}' will play next.", "blue")
            else:
                self.all_tree_items.insert(0, item_to_move)
                self.filter_treeview() 
                self.log(f"Moved '{self.get_display_name(item_to_move['url'])}' to the top of the list.", "blue")

    def mark_as_watched(self):
        """Manually marks the selected video as finished."""
        selected_item = self.url_tree.selection()
        if not selected_item:
            return
        
        item_id = selected_item[0]
        url = self.url_tree.item(item_id, 'values')[1]
        clean_url = self._clean_url(url)
        
        today = date.today().isoformat()
        if today not in self.stats:
            self.stats[today] = {'timestamps': {}}
        
        self.stats[today].setdefault('timestamps', {})[clean_url] = -1
        self.save_stats()
        self.update_item_status_in_treeview(url)
        self.log(f"Marked '{self.get_display_name(url)}' as watched.", "blue")

    def mark_as_unwatched(self):
        """Manually marks the selected video as not finished."""
        selected_item = self.url_tree.selection()
        if not selected_item:
            return
        
        item_id = selected_item[0]
        url = self.url_tree.item(item_id, 'values')[1]
        clean_url = self._clean_url(url)
        
        for day, data in self.stats.items():
            if isinstance(data, dict) and 'timestamps' in data:
                if clean_url in data['timestamps']:
                    del data['timestamps'][clean_url]
                    
        self.save_stats()
        self.update_item_status_in_treeview(url)
        self.log(f"Marked '{self.get_display_name(url)}' as unwatched.", "blue")

    def on_playlist_mode_change(self, event=None):
        """Applies settings based on the selected quick mode and enables/disables custom checkboxes."""
        new_mode = self.playlist_mode_var.get()

        # --- START: NEW DYNAMIC CHANGE LOGIC ---
        if self.is_monitoring:
            if new_mode == "True Random":
                messagebox.showinfo(
                    "Mode Change Required",
                    "'True Random' mode cannot be switched to during playback.\nPlease stop and start again to use this mode.",
                    parent=self.root
                )
                # Revert the dropdown to the previous selection
                self.playlist_mode_var.set(self.previous_playlist_mode)
                return
            
            # If monitoring and not True Random, rebuild the queue
            self.rebuild_queue_dynamically(new_mode)
        
        self.previous_playlist_mode = new_mode
        # --- END: NEW DYNAMIC CHANGE LOGIC ---
        
        # This part remains the same: enable/disable checkboxes based on mode
        if self.custom_settings_frame:
            if new_mode == "Custom":
                for child in self.custom_settings_frame.winfo_children():
                    child.config(state=tk.NORMAL)
            else:
                for child in self.custom_settings_frame.winfo_children():
                    child.config(state=tk.DISABLED)

        if new_mode != "Custom":
            settings = {
                'expand_playlists': False, 'random_list': False,
                'true_random_on_skip': False, 'smart_shuffle': False,
                'shuffle_within_playlists': False, 'sequential_playlists': False
            }
            
            if new_mode == "Sequential":
                settings['sequential_playlists'] = True
                settings['expand_playlists'] = True
            elif new_mode == "Shuffle All":
                settings['expand_playlists'] = True
                settings['random_list'] = True
            elif new_mode == "True Random":
                settings['true_random_on_skip'] = True
            elif new_mode == "Smart Shuffle":
                settings['smart_shuffle'] = True
                
            self.expand_playlists_var.set(settings['expand_playlists'])
            self.random_list_var.set(settings['random_list'])
            self.true_random_on_skip_var.set(settings['true_random_on_skip'])
            self.smart_shuffle_var.set(settings['smart_shuffle'])
            self.shuffle_within_playlists_var.set(settings['shuffle_within_playlists'])
            self.sequential_playlists_var.set(settings['sequential_playlists'])

    def rebuild_queue_dynamically(self, new_mode):
        """Rebuilds the upcoming song queue when the playlist mode is changed during playback."""
        self.log(f"Dynamically changing playlist mode to: {new_mode}", "blue")

        # Get the full, original list of URLs in their visual order
        original_urls = [item['url'] for item in self.all_tree_items]
        
        # If the current queue is empty or something is wrong, abort.
        if not self.main_queue or not self.current_url:
            self.log("Cannot rebuild queue: playback not in a valid state.", "orange")
            return

        # Preserve the currently playing song and what has already been played
        played_urls = self.main_queue[:self.main_queue_index]
        upcoming_urls = []

        # --- Determine the new list of upcoming songs based on the selected mode ---
        if new_mode == "Sequential":
            # Find the current song in the original, sequential list
            try:
                current_original_index = original_urls.index(self.current_url)
                # The new upcoming list is everything after the current song in the original order
                upcoming_urls = original_urls[current_original_index + 1:]
            except ValueError:
                # Fallback: if current song isn't in the main list, just use what's left in the queue
                upcoming_urls = self.main_queue[self.main_queue_index + 1:]

        elif new_mode in ["Shuffle All", "Smart Shuffle"]:
            # For shuffle modes, we shuffle everything that hasn't been played yet.
            # This includes the current song's original position and everything after.
            try:
                current_original_index = original_urls.index(self.current_url)
                # Pool of songs to be shuffled = everything from the current song onwards in the original list
                shuffle_pool = original_urls[current_original_index + 1:]
                random.shuffle(shuffle_pool)
                upcoming_urls = shuffle_pool
            except ValueError:
                # Fallback: if current song isn't in the main list, just shuffle what's left in the queue
                upcoming_urls = self.main_queue[self.main_queue_index + 1:]
                random.shuffle(upcoming_urls)
        
        else: # For "Custom" or other modes, we don't change the order
            upcoming_urls = self.main_queue[self.main_queue_index + 1:]


        # --- Assemble the new queue ---
        # The new queue is [what was played] + [current song] + [newly ordered upcoming songs]
        self.main_queue = played_urls + [self.current_url] + upcoming_urls
        
        # The index of the current song doesn't change in this new structure
        # self.main_queue_index remains the same.

        self.log(f"Upcoming queue rebuilt with {len(upcoming_urls)} songs.", "green")
        self.update_playlist_info() # Refresh the UI to show the new queue length/order

    def on_custom_setting_change(self, *args):
        """Switches the mode to 'Custom' and re-enables checkboxes."""
        self.playlist_mode_var.set("Custom")
        self.on_playlist_mode_change()
        
    def on_drag_start(self, event):
        """Records the item being dragged."""
        item = self.url_tree.identify_row(event.y)
        if item:
            self._drag_data["item"] = item
            self._drag_data["y"] = event.y
            
    def on_drag_motion(self, event):
        """Moves the dragged item as the mouse moves."""
        if not self._drag_data["item"]:
            return

        y = event.y
        target_item = self.url_tree.identify_row(y)
        
        if target_item and target_item != self._drag_data["item"]:
            self.url_tree.move(self._drag_data["item"], self.url_tree.parent(target_item), self.url_tree.index(target_item))

    def on_drag_release(self, event):
        """Finalizes the drag and drop operation."""
        if self._drag_data["item"]:
            self.all_tree_items = self.get_items_from_display()
        self._drag_data["item"] = None
        self._drag_data["y"] = 0
            
    def update_percentage_label(self, value):
        self.percentage_label.config(text=f"{float(value):.1f}%")

    def is_browser_responsive(self):
        """Checks if the browser instance is still alive and responding."""
        if not self.browser:
            return False
        try:
            _ = self.browser.window_handles
            return True
        except WebDriverException:
            return False

    def view_stats(self):
        """Displays a window with the monitoring statistics."""
        stats_window = ttk.Toplevel(self.root)
        stats_window.title("Playing Statistics")
        stats_window.transient(self.root)
        stats_window.grab_set()

        stats_geometry = getattr(self, 'stats_window_geometry', None)
        if stats_geometry:
            try:
                stats_window.geometry(stats_geometry)
            except tk.TclError:
                width = 800; height = 600
                x = (stats_window.winfo_screenwidth() // 2) - (width // 2)
                y = (stats_window.winfo_screenheight() // 2) - (height // 2)
                stats_window.geometry(f"{width}x{height}+{x}+{y}")
        else:
            width = 800; height = 600
            x = (stats_window.winfo_screenwidth() // 2) - (width // 2)
            y = (stats_window.winfo_screenheight() // 2) - (height // 2)
            stats_window.geometry(f"{width}x{height}+{x}+{y}")

        def on_stats_window_close():
            try:
                self.stats_window_geometry = stats_window.geometry()
                self.save_profile()
            except tk.TclError:
                pass
            stats_window.destroy()
        
        stats_window.protocol("WM_DELETE_WINDOW", on_stats_window_close)

        main_stats_frame = ttk.Frame(stats_window, padding=10)
        main_stats_frame.pack(fill=tk.BOTH, expand=True)

        notebook = ttk.Notebook(main_stats_frame)
        notebook.pack(fill=tk.BOTH, expand=True)

        daily_breakdown_tab = ttk.Frame(notebook, padding=10)
        notebook.add(daily_breakdown_tab, text="Daily Breakdown")
        
        header_label = ttk.Label(daily_breakdown_tab, text="DAILY PLAYING BREAKDOWN", 
                                font=(get_japanese_font(), 16, 'bold'))
        header_label.pack(pady=(0, 20))
        
        table_frame = ttk.Frame(daily_breakdown_tab)
        table_frame.pack(fill=tk.BOTH, expand=True)
        
        columns = ("Date", "Time", "Visual")
        tree = ttk.Treeview(table_frame, columns=columns, show="headings", height=15)
        
        tree.heading("Date", text="Date")
        tree.heading("Time", text="Time")
        tree.heading("Visual", text="Visual")
        
        tree.column("Date", width=120, anchor='center')
        tree.column("Time", width=120, anchor='center')
        tree.column("Visual", width=400, anchor='w')
        
        scrollbar = ttk.Scrollbar(table_frame, orient=tk.VERTICAL, command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        has_daily_data = any(isinstance(data, dict) and day != 'url_stats' for day, data in self.stats.items())
        
        if has_daily_data:
            sorted_days = sorted([day for day in self.stats.keys() if day != 'url_stats' and isinstance(self.stats[day], dict)], reverse=True)
            
            max_time = max(data.get('total_monitored_time', 0) for day, data in self.stats.items() 
                          if isinstance(data, dict) and day != 'url_stats') if sorted_days else 1
            
            for day in sorted_days:
                data = self.stats[day]
                total_time = data.get('total_monitored_time', 0)
                hours = int(total_time // 3600)
                minutes = int((total_time % 3600) // 60)
                time_str = f"{hours}h {minutes}m"
                bar_length = int((total_time / max_time) * 40) if max_time > 0 else 0
                visual_bar = "█" * bar_length
                tree.insert("", tk.END, values=(day, time_str, visual_bar))
        else:
            tree.insert("", tk.END, values=("No data", "0h 0m", ""))

        overview_tab = ttk.Frame(notebook, padding=10)
        notebook.add(overview_tab, text="Overview")
        
        if has_daily_data:
            overview_header = ttk.Label(overview_tab, text="LIFETIME PLAYING OVERVIEW", 
                                       font=(get_japanese_font(), 16, 'bold'))
            overview_header.pack(pady=(0, 30))
            
            total_days = len([day for day in self.stats.keys() if day != 'url_stats' and isinstance(self.stats[day], dict)])
            total_time_all = sum(data.get('total_monitored_time', 0) for data in self.stats.values() if isinstance(data, dict))
            
            total_hours = int(total_time_all // 3600)
            total_minutes = int((total_time_all % 3600) // 60)
            total_seconds = int(total_time_all % 60)
            
            avg_time_per_day = total_time_all / total_days if total_days > 0 else 0
            avg_hours = int(avg_time_per_day // 3600)
            avg_minutes = int((avg_time_per_day % 3600) // 60)
            avg_seconds = int(avg_time_per_day % 60)
            
            stats_main_frame = ttk.Frame(overview_tab)
            stats_main_frame.pack(fill=tk.X, padx=50)
            
            def create_stat_row(parent, label, value):
                row_frame = ttk.Frame(parent)
                row_frame.pack(fill=tk.X, pady=10)
                label_widget = ttk.Label(row_frame, text=label + ":", font=(get_japanese_font(), 12))
                label_widget.pack(side=tk.LEFT)
                value_widget = ttk.Label(row_frame, text=value, font=(get_japanese_font(), 12))
                value_widget.pack(side=tk.RIGHT)
            
            create_stat_row(stats_main_frame, "Total Time Played", f"{total_hours}h {total_minutes}m {total_seconds}s")
            create_stat_row(stats_main_frame, "Average Time Per Day", f"{avg_hours}h {avg_minutes}m {avg_seconds}s")
            create_stat_row(stats_main_frame, "Total Days Tracked", str(total_days))
            
        else:
            ttk.Label(overview_tab, text="No statistics available yet.\nStart using the app to generate some data!", 
                      font=(get_japanese_font(), 12), bootstyle="info").pack(pady=20, padx=10)
        
        if MATPLOTLIB_AVAILABLE:
            calendar_tab = ttk.Frame(notebook, padding=10)
            notebook.add(calendar_tab, text="Contribution Calendar")
            self._create_contribution_calendar_in_tab(calendar_tab)
        else:
            self.log("Matplotlib/Seaborn not found, contribution calendar tab disabled.", "orange")

        notebook.select(daily_breakdown_tab)
        stats_window.wait_window()

    def _create_contribution_calendar_in_tab(self, parent_tab):
        """Creates and embeds a GitHub-style contribution calendar using seaborn."""
        has_data = any(isinstance(data, dict) and day != 'url_stats' for day, data in self.stats.items())

        if not has_data:
            ttk.Label(parent_tab, text="No activity data to display.",
                      font=(get_japanese_font(), 12), bootstyle="info").pack(pady=20, padx=10)
            return

        try:
            def create_calendar_heatmap():
                data = {
                    date.fromisoformat(day): data.get('total_monitored_time', 0) / 3600.0
                    for day, data in self.stats.items()
                    if isinstance(data, dict) and day != 'url_stats'
                }
                if not data: return None
                all_days = pd.Series(data)
                all_days.index = pd.to_datetime(all_days.index)

                end_date = date.today()
                start_date = end_date - timedelta(days=365)
                start_date_aligned = start_date - timedelta(days=start_date.weekday())
                end_date_aligned = end_date + timedelta(days=(6 - end_date.weekday()))
                date_range = pd.date_range(start=start_date_aligned, end=end_date_aligned)
                all_days = all_days.reindex(date_range, fill_value=0)

                all_days_df = pd.DataFrame({'date': all_days.index, 'hours': all_days.values})
                all_days_df['hours'] = pd.to_numeric(all_days_df['hours'], errors='coerce').fillna(0)
                all_days_df['weekday'] = all_days_df['date'].dt.weekday
                all_days_df['unique_week'] = all_days_df['date'].dt.strftime('%Y-%W')

                heatmap_data = all_days_df.pivot_table(
                    index='weekday', columns='unique_week', values='hours', fill_value=0
                )

                bg_color = self.root.style.colors.bg
                fg_color = self.root.style.colors.fg

                fig, ax = plt.subplots(figsize=(10, 2.5), dpi=100)
                fig.patch.set_facecolor(bg_color)
                ax.set_facecolor(bg_color)

                sns.heatmap(heatmap_data, ax=ax, cmap="Greens", cbar=True, linewidths=.5, linecolor=bg_color,
                            cbar_kws={'label': 'Hours Played', 'orientation': 'vertical'})

                ax.set_title('Playing Activity Last Year', color=fg_color)
                ax.set_ylabel('Day of Week', color=fg_color)
                ax.set_xlabel('')
                ax.set_yticklabels(['Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat', 'Sun'], rotation=0, color=fg_color)

                month_ticks = []; month_labels = []; last_month = -1
                for i, week_str in enumerate(heatmap_data.columns):
                    try:
                        first_day_of_week = pd.to_datetime(week_str + '-1', format='%Y-%W-%w')
                        current_month = first_day_of_week.month
                        if current_month != last_month:
                            month_ticks.append(i + 0.5)
                            month_labels.append(first_day_of_week.strftime("%b '%y"))
                            last_month = current_month
                    except (ValueError, IndexError): continue
                
                ax.set_xticks(month_ticks)
                ax.set_xticklabels(month_labels, rotation=30, ha='right', color=fg_color, fontsize=9)
                ax.tick_params(axis='x', length=0)
                ax.tick_params(axis='y', length=0)

                cbar = ax.collections[0].colorbar
                cbar.ax.yaxis.label.set_color(fg_color)
                cbar.ax.tick_params(colors=fg_color)

                plt.tight_layout()
                return fig

            fig = create_calendar_heatmap()
            if fig:
                canvas = FigureCanvasTkAgg(fig, master=parent_tab)
                canvas_widget = canvas.get_tk_widget()
                canvas_widget.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
                canvas.draw()
            else:
                ttk.Label(parent_tab, text="No valid data to display in calendar.",
                          font=(get_japanese_font(), 12), bootstyle="info").pack(pady=20, padx=10)

        except Exception as e:
            error_msg = f"Error creating contribution calendar: {str(e)}"
            ttk.Label(parent_tab, text=error_msg, font=(get_japanese_font(), 10), 
                     bootstyle="danger", wraplength=400).pack(pady=20, padx=10)
            self.log(f"Contribution calendar creation error: {e}", "red")
            self.log(traceback.format_exc(), "red")
            
    def update_countdown_display(self, remaining_time):
        """Updates the countdown timer label in the UI."""
        if remaining_time > 0:
            self.countdown_var.set(f"Next video in {int(remaining_time)}s...")
        else:
            self.countdown_var.set("")
            
    def add_url_to_treeview(self, event=None):
        url = self.video_link_entry.get().strip()
        if not url: messagebox.showerror("Invalid Input", "Video Link cannot be empty."); return
        self.add_url_to_list(url)
        self.video_link_entry.delete(0, tk.END)
        self.video_link_entry.focus_set()
        self.video_link_entry.select_range(0, tk.END)

    def add_folder_to_treeview(self):
        folder_path = filedialog.askdirectory(title="Select Folder with Video Files")
        if not folder_path: return
        video_extensions = {'.mp4', '.mkv', '.avi', '.mov', '.wmv', '.flv', '.webm', '.m4v'}
        video_files = []
        try:
            if self.recursive_folder_var.get():
                for root_dir, _, files in os.walk(folder_path):
                    for file in files:
                        if any(file.lower().endswith(ext) for ext in video_extensions): video_files.append(os.path.join(root_dir, file))
            else:
                for file in os.listdir(folder_path):
                    if any(file.lower().endswith(ext) for ext in video_extensions): video_files.append(os.path.join(folder_path, file))
            if not video_files: messagebox.showinfo("No Videos Found", f"No video files found in '{folder_path}'."); return
            video_files.sort()
            for video_file in video_files: self.add_url_to_list(video_file)
            self.log(f"Added {len(video_files)} files from {folder_path}", 'green')
        except Exception as e: self.log(f"Error adding folder: {e}", 'red'); messagebox.showerror("Error", f"Failed to add folder: {e}")

    def browse_file(self):
        filetypes = [("Video files", "*.mp4 *.mkv *.avi *.mov *.webm"), ("All files", "*.*")]
        file_path = filedialog.askopenfilename(title="Select Video File", filetypes=filetypes)
        if file_path: self.video_link_entry.delete(0, tk.END); self.video_link_entry.insert(0, file_path)

    def remove_selected_url(self):
        selected_items = self.url_tree.selection()
        if not selected_items: messagebox.showinfo("No Selection", "Please select a URL to remove."); return
        
        # CORRECTED: Get URL from index [2] instead of [1]
        urls_to_remove = {self.url_tree.item(item, 'values')[2] for item in selected_items}
        
        # This part remains the same
        for item in selected_items:
            self.url_tree.delete(item)
            
        self.all_tree_items = [item for item in self.all_tree_items if item['url'] not in urls_to_remove]
        self.update_playlist_ui()
        self.log(f"Removed {len(selected_items)} URL(s).", 'blue')

    def save_playlist(self):
        """Saves the current list of URLs from the Treeview to a JSON file."""
        items_to_save = self.get_items_from_display()
        if not items_to_save:
            messagebox.showinfo("Empty List", "There are no URLs in the list to save.")
            return

        file_path = filedialog.asksaveasfilename(
            title="Save Playlist As",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            defaultextension=".json"
        )
        if not file_path:
            return

        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                json.dump(items_to_save, f, indent=4, ensure_ascii=False)
            self.log(f"Playlist saved successfully to {os.path.basename(file_path)}", "green")
        except Exception as e:
            self.log(f"Error saving playlist: {e}", "red")
            messagebox.showerror("Save Error", f"Failed to save the playlist.\n\n{e}")

    def load_playlist(self):
        """Loads a list of URLs from a JSON file into the Treeview."""
        file_path = filedialog.askopenfilename(
            title="Load Playlist",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not file_path:
            return

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                loaded_items = json.load(f)
            
            if not isinstance(loaded_items, list) or not all('url' in item for item in loaded_items):
                raise ValueError("Invalid playlist file format.")

            self.url_tree.delete(*self.url_tree.get_children())
            self.all_tree_items.clear()
            for item in loaded_items:
                title = item.get('title', os.path.basename(item['url']))
                url = item['url']
                url_type = item.get('type', self.get_url_type(url))
                self.url_tree.insert("", tk.END, values=(title, url, url_type))
                self.all_tree_items.append({'title': title, 'url': url, 'type': url_type})
            
            self.update_playlist_ui()
            self.log(f"Playlist loaded successfully from {os.path.basename(file_path)}", "green")
        except Exception as e:
            self.log(f"Error loading playlist: {e}", "red")
            messagebox.showerror("Load Error", f"Failed to load the playlist.\n\n{e}")

    def clear_all_urls(self):
        """Removes all items from the playlist."""
        if not self.all_tree_items:
            return
        if messagebox.askyesno("Confirm Clear", "Are you sure you want to remove all items from the playlist?"):
            self.url_tree.delete(*self.url_tree.get_children())
            self.all_tree_items.clear()
            self.update_playlist_ui()
            self.log("Playlist cleared", "orange")
    
    def start_monitoring_with_resume(self):
        self.show_loading_dialog_for_start(from_beginning=False)

    def pause_monitoring(self, sync_only=False):
        if self.is_monitoring and not self.is_paused:
            self.is_paused = True; self.pause_start_time = time.time()
            self.set_button_states('paused')
            self.log("Playback paused.", 'orange')
            
            if not sync_only:
                if self.mpv_process: self.control_mpv("pause")
                elif self.browser: self.control_video_playback("pause")

            self.save_current_timestamp(); self.save_stats()
            self.update_countdown_display(-1)

    def stop_monitoring(self):
        if not self.is_monitoring: return
        self.log("Pausing player before stopping...", "blue")
        if self.mpv_process: self.control_mpv("pause")
        elif self.browser:
            try: self.control_video_playback("pause")
            except WebDriverException: pass 
        time.sleep(0.5)
        self.update_player_geometries()
        self.is_monitoring = False
        self.log("Stopping playback...", 'blue')
        self.save_app_state(); self.save_current_timestamp()
        if self.monitor_thread and self.monitor_thread.is_alive(): self.monitor_thread.join(timeout=2.0)
        if self.mpv_process: self.mpv_process.terminate(); self.mpv_process = None
        if self.browser and not self.keep_browser_open_var.get(): self.browser.quit(); self.browser = None
        self.save_stats(); self.set_button_states('idle')
        self.update_countdown_display(-1)
        self.update_window_title()

        # Hide Now Playing card
        self.now_playing_title_var.set("Nothing Playing")
        self.now_playing_progress_var.set(0)
        self.set_placeholder_thumbnail()

    def start_monitoring_from_beginning(self):
        self.show_loading_dialog_for_start(from_beginning=True)

    def add_subscription(self):
        """Adds a new subscription."""
        source = simpledialog.askstring("Add Subscription", "Enter a YouTube/Bilibili channel URL or a local folder path:", parent=self.root)
        if not source:
            return
        
        sub_type = "Channel" if source.startswith("http") else "Folder"
        self.subscriptions.append({"source": source, "type": sub_type})
        self.update_subscriptions_display()
        self.save_app_state()

    def start_audio_preview(self):
        """Starts a persistent audio stream to detect prolonged silence."""
        def audio_preview_thread_func():
            current_device_name = None
            stream = None
            while True:
                try:
                    selected_device_name = self.audio_device_var.get()
                    if selected_device_name != current_device_name and stream:
                        stream.stop(ignore_errors=True); stream.close(ignore_errors=True); stream = None
                        self.log(f"Audio device changed to {selected_device_name}. Restarting stream.", "blue")

                    if not stream and selected_device_name and "No devices" not in selected_device_name:
                        current_device_name = selected_device_name
                        device_id = self.audio_devices.get(current_device_name)

                        def preview_callback(indata, frames, time_info, status):
                            if status: self.log(f"Audio stream status: {status}", "orange")

                            scaled_indata = indata * self.audio_gain_var.get()
                            volume_norm = np.linalg.norm(scaled_indata)

                            self.audio_level = max(self.audio_level * 0.8, volume_norm * 50)
                            
                            if self.visualization_mode_var.get() in ["waveform", "spectrum"]:
                                mono_data = np.mean(indata, axis=1) if len(indata.shape) > 1 else indata.flatten()
                                self.audio_buffer.extend(mono_data * self.audio_gain_var.get())
                            
                            if volume_norm < self.silence_threshold_var.get():
                                self.last_silence_time = time.time()
                            else:
                                self.last_sound_time = time.time()

                            silence_threshold_seconds = self.silence_minutes_var.get() * 60

                            if volume_norm < self.silence_threshold_var.get():
                                if self.silence_start_time is None:
                                    self.silence_start_time = time.time()
                                else:
                                    elapsed_silence = time.time() - self.silence_start_time
                                    remaining_time = silence_threshold_seconds - elapsed_silence

                                    if time.time() - self.last_countdown_update > 0.5:
                                        self.root.after(0, self.update_countdown_display, remaining_time)
                                        self.last_countdown_update = time.time()

                                    if remaining_time <= 0:
                                        self.root.after(0, self.update_countdown_display, -1)
                                        if self.afk_enabled_var.get() and self.is_afk:
                                            self.log("AFK detected, will not start/advance on silence.", "orange")
                                            self.silence_start_time = time.time()
                                        else:
                                            if self.is_monitoring and not self.is_paused:
                                                minutes = self.silence_minutes_var.get()
                                                self.log(f"Silence detected for over {minutes} min. Advancing video.", 'green')
                                                self.root.after(0, self.handle_silence_trigger)
                                            elif not self.is_monitoring:
                                                minutes = self.silence_minutes_var.get()
                                                self.log(f"Silence detected for over {minutes} min. Starting playback.", 'green')
                                                self.root.after(0, self.start_monitoring_with_resume)
                                            
                                            self.silence_start_time = None 
                            else: 
                                if self.silence_start_time is not None:
                                    self.root.after(0, self.update_countdown_display, -1)
                                self.silence_start_time = None

                            if self.is_monitoring and not self.is_paused:
                                if not self.monitored_time_started and volume_norm > self.sound_threshold_var.get():
                                    self.monitoring_start_time = time.time()
                                    self.last_stats_update_time = time.time()
                                    self.monitored_time_started = True
                                    self.log("First sound detected, starting timer.", "green")
                                    self.root.after(0, self.update_timer)


                        stream = sd.InputStream(device=device_id, callback=preview_callback, samplerate=44100)
                        stream.start()
                        self.log(f"Audio preview started on: {current_device_name}", "cyan")
                
                except Exception as e:
                    self.log(f"Audio preview stream error: {e}", "red")
                    self.audio_level = 0
                    if stream: stream.stop(ignore_errors=True); stream.close(ignore_errors=True)
                    stream = None; current_device_name = None 
                    time.sleep(2) 
                time.sleep(0.5)
        threading.Thread(target=audio_preview_thread_func, daemon=True).start()

    def set_status(self, text):
        """Safely sets the status label text from any thread."""
        self.status_label.config(text=text)
        if not self.is_afk:
            self.pre_afk_status_text = text

    def start_afk_detector(self):
        """Starts a background thread to monitor for user inactivity (AFK)"""

        def afk_thread_func():
            was_afk = False
            if sys.platform == "win32":
                class LASTINPUTINFO(ctypes.Structure):
                    _fields_ = [("cbSize", wintypes.UINT), ("dwTime", wintypes.DWORD)]
                user32 = ctypes.windll.user32; kernel32 = ctypes.windll.kernel32
                get_last_input_info = user32.GetLastInputInfo; get_last_input_info.restype = wintypes.BOOL; get_last_input_info.argtypes = [ctypes.POINTER(LASTINPUTINFO)]
                get_tick_count = kernel32.GetTickCount; get_tick_count.restype = wintypes.DWORD
                self.log("Using Windows API for AFK detection.", "cyan")
                while True:
                    try:
                        if self.afk_enabled_var.get():
                            liinfo = LASTINPUTINFO(); liinfo.cbSize = ctypes.sizeof(liinfo)
                            if get_last_input_info(ctypes.byref(liinfo)):
                                idle_time_sec = (get_tick_count() - liinfo.dwTime) / 1000.0
                                self.is_afk = idle_time_sec > (self.afk_timeout_minutes_var.get() * 60)
                        else: self.is_afk = False
                        
                        if self.is_afk and not was_afk:
                            if self.is_monitoring and not self.is_paused:
                                self.log("User is now AFK. Pausing playback.", "orange")
                                self.root.after(0, self.pause_monitoring)
                            else:
                                self.log("User is now AFK. Autoplay is paused.", "orange")
                            
                            if self.show_afk_status_var.get():
                                self.pre_afk_status_text = self.status_label.cget("text")
                                self.root.after(0, self.set_status, "Status: AFK (Playback Paused)")
                            self.root.after(0, self.update_tray_icon_state)
                            was_afk = True

                        elif not self.is_afk and was_afk:
                            self.log("User activity detected. Resuming normal operation.", "green")
                            if self.show_afk_status_var.get(): self.root.after(0, self.set_status, self.pre_afk_status_text)
                            self.root.after(0, self.update_tray_icon_state)
                            was_afk = False
                    except Exception as e: self.log(f"Error in Windows AFK detector: {e}", "red")
                    time.sleep(5)
                return
            if pynput_mouse and pynput_keyboard:
                self.log("Using pynput for AFK detection.", "cyan")
                def on_activity(*args): self.last_input_time = time.time()
                mouse_listener = pynput_mouse.Listener(on_move=on_activity, on_click=on_activity, on_scroll=on_activity)
                keyboard_listener = pynput_keyboard.Listener(on_press=on_activity)
                mouse_listener.start(); keyboard_listener.start()
                while True:
                    try:
                        if self.afk_enabled_var.get(): self.is_afk = (time.time() - self.last_input_time) > (self.afk_timeout_minutes_var.get() * 60)
                        else: self.is_afk = False

                        if self.is_afk and not was_afk:
                            if self.is_monitoring and not self.is_paused:
                                self.log("User is now AFK. Pausing playback.", "orange")
                                self.root.after(0, self.pause_monitoring)
                            else:
                                self.log("User is now AFK. Autoplay is paused.", "orange")

                            if self.show_afk_status_var.get():
                                self.pre_afk_status_text = self.status_label.cget("text")
                                self.root.after(0, self.set_status, "Status: AFK (Playback Paused)")
                            self.root.after(0, self.update_tray_icon_state)
                            was_afk = True

                        elif not self.is_afk and was_afk:
                            self.log("User activity detected. Resuming normal operation.", "green")
                            if self.show_afk_status_var.get(): self.root.after(0, self.set_status, self.pre_afk_status_text)
                            self.root.after(0, self.update_tray_icon_state)
                            was_afk = False
                    except Exception as e: self.log(f"Error in pynput AFK detector: {e}", "red")
                    time.sleep(5)
            else: self.log("AFK detector not started: no suitable method for this OS.", "orange")
        threading.Thread(target=afk_thread_func, daemon=True).start()
        
    def populate_audio_devices(self):
        """Populates the audio device dropdown and attempts to auto-select a default."""
        try:
            devices = sd.query_devices()
            self.audio_devices = {}
            for i, device in enumerate(devices):
                if device['max_input_channels'] > 0:
                    device_name = f"{i}: {device['name']}"
                    self.audio_devices[device_name] = i
            
            if self.audio_devices:
                self.audio_device_menu['values'] = list(self.audio_devices.keys())
                
                saved_device = self.audio_device_var.get()
                if saved_device and saved_device in self.audio_devices:
                    self.audio_device_menu.set(saved_device)
                else:
                    preferred_device = None
                    for name in self.audio_devices.keys():
                        if any(keyword in name.lower() for keyword in ["mix", "loopback", "what u hear"]):
                            preferred_device = name
                            break
                    if preferred_device:
                        self.audio_device_menu.set(preferred_device)
                        self.log(f"Auto-selected audio device: {preferred_device}", "cyan")
                    else:
                        self.audio_device_menu.current(0)
            else:
                self.log("No audio input devices found. Is 'Stereo Mix' or VoiceMeeter enabled?", "red")
                self.audio_device_var.set("No devices found")
        except Exception as e:
            self.log(f"Could not query audio devices: {e}", "red")
            self.audio_device_var.set("Error finding devices")

    def update_sound_bar(self):
        """Update simple bar visualization."""
        if self.visualization_mode_var.get() != "bar" or not self.sound_bar_canvas or not self.sound_bar_canvas.winfo_exists():
            return
            
        self.sound_bar_canvas.delete("all")
        width = self.sound_bar_canvas.winfo_width()
        height = self.sound_bar_canvas.winfo_height()
        background_color = getattr(self.root.style.colors, 'inputbg', '#333333')
        self.sound_bar_canvas.create_rectangle(0, 0, width, height, fill=background_color, outline="")
        bar_width = (self.audio_level / 100) * width
        if self.audio_level < 50: color = "#00b050"
        elif self.audio_level < 80: color = "#ffc000"
        else: color = "#ff0000"
        if bar_width > 0: self.sound_bar_canvas.create_rectangle(0, 0, bar_width, height, fill=color, outline="")
        self.root.after(50, self.update_sound_bar)

    def log(self, message, color_name=None):
        def _log():
            if not self.log_text: print(f"LOG: {message}"); return
            try:
                self.log_text.configure(state='normal')
                timestamp = datetime.now().strftime('%H:%M:%S')
                self.log_text.insert(tk.END, f"{timestamp} - {message}\n")
                self.log_text.see(tk.END)
                self.log_text.configure(state='disabled')
                logging.info(message)
            except Exception as e: print(f"LOGGING ERROR: {e} - Original message: {message}")
        if self.root: self.root.after(0, _log)
    
    def browse_mpv_path(self):
        filetypes = [("Executable files", "*.exe")] if platform.system() == "Windows" else [("All files", "*")]
        file_path = filedialog.askopenfilename(title="Select MPV Executable", filetypes=filetypes)
        if file_path: self.mpv_path_var.set(file_path)

    def browse_folder_path(self, string_var):
        """Opens a dialog to select a folder and sets the provided StringVar."""
        folder_path = filedialog.askdirectory(title="Select Folder")
        if folder_path:
            string_var.set(folder_path)    

    def add_url_to_list(self, url):
        if 'playlist' in url.lower():
            self.expand_playlists_var.set(True)

        url_type = self.get_url_type(url)
        if self.is_local_file(url) or self.is_folder(url):
            title = os.path.basename(url.rstrip(os.sep))
            item_id = self.url_tree.insert("", tk.END, values=(title, url, url_type))
            self.all_tree_items.append({'title': title, 'url': url, 'type': url_type, 'id': item_id})
            self.log(f"Added local file/folder: {title}", "green")
        else:
            if self.fetch_titles_var.get():
                item_id = self.url_tree.insert("", tk.END, values=("Fetching Title...", url, url_type))
                item_data = {'title': "Fetching Title...", 'url': url, 'type': url_type, 'id': item_id}
                self.all_tree_items.append(item_data)
                self.log(f"Added URL for title fetching: {url} (item_id: {item_id})", "cyan")
                threading.Thread(target=self._fetch_single_web_title, args=(url, item_id), daemon=True).start()
            else:
                item_id = self.url_tree.insert("", tk.END, values=(url, url, url_type))
                self.all_tree_items.append({'title': url, 'url': url, 'type': url_type, 'id': item_id})
                self.log(f"Added URL without title fetching: {url}", "green")
        
        self.update_playlist_ui()

    def _fetch_single_web_title(self, url, item_id):
        """Fetches a video title using fast, direct API calls."""
        title = "Title Unavailable"
        self.log(f"Starting API title fetch for: {url}", "cyan")
        try:
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
            }
            if "youtube.com" in url or "youtu.be" in url:
                self.log("Detected YouTube URL, using oEmbed API", "cyan")
                oembed_url = f"https://www.youtube.com/oembed?url={url}&format=json"
                response = requests.get(oembed_url, headers=headers, timeout=10)
                response.raise_for_status()
                data = response.json()
                title = data.get('title', 'YouTube Video')
                self.log(f"Successfully fetched YouTube title: {title}", "green")

            elif "bilibili.com" in url:
                self.log("Detected Bilibili URL, using API and HTML scraping", "cyan")
                response = requests.get(url, headers=headers, timeout=10)
                response.raise_for_status()
                title = extract_bilibili_title(response.text, url)
                self.log(f"Bilibili title extraction result: {title}", "green")
            
            else:
                self.log(f"Unknown URL type, cannot fetch title for: {url}", "orange")
                title = "Unknown URL Type"

            for site_name in ['-哔哩哔哩', '_bilibili', '| bilibili', ' - YouTube']:
                if title.lower().endswith(site_name.lower()):
                    title = title[:-len(site_name)]
                    break
            title = title.strip(' _|-')

            self.root.after(0, self.update_treeview_item, item_id, title)
            self.url_to_title_map[url] = title
            self.log(f"Title fetch completed successfully: {title}", "green")

        except requests.exceptions.Timeout:
            self.log(f"Timeout while fetching title for {url}", 'red')
            self.root.after(0, self.update_treeview_item, item_id, "Fetch Timeout")
        except requests.exceptions.RequestException as e:
            self.log(f"Network error fetching title for {url}: {e}", 'red')
            self.root.after(0, self.update_treeview_item, item_id, "Network Error")
        except Exception as e:
            self.log(f"Unexpected error fetching title for {url}: {e}", 'red')
            self.log(traceback.format_exc(), 'red')
            self.root.after(0, self.update_treeview_item, item_id, "Title Fetch Failed")

    def update_treeview_item(self, item_id, new_title):
        """Robustly updates both the treeview display and the internal data structure."""
        try:
            self.log(f"Attempting to update treeview item {item_id} with title: '{new_title}'", "cyan")
            
            # Find the original data in our master list using the temporary item_id
            target_item_data = next((item for item in self.all_tree_items if item.get('id') == item_id), None)
            
            if not target_item_data:
                self.log(f"Could not find item {item_id} in internal data. It may have been removed.", "orange")
                return

            # Update the title in the master list and get the URL
            target_item_data['title'] = new_title
            target_url = target_item_data['url']
            self.log(f"Updated internal data for item {item_id} (URL: {target_url})", "green")

            # Now find the item in the visible treeview and update it
            for tree_item_id in self.url_tree.get_children():
                try:
                    values = self.url_tree.item(tree_item_id, 'values')
                    # CORRECTED: Check URL at index [2] and ensure 4 columns exist
                    if len(values) >= 4 and values[2] == target_url:
                        # CORRECTED: Rebuild the 4-column tuple with the new title at index [1]
                        new_values = (values[0], new_title, values[2], values[3])
                        self.url_tree.item(tree_item_id, values=new_values)
                        self.log(f"Found and updated visible treeview item for URL: {target_url}", "green")
                        return
                except tk.TclError:
                    continue
            
            self.log(f"Could not find a visible treeview item with URL to update: {target_url}", "orange")
                
        except Exception as e: 
            self.log(f"Error updating treeview item {item_id}: {e}", 'red')
            self.log(f"Traceback: {traceback.format_exc()}", 'red')

    def on_double_click_item(self, event):
        item_id = self.url_tree.identify_row(event.y)
        if not item_id:
            return
        
        selected_values = self.url_tree.item(item_id, 'values')
        if not selected_values or len(selected_values) < 2:
            return
            
        selected_url = selected_values[1]
        selected_title = selected_values[0]
        selected_type = selected_values[2] if len(selected_values) > 2 else self.get_url_type(selected_url)
        
        self.log(f"Double-clicked: {selected_title}", "blue")
        
        if selected_type == "Playlist" and not self.treat_playlists_as_videos_var.get():
            self.log("Detected playlist - will expand before playing...", "orange")
            if self.is_monitoring:
                self.log("Stopping current playing to switch to playlist...", "orange")
                self.stop_monitoring()
                self.root.after(1000, lambda: self.start_playlist_from_doubleclick(selected_url))
            else:
                self.start_playlist_from_doubleclick(selected_url)
        else:
            if self.is_monitoring:
                self.log("Stopping current playing to switch video...", "orange")
                self.stop_monitoring()
                self.root.after(1000, lambda: self.start_single_video_directly(selected_url))
            else:
                self.start_single_video_directly(selected_url)

    def start_playlist_from_doubleclick(self, playlist_url):
        progress_dialog = ttk.Toplevel(self.root)
        progress_dialog.title("Loading Playlist")
        progress_dialog.transient(self.root)
        progress_dialog.grab_set()
        
        progress_dialog.update_idletasks()
        
        main_x, main_y = self.root.winfo_x(), self.root.winfo_y()
        main_width, main_height = self.root.winfo_width(), self.root.winfo_height()
        dialog_width, dialog_height = 400, 150
        x = main_x + (main_width // 2) - (dialog_width // 2)
        y = main_y + (main_height // 2) - (dialog_height // 2)
        
        progress_dialog.geometry(f"{dialog_width}x{dialog_height}+{x}+{y}")
        progress_dialog.resizable(False, False)
        
        main_frame = ttk.Frame(progress_dialog, padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        status_label = ttk.Label(main_frame, text="Expanding playlist...", font=(get_japanese_font(), 11))
        status_label.pack(pady=(0, 10))
        
        progress_bar = ttk.Progressbar(main_frame, mode='indeterminate', length=350)
        progress_bar.pack(pady=(0, 10))
        progress_bar.start(10)
        
        details_label = ttk.Label(main_frame, text="Please wait, this may take a few seconds...", 
                                 font=(get_japanese_font(), 9), bootstyle="secondary")
        details_label.pack()
        
        cancelled = [False]
        
        def cancel_expansion():
            cancelled[0] = True
            progress_dialog.destroy()
            self.log("Playlist expansion cancelled by user.", "orange")
        
        cancel_btn = ttk.Button(main_frame, text="Cancel", command=cancel_expansion, bootstyle="danger-outline")
        cancel_btn.pack(pady=(10, 0))
        
        progress_dialog.update()
        
        def expand_playlist_async():
            try:
                self.log("Expanding playlist to get individual videos...", "blue")
                
                videos = []
                try:
                    self.log("Using a temporary headless browser for playlist expansion...", "cyan")
                    status_label.config(text="Launching temporary browser...")
                    progress_dialog.update()
                    
                    options = uc.ChromeOptions()
                    options.add_argument("--headless=new")
                    options.add_argument("--mute-audio")

                    with uc.Chrome(options=options, patcher_force_close=True) as temp_browser:
                        if cancelled[0]: return
                        status_label.config(text="Loading playlist page...")
                        details_label.config(text=f"URL: {playlist_url[:50]}...")
                        progress_dialog.update()
                        videos = self.get_playlist_videos(temp_browser, playlist_url)
                    
                    status_label.config(text=f"Found {len(videos)} videos!")
                    details_label.config(text="Preparing playback...")
                    progress_dialog.update()
                    
                except Exception as e:
                    self.log(f"Error expanding playlist with headless browser: {e}", "red")
                    status_label.config(text="Error expanding playlist!")
                    details_label.config(text=str(e)[:50])
                    progress_dialog.update()
                    time.sleep(2)
                    return
                
                if cancelled[0]: return
                
                progress_dialog.destroy()
                
                if not videos or (len(videos) == 1 and videos[0] == playlist_url):
                    self.root.after(0, lambda: messagebox.showwarning("Empty Playlist", "No videos found in the selected playlist."))
                    self.log("No videos found in playlist. Cannot start playback.", "red")
                    return
                
                self.log(f"Found {len(videos)} videos in playlist. Starting playback...", "green")
                
                def setup_playback():
                    if self.shuffle_within_playlists_var.get():
                        random.shuffle(videos)
                        self.log("Playlist videos shuffled.", "blue")
                    
                    self.current_playlist_videos = videos
                    self.current_playlist_index = 0
                    self.current_url = videos[0]
                    
                    self.is_monitoring = True
                    self.is_paused = False
                    self.monitoring_start_time = None
                    self.monitoring_paused_time = 0
                    
                    self.set_button_states('monitoring')
                    self.update_playlist_info()
                    
                    self.log(f"Loading first video: {self.get_display_name(self.current_url, format_type='log')}", "green")
                    self.load_video(self.current_url)
                    
                    self.monitor_thread = threading.Thread(target=self.playlist_monitor_loop_simple, daemon=True)
                    self.monitor_thread.start()
                    
                    self.update_timer()
                
                self.root.after(0, setup_playback)
                
            except Exception as e:
                self.log(f"Error in playlist expansion thread: {e}", "red")
                try: progress_dialog.destroy()
                except: pass
                self.root.after(0, lambda: messagebox.showerror("Playlist Error", f"Failed to expand playlist:\n{e}"))
        
        expansion_thread = threading.Thread(target=expand_playlist_async, daemon=True)
        expansion_thread.start()

    def get_playlist_videos_with_progress(self, browser, playlist_url, progress_callback=None):
        self.log(f"Fetching videos from playlist: {playlist_url}", 'blue')
        video_urls = []
        
        try:
            if progress_callback: progress_callback("Navigating to playlist...", "")
            browser.get(playlist_url)
            
            wait = WebDriverWait(browser, 10)
            
            if 'youtube.com' in playlist_url:
                if progress_callback: progress_callback("Loading YouTube playlist...", "")
                time.sleep(2)
                
                self.log("Starting YouTube scroll loop to load all videos...", "cyan")
                last_height = browser.execute_script("return document.documentElement.scrollHeight")
                scroll_attempts = 0
                while scroll_attempts < 15:
                    browser.execute_script("window.scrollTo(0, document.documentElement.scrollHeight);")
                    time.sleep(2.5)
                    new_height = browser.execute_script("return document.documentElement.scrollHeight")
                    if new_height == last_height:
                        self.log("Scrolling complete, page height is stable.", "green")
                        break
                    last_height = new_height
                    scroll_attempts += 1
                    self.log(f"Scrolled down, new page height: {new_height}", "blue")
                if scroll_attempts >= 15:
                    self.log("Reached max scroll attempts for YouTube playlist.", "orange")

                js_script = """
                function getYouTubePlaylistVideos() {
                    let urls = new Set();
                    document.querySelectorAll('ytd-playlist-video-renderer a#video-title').forEach(a => {
                        if (a.href && a.href.includes('/watch')) {
                            urls.add(a.href.split('&')[0]);
                        }
                    });
                    if (urls.size === 0) {
                        document.querySelectorAll('ytd-playlist-panel-video-renderer a').forEach(a => {
                            if (a.href && a.href.includes('/watch')) {
                                urls.add(a.href.split('&')[0]);
                            }
                        });
                    }
                    return Array.from(urls);
                }
                return getYouTubePlaylistVideos();
                """
                video_urls = browser.execute_script(js_script)
                
                if video_urls:
                    self.log(f"Found {len(video_urls)} videos in YouTube playlist", 'green')
                else:
                    self.log("No videos found in YouTube playlist, will play as single item", 'orange')
                    return [playlist_url]
                    
            elif 'bilibili.com' in playlist_url:
                if progress_callback: progress_callback("Loading Bilibili playlist...", "")
                try:
                    wait.until(EC.presence_of_element_located((By.CSS_SELECTOR, "a[href*='/video/BV']")))
                    self.log("Bilibili video links found. Proceeding with scrape.", "cyan")
                    time.sleep(2) 
                except TimeoutException:
                    self.log("Timed out waiting for Bilibili video links to appear.", "red")
                    return [playlist_url]

                video_urls_set = set()
                
                js_script = """
                function getBilibiliLinksInOrder() {
                    const videoItems = document.querySelectorAll(
                        '.video-list-item, .series-video-item, .fav-video-list > li, .list-item, .collection-video-card, .bili-video-card'
                    );
                    let urls = [];
                    videoItems.forEach(item => {
                        const linkElement = item.querySelector("a[href*='/video/BV']");
                        if (linkElement && linkElement.href) {
                            let baseUrl = linkElement.href.split('?')[0];
                            if (baseUrl.endsWith('/')) {
                                baseUrl = baseUrl.slice(0, -1);
                            }
                            urls.push(baseUrl);
                        }
                    });
                    return Array.from(new Set(urls));
                }
                return getBilibiliLinksInOrder();
                """

                for page_num in range(1, 51):
                    self.log(f"Scraping Bilibili playlist page {page_num}...", "cyan")
                    
                    try:
                        browser.execute_script("window.scrollTo(0, document.body.scrollHeight);")
                        time.sleep(1.5)
                    except JavascriptException:
                        self.log("Could not scroll, continuing scrape.", "orange")

                    page_videos = browser.execute_script(js_script)
                    new_videos_found_this_page = []
                    if page_videos:
                        for video_url in page_videos:
                            if video_url not in video_urls_set:
                                new_videos_found_this_page.append(video_url)
                                video_urls_set.add(video_url)
                        
                        if new_videos_found_this_page:
                           self.log(f"Found {len(new_videos_found_this_page)} new videos on this page.", "blue")
                           video_urls.extend(new_videos_found_this_page)

                    try:
                        next_button = browser.find_element(By.CSS_SELECTOR, '.be-pager-next:not(.be-pager-disabled), .bu-pager-next:not(.bu-pager-disabled)')
                        self.log("Found 'next page' button, clicking...", "blue")
                        browser.execute_script("arguments[0].click();", next_button)
                        time.sleep(3)
                    except NoSuchElementException:
                        self.log("No more pages found or button is disabled. Concluding Bilibili scrape.", "green")
                        break
                    except Exception as e:
                        self.log(f"Error during Bilibili pagination: {e}", "red")
                        break

                self.log(f"Found a total of {len(video_urls)} unique Bilibili videos.", 'green')


            if not video_urls:
                self.log("No playlist videos found after scraping, treating as single video.", 'orange')
                return [playlist_url.split('?')[0]]
                    
            return video_urls
            
        except TimeoutException:
            self.log(f"Timeout while fetching playlist videos from {playlist_url}.", 'red')
            return [playlist_url.split('?')[0]]
        except Exception as e:
            self.log(f"A critical error occurred in get_playlist_videos: {e}\n{traceback.format_exc()}", 'red')
            return [playlist_url.split('?')[0]]

    def playlist_monitor_loop_simple(self):
        try:
            while self.is_monitoring and self.current_playlist_videos:
                if self.browser:
                    try: _ = self.browser.window_handles
                    except: self.log("Browser closed. Stopping.", "orange"); break
                
                if self.mpv_process and self.mpv_process.poll() is not None:
                    self.log("MPV closed. Stopping.", "orange"); break
                
                # --- START: CORRECTED LOGIC ---
                # Always check the player's state first to sync the app's internal state.
                is_player_paused = self.get_player_paused_state()
                if self.sync_video_pause_var.get():
                    # If the player is playing but the app thinks it's paused, resume the app.
                    if is_player_paused is False and self.is_paused:
                        self.root.after(0, self.resume_monitoring, True)
                    # If the player is paused but the app thinks it's playing, pause the app.
                    elif is_player_paused is True and not self.is_paused:
                        self.root.after(0, self.pause_monitoring, True)
                
                # Now that the app state is synced, if we are paused, skip the rest of the loop.
                if self.is_paused:
                    time.sleep(1)
                    continue
                # --- END: CORRECTED LOGIC ---

                if self.auto_skip_var.get() and self.is_video_ended():
                    self.log("Video ended, moving to next in playlist.", "blue")
                    self.update_stats(0, skipped=True)
                    self.save_current_timestamp()
                    
                    self.current_playlist_index += 1
                    
                    if self.current_playlist_index >= len(self.current_playlist_videos):
                        self.log("Reached end of playlist.", "green")
                        break
                    
                    self.current_url = self.current_playlist_videos[self.current_playlist_index]
                    self.root.after(0, self.update_playlist_info)
                    self.log(f"Loading next video: {self.get_display_name(self.current_url, format_type='log')}", "green")
                    self.load_video(self.current_url)
                    continue
                
                if time.time() - self.last_stats_update_time > 10:
                    elapsed = time.time() - self.last_stats_update_time
                    self.update_stats(elapsed)
                    self.save_current_timestamp()
                    self.last_stats_update_time = time.time()
                    self.save_stats()
                
                time.sleep(1)
            
        except Exception as e:
            self.log(f"Error in playlist monitor loop: {e}", "red")
        
        finally:
            self.save_current_timestamp()
            self.log("Playlist playing finished.", "blue")
            self.root.after(0, self.stop_monitoring)

    def start_single_video_directly(self, url):
        try:
            self.log(f"Starting direct playback of: {url}", "blue")
            
            self.current_url = url
            self.current_playlist_videos = []
            self.current_playlist_index = 0
            
            self.is_monitoring = True
            self.is_paused = False
            self.monitoring_start_time = None
            self.monitoring_paused_time = 0
            
            self.set_button_states('monitoring')
            self.update_playlist_info()
            
            if not self.is_local_file(url) and not self.browser:
                self.setup_browser()
                if not self.browser:
                    self.log("Failed to setup browser.", "red")
                    self.stop_monitoring()
                    return
            
            self.load_video(url)
            
            self.monitor_thread = threading.Thread(target=self.simple_monitor_loop, daemon=True)
            self.monitor_thread.start()
            
            self.update_timer()
            
        except Exception as e:
            self.log(f"Error starting video: {e}", "red")
            self.stop_monitoring()
    
    def get_player_paused_state(self):
        """Checks if the video player in the browser is paused."""
        if not self.browser:
            return None
        try:
            js_script = """
            var video = document.querySelector('.bpx-player-video-wrap video') || 
                        document.querySelector('.html5-main-video') || 
                        document.querySelector('video');
            if (video) {
                return video.paused;
            }
            return null;
            """
            is_paused = self.browser.execute_script(js_script)
            return is_paused
        except (WebDriverException, JavascriptException, TypeError):
            return None

    def simple_monitor_loop(self):
        try:
            while self.is_monitoring:
                if self.browser:
                    try: _ = self.browser.window_handles
                    except WebDriverException: self.log("Browser closed. Stopping.", "orange"); break
                
                if self.mpv_process and self.mpv_process.poll() is not None:
                    self.log("MPV closed. Stopping.", "orange"); break
                
                is_player_paused = self.get_player_paused_state()
                if self.sync_video_pause_var.get():
                    if is_player_paused and not self.is_paused:
                        self.root.after(0, self.pause_monitoring, True)
                    elif not is_player_paused and self.is_paused:
                        self.root.after(0, self.resume_monitoring, True)

                if self.auto_skip_var.get() and self.is_video_ended():
                    self.log("Video ended.", "blue")
                    self.update_stats(0, skipped=True)
                    break
                
                if not self.is_paused and time.time() - self.last_stats_update_time > 10:
                    elapsed = time.time() - self.last_stats_update_time
                    self.update_stats(elapsed)
                    self.save_current_timestamp()
                    self.last_stats_update_time = time.time()
                    self.save_stats()
                
                time.sleep(1)
            
        except Exception as e:
            self.log(f"Error in simple monitor loop: {e}", "red")
        
        finally:
            self.save_current_timestamp()
            self.root.after(0, self.stop_monitoring)

    def update_timer(self):
        if self.is_monitoring and not self.is_paused:
            if self.monitoring_start_time is not None:
                elapsed = time.time() - self.monitoring_start_time - self.monitoring_paused_time
                h, rem = divmod(elapsed, 3600)
                m, s = divmod(rem, 60)
                self.time_label.config(text=f"Time: {int(h)}h {int(m)}m {int(s)}s")
            else:
                self.time_label.config(text="Time: Loading...")
            
            self.root.after(1000, self.update_timer)

    def show_loading_dialog_for_start(self, from_beginning=False):
        progress_dialog = ttk.Toplevel(self.root)
        progress_dialog.title("Starting Playback...")
        progress_dialog.transient(self.root)
        progress_dialog.grab_set()
        
        progress_dialog.update_idletasks()
        
        main_x, main_y = self.root.winfo_x(), self.root.winfo_y()
        main_width, main_height = self.root.winfo_width(), self.root.winfo_height()
        dialog_width, dialog_height = 400, 150
        x = main_x + (main_width // 2) - (dialog_width // 2)
        y = main_y + (main_height // 2) - (dialog_height // 2)
        
        progress_dialog.geometry(f"{dialog_width}x{dialog_height}+{x}+{y}")
        progress_dialog.resizable(False, False)
        
        main_frame = ttk.Frame(progress_dialog, padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        status_label = ttk.Label(main_frame, text="Preparing to play...", font=(get_japanese_font(), 11))
        status_label.pack(pady=(0, 10))
        
        progress_bar = ttk.Progressbar(main_frame, mode='indeterminate', length=350)
        progress_bar.pack(pady=(0, 10))
        progress_bar.start(10)
        
        details_label = ttk.Label(main_frame, text="Launching browser and setting up connections...", 
                                 font=(get_japanese_font(), 9), bootstyle="secondary")
        details_label.pack()

        def start_monitor_thread():
            self.start_monitoring(from_beginning)
            self.setup_complete_event.wait(timeout=30)
            try:
                progress_dialog.destroy()
            except tk.TclError:
                pass 
        
        threading.Thread(target=start_monitor_thread, daemon=True).start()

    def set_button_states(self, state):
        """A centralized function to manage the state of all interactive UI elements."""
        if state == 'monitoring':
            self.start_btn.config(state='disabled')
            self.pause_btn.config(state='normal', text="⏸️ PAUSE", command=self.pause_monitoring, bootstyle="warning")
            self.stop_btn.config(state='normal')
            self.now_playing_play_pause_btn.config(text="⏸️")
            self.set_status("Status: ▶️ Playing")
            for btn in [self.add_url_btn, self.add_folder_btn, self.browse_file_btn, self.remove_url_btn, self.save_playlist_btn, self.load_playlist_btn]:
                btn.config(state='disabled')

        elif state == 'paused':
            self.start_btn.config(state='disabled')
            self.pause_btn.config(state='normal', text="▶️ RESUME", command=self.resume_monitoring, bootstyle="success")
            self.stop_btn.config(state='normal')
            self.now_playing_play_pause_btn.config(text="▶️")
            self.set_status("Status: ⏸️ Paused")
            for btn in [self.add_url_btn, self.add_folder_btn, self.browse_file_btn, self.remove_url_btn, self.save_playlist_btn, self.load_playlist_btn]:
                btn.config(state='disabled')

        elif state == 'idle':
            self.start_btn.config(state='normal')
            self.pause_btn.config(state='disabled', text="⏸️ PAUSE", command=self.pause_monitoring, bootstyle="warning")
            self.stop_btn.config(state='disabled')
            self.now_playing_play_pause_btn.config(text="▶️")
            self.set_status("Status: 🎧 Listening")
            for btn in [self.add_url_btn, self.add_folder_btn, self.browse_file_btn, self.remove_url_btn, self.save_playlist_btn, self.load_playlist_btn]:
                btn.config(state='normal')

        elif state == 'fetching':
            self.start_btn.config(state='disabled')
            self.pause_btn.config(state='disabled')
            self.stop_btn.config(state='normal')
            self.set_status("Status: Fetching...")
            for btn in [self.add_url_btn, self.add_folder_btn, self.browse_file_btn, self.remove_url_btn, self.save_playlist_btn, self.load_playlist_btn]:
                btn.config(state='disabled')

        self.update_playlist_info()
        self.update_tray_menu()
        self.update_tray_icon_state()
        
    def resume_monitoring(self, sync_only=False):
        if self.is_monitoring and self.is_paused:
            self.is_paused = False
            if self.pause_start_time: self.monitoring_paused_time += (time.time() - self.pause_start_time)
            self.set_button_states('monitoring')
            self.log("Playback resumed.", 'green')
            
            if not sync_only:
                if self.mpv_process: self.control_mpv("play")
                elif self.browser: self.control_video_playback("play")
            
            self.update_timer()

    def on_closing(self):
        if self.is_monitoring: self.save_current_timestamp(); self.save_stats()
        self.save_profile()
        if self.browser:
            try: self.browser.quit(); self.log("Browser closed on exit.", "blue")
            except Exception as e: self.log(f"Error closing browser on exit: {e}", "red")
        if self.mpv_process:
            try: self.mpv_process.terminate(); self.log("MPV process terminated on exit.", "blue")
            except Exception as e: self.log(f"Error terminating MPV on exit: {e}", "red")
        self.root.destroy()
        
    def start_monitoring(self, from_beginning=False):
        """
        Initiates the entire playback process.
        """
        initial_urls = [item['url'] for item in self.get_items_from_display()]
        if not initial_urls:
            messagebox.showerror("Error", "Please add at least one URL or file to the list.")
            self.log("Start failed: No URLs provided.", 'red')
            self.setup_complete_event.set()
            return

        if from_beginning:
            self.ignore_timestamps_for_session = True
            self.log("Starting from the beginning, ignoring saved timestamps for this session.", "blue")
        else:
            self.ignore_timestamps_for_session = False
            playable_videos = [url for url in initial_urls if self.get_saved_timestamp_status(url) != "finished"]
            if not playable_videos and not any(self.get_url_type(url) == "Playlist" for url in initial_urls):
                 messagebox.showinfo("All Watched", "All items have been watched. Use 'Play from Beginning' to watch again.")
                 self.log("Playback not started: all items have been watched.", "orange")
                 self.setup_complete_event.set()
                 self.set_button_states('idle')
                 return

        self.is_monitoring = True
        self.is_paused = False
        # REFACTOR: Pack the Now Playing card into the dashboard
        self.update_now_playing_card()
        self.monitoring_start_time = None
        self.monitoring_paused_time = 0
        self.setup_complete_event.clear()

        self.monitor_thread = threading.Thread(
            target=self.monitor_loop, 
            args=(initial_urls,), 
            daemon=True
        )
        self.monitor_thread.start()

    def monitor_loop(self, urls_to_monitor):
        try:
            self.log("Monitor loop started. Preparing playlist...", "cyan")
            
            if self.expand_playlists_var.get() and any(self.get_url_type(url) == "Playlist" for url in urls_to_monitor):
                self.log("Expanding all playlists in a temporary headless browser...", "blue")
                try:
                    options = uc.ChromeOptions()
                    options.add_argument("--headless=new")
                    options.add_argument("--mute-audio")
                    with uc.Chrome(options=options, patcher_force_close=True) as temp_browser:
                        urls_to_monitor = self.preprocess_playlists(urls_to_monitor, temp_browser)
                except Exception as e:
                    self.log(f"Failed to expand playlists in headless mode: {e}", "red")
                    self.root.after(0, self.stop_monitoring)
                    self.setup_complete_event.set()
                    return
            else:
                 urls_to_monitor = self.always_expand_playlists(urls_to_monitor)

            if self.true_random_on_skip_var.get():
                self.true_random_monitor_loop(urls_to_monitor)
                return

            self.main_queue = list(urls_to_monitor)
            self.main_queue_index = 0
            self.current_playlist_videos = []

            if self.smart_shuffle_var.get():
                watched = [url for url in self.main_queue if self.get_saved_timestamp_status(url) == "finished"]
                unwatched = [url for url in self.main_queue if self.get_saved_timestamp_status(url) != "finished"]
                random.shuffle(unwatched)
                self.main_queue = unwatched + watched
                self.log(f"Smart shuffled: {len(unwatched)} unwatched, {len(watched)} watched.", "blue")
            elif self.random_list_var.get():
                random.shuffle(self.main_queue)
                self.log("Shuffled main queue order", "blue")

            has_web_urls = any(not self.is_local_file(url) for url in self.main_queue)
            if has_web_urls and not self.browser:
                self.setup_browser()
                if not self.browser:
                    self.log("Browser setup failed. Stopping playback.", "red")
                    self.root.after(0, self.stop_monitoring)
                    self.setup_complete_event.set()
                    return

            self.root.after(0, self.set_button_states, 'monitoring')
            self.setup_complete_event.set()

            while self.is_monitoring and self.main_queue_index < len(self.main_queue):
                current_item = self.main_queue[self.main_queue_index]
                self.current_url = current_item
                self.root.after(0, self.update_playlist_info)
                
                url_type = self.get_url_type(current_item)

                if url_type == "Playlist" and self.sequential_playlists_var.get() and not self.treat_playlists_as_videos_var.get():
                    self.handle_playlist_sequential(current_item)
                else: 
                    if not self.ignore_timestamps_for_session and self.get_saved_timestamp_status(current_item) == "finished":
                        self.log(f"Skipping '{self.get_display_name(current_item)}' as it was previously finished.", "blue")
                    else:
                        self.handle_single_video(current_item)
                
                if not self.is_monitoring: break

                self.main_queue_index += 1
                if self.main_queue_index < len(self.main_queue):
                    time.sleep(1)

            self.log("Finished all items in the queue.", "green")

        except Exception as e:
            self.log(f"Critical error in monitor loop: {e}\n{traceback.format_exc()}", "red")
        finally:
            self.root.after(0, self.stop_monitoring)

    def true_random_monitor_loop(self, urls_to_monitor):
        self.log("Starting 'True Random' playing mode.", "cyan")
        
        self.expanded_video_pool = []
        self.log("Expanding all playlists into a random pool...", "blue")
        try:
            options = uc.ChromeOptions(); options.add_argument("--headless=new"); options.add_argument("--mute-audio")
            with uc.Chrome(options=options, patcher_force_close=True) as temp_browser:
                self.expanded_video_pool = self.preprocess_playlists(urls_to_monitor, temp_browser)
        except Exception as e:
            self.log(f"Failed to expand playlists for random mode: {e}", "red")
            messagebox.showerror("Error", f"Could not expand playlists for random mode.\n\n{e}")
            return
        finally:
            self.setup_complete_event.set()

        if not self.expanded_video_pool:
            self.log("No videos found after expanding playlists. Stopping.", "red")
            return

        self.log(f"Created a random pool of {len(self.expanded_video_pool)} videos.", "green")

        has_web_urls = any(not self.is_local_file(url) for url in self.expanded_video_pool)
        if has_web_urls and not self.browser:
            self.setup_browser()
            if not self.browser:
                self.log("Browser setup failed. Stopping playing.", "red")
                return
        
        self.root.after(0, self.set_button_states, 'monitoring')

        while self.is_monitoring:
            next_video_url = random.choice(self.expanded_video_pool)
            self.handle_single_video(next_video_url)
            
            if not self.is_monitoring:
                break
            
            time.sleep(2)

    def setup_browser(self):
        try:
            self.log("Setting up Chrome browser...", "blue")
            options = uc.ChromeOptions()
            if self.headless_var.get(): options.add_argument("--headless=new")
            user_data_dir = self.profile_path_var.get().strip(); profile_name = self.profile_name_var.get().strip()
            if user_data_dir: options.add_argument(f"--user-data-dir={user_data_dir}")
            if profile_name: options.add_argument(f"--profile-directory={profile_name}")
            if not self.unmute_var.get(): options.add_argument("--mute-audio")

            self.log("Patching and creating uc.Chrome instance...");
            self.browser = uc.Chrome(options=options, patcher_force_close=True)
            self.log("Browser instance created successfully.", "green")
            
            if not self.headless_var.get():
                try:
                    browser_geom_str = self.browser_geometry_var.get()
                    if browser_geom_str:
                        browser_geom = json.loads(browser_geom_str)
                        if all(k in browser_geom for k in ['x', 'y', 'width', 'height']):
                            self.browser.set_window_position(browser_geom['x'], browser_geom['y'])
                            self.browser.set_window_size(browser_geom['width'], browser_geom['height'])
                except (json.JSONDecodeError, TypeError, KeyError, WebDriverException) as e: 
                    self.log(f"Could not restore browser position: {e}", "orange")
        except Exception as e: self.log(f"Failed to launch Undetected Chrome: {e}", "red"); messagebox.showerror("Browser Error", f"Could not launch Chrome. Error: {e}"); self.browser = None

    def load_video(self, url):
        self.monitored_time_started = False
        self.current_url = url
        
        self.update_window_title()
        
        title = self.get_video_title(url)
        self.now_playing_title_var.set(title)
        self.now_playing_progress_var.set(0)
        self.update_now_playing_thumbnail(url)
        
        needs_mpv = self.is_local_file(url) and self.use_mpv_var.get()
        needs_browser = not self.is_local_file(url)

        if needs_mpv and self.browser:
            self.log("Switching to MPV, closing browser.", "blue")
            try: self.browser.quit()
            except WebDriverException: pass
            finally: self.browser = None
        elif needs_browser and self.mpv_process:
            self.log("Switching to browser, closing MPV.", "blue")
            try: self.mpv_process.terminate()
            except OSError: pass
            finally: self.mpv_process = None

        self.video_load_time = time.time()
        
        if needs_mpv:
            if not self.mpv_process: self.launch_mpv(url)
            else: self.control_mpv("loadfile", url)
        elif needs_browser:
            if not self.browser: self.setup_browser()
            if self.browser:
                try:
                    self.browser.get(url)
                    
                    if 'youtube.com' in url:
                        try:
                            WebDriverWait(self.browser, 10).until(
                                EC.presence_of_element_located((By.CSS_SELECTOR, "h1.ytd-video-primary-info-renderer, h1.title, yt-formatted-string.style-scope.ytd-video-primary-info-renderer"))
                            )
                            time.sleep(2)
                        except:
                            time.sleep(3)
                    elif 'bilibili.com' in url:
                        try:
                            WebDriverWait(self.browser, 10).until(
                                EC.presence_of_element_located((By.CSS_SELECTOR, "h1.video-title, .video-title-href"))
                            )
                            time.sleep(2)
                        except:
                            time.sleep(3)
                    else:
                        time.sleep(3)
                    
                    if url not in self.url_to_title_map or self.url_to_title_map.get(url) in [None, "New Tab", ""]:
                        try:
                            actual_title = self.browser.title
                            
                            if actual_title and actual_title not in ["New Tab", "YouTube", ""]:
                                for site_name in [' - YouTube', '-哔哩哔哩', '_bilibili', '| bilibili']:
                                    if actual_title.endswith(site_name):
                                        actual_title = actual_title[:-len(site_name)]
                                        break
                                self.url_to_title_map[url] = actual_title.strip()
                                
                                self.update_window_title()
                                title = self.get_video_title(url)
                                self.now_playing_title_var.set(title)
                                self.update_tray_menu()
                            else:
                                if 'youtube.com' in url:
                                    title_element = self.browser.execute_script(
                                        "return document.querySelector('h1.ytd-video-primary-info-renderer, h1.title, yt-formatted-string.style-scope.ytd-video-primary-info-renderer')?.textContent || document.title"
                                    )
                                    if title_element and title_element != "New Tab":
                                        self.url_to_title_map[url] = title_element.strip()
                                        self.update_window_title()
                                        self.now_playing_title_var.set(title_element.strip())
                                        self.update_tray_menu()
                        except Exception as e:
                            print(f"DEBUG: Error getting title after page load: {e}")
                    
                    self.apply_saved_timestamp(url)
                    time.sleep(1)
                    self.control_video_playback("play")
                except Exception as e:
                    self.log(f"Error loading URL in browser: {url}, Error: {e}", "red")
            else:
                self.log(f"Failed to setup browser. Cannot play '{url}'.", "red")

    def launch_mpv(self, file_path):
        mpv_path = self.find_mpv_executable()
        if not mpv_path: messagebox.showerror("MPV Not Found", "MPV executable not found."); return
        try:
            if platform.system() == "Windows": self.mpv_ipc_path = f"\\\\.\\pipe\\mpv_ipc_{uuid.uuid4().hex[:8]}"
            else: self.mpv_ipc_path = os.path.join(tempfile.gettempdir(), f"mpv_socket_{uuid.uuid4().hex[:8]}")
            args = [mpv_path, file_path, "--force-window", "--keep-open=yes", "--save-position-on-quit", f"--input-ipc-server={self.mpv_ipc_path}"]
            if not self.unmute_var.get(): args.append("--mute=yes")
            timestamp = self.get_saved_timestamp_status(file_path)
            if timestamp and isinstance(timestamp, (int, float)) and timestamp > 5: args.append(f"--start={timestamp}")
            self.mpv_process = subprocess.Popen(args); self.log(f"Launched MPV for: {file_path}", 'green')
        except Exception as e: self.log(f"Failed to launch MPV: {e}", 'red')

    def control_mpv(self, command, value=None):
        if not self.mpv_process or not self.mpv_ipc_path: return
        try:
            ipc_command = {"command": ["loadfile", value]} if command == "loadfile" else {"command": ["set_property", "pause", command == "pause"]}
            cmd_str = json.dumps(ipc_command) + '\n'
            if platform.system() == "Windows":
                with open(self.mpv_ipc_path, 'w') as pipe: pipe.write(cmd_str)
            else:
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock: sock.connect(self.mpv_ipc_path); sock.sendall(cmd_str.encode('utf-8'))
        except Exception as e: self.log(f"Error sending MPV command '{command}': {e}", 'orange')

    def query_mpv(self, property_name):
        if not self.mpv_process or not self.mpv_ipc_path: return None
        try:
            ipc_command = {"command": ["get_property", property_name]}; cmd_str = json.dumps(ipc_command) + '\n'
            if platform.system() == "Windows":
                with open(self.mpv_ipc_path, 'r+', encoding='utf-8') as pipe: pipe.write(cmd_str); pipe.flush(); response_str = pipe.readline()
            else:
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
                    sock.settimeout(1.0); sock.connect(self.mpv_ipc_path); sock.sendall(cmd_str.encode('utf-8')); response_data = b''
                    while b'\n' not in response_data:
                        chunk = sock.recv(1024)
                        if not chunk: break
                        response_data += chunk
                    response_str = response_data.decode('utf-8')
            for line in response_str.strip().split('\n'):
                if not line: continue
                response_json = json.loads(line)
                if "data" in response_json and response_json.get("error") == "success": return response_json.get("data")
            self.log(f"MPV query for '{property_name}' did not return data.", 'orange'); return None
        except (IOError, OSError, json.JSONDecodeError, socket.timeout) as e: self.log(f"Error querying MPV property '{property_name}': {e}", 'orange'); return None

    def get_video_timestamp(self):
        if self.mpv_process and self.mpv_process.poll() is None:
            timestamp = self.query_mpv("time-pos"); return timestamp if timestamp is not None else 0
        if self.browser:
            try: ts = self.browser.execute_script("var v = document.querySelector('video'); return v ? v.currentTime : null;"); return ts if isinstance(ts, (int, float)) or isinstance(ts, int) else 0
            except (WebDriverException, JavascriptException): return 0
        return 0

    def get_video_duration(self):
        if self.mpv_process and self.mpv_process.poll() is None:
            duration = self.query_mpv("duration"); return duration if duration is not None else 0
        if self.browser:
            try: duration = self.browser.execute_script("var v = document.querySelector('video'); return v ? v.duration : null;"); return duration if isinstance(duration, (int, float)) or isinstance(duration, int) else 0
            except (WebDriverException, JavascriptException): return 0
        return 0

    def is_video_finished(self):
        current_time = self.get_video_timestamp()
        total_duration = self.get_video_duration()

        if total_duration and total_duration > 0:
            percentage_watched = (current_time / total_duration) * 100
            if percentage_watched >= self.finished_percentage_var.get():
                return True
        
        if self.is_video_ended():
            return True

        return False

    def is_video_ended(self):
        if self.mpv_process: 
            return self.mpv_process.poll() is not None
        if self.browser:
            try:
                js_script = "return (document.querySelector('.bpx-player-video-wrap video') || document.querySelector('.html5-main-video') || document.querySelector('video'))?.ended ?? false;"
                return self.browser.execute_script(js_script)
            except WebDriverException:
                return True
            except (JavascriptException, TypeError):
                return False
        return False

    def control_video_playback(self, action):
        if self.browser:
            try:
                js_script = f"var v = document.querySelector('.bpx-player-video-wrap video') || document.querySelector('.html5-main-video') || document.querySelector('video'); if(v) v.{action}();"
                self.browser.execute_script(js_script)
            except: pass

    def handle_silence_trigger(self):
        if self.is_monitoring and not self.is_paused:
            self.log("Silence trigger: Advancing to next video.", "blue")
            
            if self.sequential_playlists_var.get() and self.current_playlist_videos:
                self.current_playlist_index += 1
                if self.current_playlist_index >= len(self.current_playlist_videos):
                    self.playlist_exhausted = True
                    self.log("Playlist finished, moving to next item in queue", "blue")
                else:
                    self.current_url = self.current_playlist_videos[self.current_playlist_index]
                    self.root.after(0, self.update_playlist_info)
                    self.log(f"Loading next in playlist: {self.get_display_name(self.current_url)}", "green")
                    self.load_video(self.current_url)
            else:
                self.next_video()

    def load_config(self):
        try:
            if os.path.exists(CONFIG_FILE):
                with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                    self.config_data = json.load(f)
            else:
                self.config_data = {"last_profile": "Default", "profiles": {"Default": {}}, "items": [], "url_to_title_map": {}, "subscriptions": []}
            
            self.tree_items = self.config_data.get("items", [])
            self.all_tree_items = list(self.tree_items)
            self.url_to_title_map = self.config_data.get("url_to_title_map", {})
            self.subscriptions = self.config_data.get("subscriptions", [])
            self.update_playlist_ui()
            self.update_subscriptions_display()

            profiles = list(self.config_data.get("profiles", {}).keys())
            if not profiles:
                profiles = ["Default"]
                self.config_data["profiles"] = {"Default": {}}
            
            self.profile_combobox['values'] = profiles
            
            last_profile = self.config_data.get("last_profile")
            if last_profile and last_profile in profiles:
                self.active_profile_name.set(last_profile)
            else:
                self.active_profile_name.set(profiles[0])
            
            self.load_profile_data(self.active_profile_name.get())
            self.log("Configuration and profiles loaded.", 'green')

        except Exception as e:
            self.log(f"Failed to load configuration: {e}", 'red')
            self.config_data = {"last_profile": "Default", "profiles": {"Default": {}}, "items": [], "url_to_title_map": {}, "subscriptions": []}
            self.active_profile_name.set("Default")
            self.profile_combobox['values'] = ["Default"]

    def load_profile_data(self, profile_name):
        profile = self.config_data.get("profiles", {}).get(profile_name, {})
        
        self.theme_var.set(profile.get('theme', 'litera'))
        self.playlist_mode_var.set(profile.get('playlist_mode', 'Custom'))
        for var_name, default in [
            ('headless', True), ('autostart', False), ('random_list', False), 
            ('save_timestamp', True), ('unmute', False), ('auto_skip', True), 
            ('sync_video_pause', True), ('keep_browser_open', True), 
            ('delay_minutes', 5.0), ('silence_minutes', 2.0), ('sound_threshold', 0.5), 
            ('silence_threshold', 0.1), ('audio_gain', 1.0), ('expand_playlists', False), 
            ('shuffle_within_playlists', False), ('use_mpv', False), 
            ('recursive_folder', True), ('fetch_titles', True), ('afk_enabled', False), 
            ('afk_timeout_minutes', 5.0), ('show_afk_status', True), 
            ('treat_playlists_as_videos', False), ('finished_percentage', 95.0),
            ('true_random_on_skip', False), ('sequential_playlists', True),
            ('smart_shuffle', False),
            ('always_show_nav_panel', False),
        ]:
            getattr(self, f"{var_name}_var").set(profile.get(var_name, default))

        self.profile_path_var.set(profile.get('profile_path', ''))
        self.profile_name_var.set(profile.get('profile_name', ''))
        self.mpv_path_var.set(profile.get('mpv_path', ''))
        self.audio_device_var.set(profile.get('audio_device', ''))
        
        self.app_geometry_var.set(profile.get('app_geometry', ''))
        self.browser_geometry_var.set(json.dumps(profile.get('browser_geometry', {})))
        self.stats_window_geometry = profile.get('stats_window_geometry', '')
        
        self.log(f"Loaded profile: {profile_name}", "cyan")

    def save_profile(self):
        profile_name = self.active_profile_name.get()
        if not profile_name:
            profile_name = "Default"
            self.active_profile_name.set(profile_name)

        current_profile_data = {}
        for var_name in [
            'headless', 'autostart', 'random_list', 'save_timestamp', 'unmute', 
            'auto_skip', 'sync_video_pause', 'keep_browser_open', 'delay_minutes', 
            'silence_minutes', 'sound_threshold', 'silence_threshold', 'audio_gain', 
            'expand_playlists', 'shuffle_within_playlists', 'use_mpv', 'profile_path', 
            'profile_name', 'mpv_path', 'recursive_folder', 'fetch_titles', 
            'audio_device', 'afk_enabled', 'afk_timeout_minutes', 'show_afk_status', 
            'treat_playlists_as_videos', 'finished_percentage', 'true_random_on_skip',
            'sequential_playlists', 'theme', 'smart_shuffle', 'playlist_mode', 'always_show_nav_panel',
        ]:
            current_profile_data[var_name] = getattr(self, f"{var_name}_var").get()
        
        current_profile_data['app_geometry'] = self.root.geometry()
        
        if self.browser and self.is_browser_responsive():
            try:
                pos = self.browser.get_window_position()
                size = self.browser.get_window_size()
                browser_geom = {'x': pos['x'], 'y': pos['y'], 'width': size['width'], 'height': size['height']}
                current_profile_data['browser_geometry'] = browser_geom
                self.log("Saved browser geometry.", "green")
            except WebDriverException:
                self.log("Could not get browser geometry to save, it may have been closed.", "orange")
        else:
             try:
                current_profile_data['browser_geometry'] = json.loads(self.browser_geometry_var.get())
             except (json.JSONDecodeError, TypeError):
                current_profile_data['browser_geometry'] = {}
        
        current_profile_data['stats_window_geometry'] = getattr(self, 'stats_window_geometry', '')

        if "profiles" not in self.config_data:
            self.config_data["profiles"] = {}
        
        self.config_data["profiles"][profile_name] = current_profile_data
        
        self.save_app_state()
        self.log(f"Settings for profile '{profile_name}' saved.", 'green')

        if profile_name not in self.profile_combobox['values']:
            self.profile_combobox['values'] = list(self.config_data["profiles"].keys())

    def new_profile(self):
        new_name = simpledialog.askstring("New Profile", "Enter a name for the new profile:", parent=self.root)
        if not new_name:
            return
        if new_name in self.config_data.get("profiles", {}):
            messagebox.showwarning("Profile Exists", f"A profile named '{new_name}' already exists.")
            return

        default_profile = self.config_data.get("profiles", {}).get("Default", {})
        self.config_data["profiles"][new_name] = copy.deepcopy(default_profile)
        
        self.profile_combobox['values'] = list(self.config_data["profiles"].keys())
        self.active_profile_name.set(new_name)
        self.load_profile_data(new_name)
        self.save_app_state()
        self.log(f"Created new profile: '{new_name}'", "green")

    def copy_profile(self):
        current_profile_name = self.active_profile_name.get()
        new_name = simpledialog.askstring("Copy Profile", "Enter a name for the new profile:", 
                                          initialvalue=f"{current_profile_name} (Copy)", parent=self.root)
        if not new_name:
            return
        if new_name in self.config_data.get("profiles", {}):
            messagebox.showwarning("Profile Exists", f"A profile named '{new_name}' already exists.")
            return

        current_profile_data = self.config_data.get("profiles", {}).get(current_profile_name, {})
        self.config_data["profiles"][new_name] = copy.deepcopy(current_profile_data)
        
        self.profile_combobox['values'] = list(self.config_data["profiles"].keys())
        self.active_profile_name.set(new_name)
        self.save_app_state()
        self.log(f"Copied profile '{current_profile_name}' to '{new_name}'", "green")

    def save_app_state(self):
        self.config_data['last_profile'] = self.active_profile_name.get()
        self.config_data['items'] = self.get_items_from_display()
        self.config_data['url_to_title_map'] = self.url_to_title_map
        self.config_data['subscriptions'] = self.subscriptions
        
        try:
            with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.config_data, f, indent=4, ensure_ascii=False)
        except Exception as e:
            self.log(f"Failed to save configuration file: {e}", 'red')

    def on_profile_select(self, event=None):
        selected_profile = self.active_profile_name.get()
        self.load_profile_data(selected_profile)

    def delete_profile(self):
        profile_to_delete = self.active_profile_name.get()
        if not profile_to_delete or profile_to_delete == "Default":
            messagebox.showwarning("Cannot Delete", "The 'Default' profile cannot be deleted.")
            return

        if messagebox.askyesno("Confirm Delete", f"Are you sure you want to delete the profile '{profile_to_delete}'?"):
            if profile_to_delete in self.config_data.get("profiles", {}):
                del self.config_data["profiles"][profile_to_delete]
                
                profiles = list(self.config_data.get("profiles", {}).keys())
                self.profile_combobox['values'] = profiles
                self.active_profile_name.set(profiles[0])
                self.load_profile_data(profiles[0])
                
                self.save_app_state()
                self.log(f"Profile '{profile_to_delete}' deleted.", "blue")
            
    def get_items_from_display(self):
        """Gets all items from the Treeview display for saving."""
        items = []
        for item_id in self.url_tree.get_children():
            values = self.url_tree.item(item_id, 'values')
            # Corrected indices to account for the new "status" column at values[0]
            if len(values) >= 4:
                items.append({'title': values[1], 'url': values[2], 'type': values[3]})
        return items

    def load_stats(self):
        try:
            if os.path.exists(STATS_FILE):
                with open(STATS_FILE, 'r', encoding='utf-8') as f:
                    self.stats = json.load(f)
                self.log("Statistics loaded.", 'green')
            else:
                self.stats = {}
                self.log("No stats file found. A new one will be created.", 'orange')
        except (json.JSONDecodeError, IOError) as e:
            self.log(f"Failed to load or parse statistics file: {e}", 'red')
            self.stats = {}

    def save_stats(self):
        try:
            with open(STATS_FILE, 'w', encoding='utf-8') as f: json.dump(self.stats, f, indent=4)
        except Exception as e: self.log(f"Failed to save statistics: {e}", 'red')

    def update_stats(self, time_elapsed, triggered=False, skipped=False):
        """Robustly updates the statistics for the current day."""
        today = date.today().isoformat()
        
        if today not in self.stats or not isinstance(self.stats.get(today), dict):
            self.stats[today] = {}

        today_stats = self.stats[today]
        today_stats['total_monitored_time'] = today_stats.get('total_monitored_time', 0) + time_elapsed
        if triggered:
            today_stats['trigger_count'] = today_stats.get('trigger_count', 0) + 1
        if skipped:
            today_stats['video_skips'] = today_stats.get('video_skips', 0) + 1
        
        if 'timestamps' not in today_stats:
            today_stats['timestamps'] = {}


    def save_current_timestamp(self):
        if not self.save_timestamp_var.get() or not self.current_url: return
        
        timestamp_url = self._clean_url(self.current_url)
        timestamp = self.get_video_timestamp()
        
        if self.is_video_finished():
            today = date.today().isoformat()
            if today not in self.stats:
                self.stats[today] = {'timestamps': {}}
            self.stats[today].setdefault('timestamps', {})[timestamp_url] = -1
            self.log(f"Video marked as finished for {self.get_display_name(timestamp_url, format_type='log')}", "blue")
        elif timestamp > 0:
            today = date.today().isoformat()
            if today not in self.stats:
                self.stats[today] = {'timestamps': {}}
            self.stats[today].setdefault('timestamps', {})[timestamp_url] = timestamp
            self.log(f"Timestamp {timestamp:.1f}s saved for {self.get_display_name(timestamp_url, format_type='log')}", "blue")

        self.update_item_status_in_treeview(timestamp_url)    

    def manual_save_timestamp(self):
        if not self.is_monitoring: self.log("Cannot save timestamp when not playing.", "orange"); return
        self.save_current_timestamp(); self.save_stats()

    def update_playlist_ui(self):
        """Updates the playlist UI elements like title, count, and status icons."""
        # Preserve the current selection and view
        selected_items = self.url_tree.selection()

        self.url_tree.delete(*self.url_tree.get_children())
        for item in self.all_tree_items:
            status_emoji = self.get_status_emoji(item.get('url'))
            self.url_tree.insert("", tk.END, values=(status_emoji, item.get('title'), item.get('url'), item.get('type')))

        count = len(self.all_tree_items)
        self.url_frame.config(text=f"Playlist ({count} items) 📝")

        # Re-apply selection
        try:
            if selected_items:
                self.url_tree.selection_set(selected_items)
        except tk.TclError:
            pass # Items may no longer exist, which is fine

        self.update_window_title()

    def is_local_file(self, path): return os.path.isfile(path) and not path.startswith(('http://', 'https://'))
    def is_folder(self, path): return os.path.isdir(path) and not path.startswith(('http://', 'https://'))
    
    def get_url_type(self, url):
        is_bilibili_playlist = (
            'bilibili.com' in url and (
                '/favlist' in url or 
                '/medialist/' in url or 
                'collectiondetail' in url or 
                '/lists/' in url or 
                'videopod.episodes' in url or
                '?type=season' in url or
                '?type=series' in url
            )
        )
        
        if self.treat_playlists_as_videos_var.get():
            if 'youtube.com/playlist' in url or is_bilibili_playlist:
                return "Video"
        
        if 'youtube.com/playlist' in url or is_bilibili_playlist:
            return "Playlist"
        
        if url.startswith(('http://', 'https://')):
            return "Video"
        if os.path.isdir(url):
            return "Folder"
        if os.path.isfile(url):
            return "Local File"
        
        return "Unknown"

    def find_mpv_executable(self):
        custom_path = self.mpv_path_var.get().strip()
        if custom_path and os.path.exists(custom_path): return custom_path
        if platform.system() == "Windows": return "mpv.exe"
        try: return subprocess.check_output(["which", "mpv"]).strip().decode()
        except: return None
        
    def _clean_url(self, url):
        if 'bilibili.com' in url:
            match = re.search(r'(https?://(?:www\.)?bilibili\.com/video/BV[a-zA-Z0-9]+)', url)
            if match: return match.group(1)
        elif 'youtube.com' in url:
            match = re.search(r'(https?://(?:www\.)?youtube\.com/watch\?v=[a-zA-Z0-9_-]+)', url)
            if match: return match.group(1)
        return url

    def get_saved_timestamp_status(self, url):
        url = self._clean_url(url)
        latest_timestamp = None

        sorted_days = sorted([day for day in self.stats.keys() if day != 'url_stats'], reverse=True)

        for day in sorted_days:
            data = self.stats[day]
            if not isinstance(data, dict): continue
            
            timestamps = data.get('timestamps', {})
            if url in timestamps:
                latest_timestamp = timestamps[url]
                break

        if latest_timestamp is not None:
            return "finished" if latest_timestamp == -1 else latest_timestamp
        
        return None

    def get_saved_timestamp(self, file_path):
        file_path = self._clean_url(file_path)
        for day, data in self.stats.items():
            if not isinstance(data, dict) or day == 'url_stats': continue
            timestamps = data.get('timestamps', {})
            if file_path in timestamps: return timestamps[file_path]
        return None

    def apply_saved_timestamp(self, url):
        if not self.save_timestamp_var.get() or self.ignore_timestamps_for_session: return
        
        timestamp = self.get_saved_timestamp(url)
        
        if timestamp == -1:
            self.log(f"Skipping {self.get_display_name(url)} as it was previously finished.", "blue")
        elif timestamp and timestamp > 5 and self.browser:
            try:
                self.browser.execute_script(f"document.querySelector('video').currentTime = {timestamp};")
            except: pass

    def update_player_geometries(self):
        """Saves the current geometry of the browser window if it's open."""
        if self.browser and not self.headless_var.get():
            try:
                pos = self.browser.get_window_position()
                size = self.browser.get_window_size()
                browser_geom = {'x': pos['x'], 'y': pos['y'], 'width': size['width'], 'height': size['height']}
                self.browser_geometry_var.set(json.dumps(browser_geom))
            except WebDriverException:
                self.log("Could not save browser geometry, it may have been closed.", "orange")

    def preprocess_playlists(self, url_list, browser):
        final_urls = []
        try:
            if not browser:
                self.log("No browser instance was provided for playlist preprocessing. Cannot proceed.", "red")
                return url_list

            self.log(f"Starting preprocessing of {len(url_list)} URLs", "blue")
            
            for i, url in enumerate(url_list, 1):
                self.log(f"Processing item {i}/{len(url_list)}: {url}", "blue")
                
                url_type = self.get_url_type(url)
                self.log(f"Detected type: {url_type}", "cyan")
                
                if url_type == "Playlist":
                    self.log(f"Expanding playlist: {url}", "blue")
                    videos = self.get_playlist_videos(browser, url)
                    
                    if len(videos) == 1 and videos[0] == url:
                        self.log(f"Playlist extraction failed, skipping: {url}", "orange")
                        continue
                    
                    if self.shuffle_within_playlists_var.get():
                        random.shuffle(videos)
                        self.log(f"Shuffled {len(videos)} videos from playlist", "blue")
                    
                    final_urls.extend(videos)
                    self.log(f"Added {len(videos)} videos from playlist to final list", "green")
                else:
                    final_urls.append(url)
                    self.log(f"Added single video/file: {url}", "green")
            
            if self.random_list_var.get():
                random.shuffle(final_urls)
                self.log("Shuffled entire final playlist", "blue")
            
            self.log(f"Preprocessing complete. Total URLs: {len(final_urls)}", "green")
            return final_urls
            
        except Exception as e:
            self.log(f"Error preprocessing playlists: {e}", "red")
            self.log(f"Traceback: {traceback.format_exc()}", "red")
            return url_list

    def get_playlist_videos(self, browser, playlist_url):
        return self.get_playlist_videos_with_progress(browser, playlist_url)
        
    def handle_single_video(self, video_url):
        try:
            self.current_url = video_url
            self.current_playlist_videos = []
            self.current_playlist_index = 0
            self.current_item_type = 'video'
            
            self.root.after(0, self.update_playlist_info)
            self.load_video(video_url)
            self.root.after(0, self.update_timer)
            
            self.skip_event.clear()
            
            while self.is_monitoring:
                if self.browser and not self.is_browser_responsive():
                    self.log("Browser closed. Stopping video handler.", "orange")
                    break
                if self.mpv_process and self.mpv_process.poll() is not None:
                    self.log("MPV closed. Stopping video handler.", "orange")
                    break

                # --- START: CORRECTED LOGIC ---
                # Always check the player's state first to sync the app's internal state.
                is_player_paused = self.get_player_paused_state()
                if self.sync_video_pause_var.get():
                    # If the player is playing but the app thinks it's paused, resume the app.
                    if is_player_paused is False and self.is_paused:
                        self.root.after(0, self.resume_monitoring, True)
                    # If the player is paused but the app thinks it's playing, pause the app.
                    elif is_player_paused is True and not self.is_paused:
                        self.root.after(0, self.pause_monitoring, True)

                # Now that the app state is synced, if we are paused, skip the rest of the loop.
                if self.is_paused:
                    time.sleep(0.5)
                    continue
                # --- END: CORRECTED LOGIC ---

                if self.auto_skip_var.get() and self.is_video_ended():
                    self.log("Video ended", "blue")
                    self.update_stats(0, skipped=True)
                    self.save_current_timestamp()
                    break

                if time.time() - self.last_stats_update_time > 10:
                    elapsed = time.time() - self.last_stats_update_time
                    self.update_stats(elapsed)
                    self.save_current_timestamp()
                    self.last_stats_update_time = time.time()
                    self.save_stats()

                if self.skip_event.wait(timeout=1.0):
                    self.log("Skip event detected, exiting video loop.", "blue")
                    break

            self.save_current_timestamp()
            
        except WebDriverException as e:
            self.log(f"Browser session ended unexpectedly while handling video: {self.current_url}. Error: {e}", "orange")
            self.browser = None
        except Exception as e:
            self.log(f"Error handling single video: {e}", "red")
            self.log(f"Traceback: {traceback.format_exc()}", "red")

    def handle_playlist_sequential(self, playlist_url):
        try:
            self.log(f"Expanding playlist: {playlist_url}", "blue")

            if not self.is_browser_responsive():
                self.log("Browser is not responsive, cannot expand playlist.", "red")
                return

            self.log(f"Using main browser instance to scrape playlist...", "cyan")
            videos = self.get_playlist_videos(self.browser, playlist_url)

            if not videos or (len(videos) == 1 and videos[0] == playlist_url):
                self.log(f"Could not expand playlist, playing as single item", "orange")
                self.handle_single_video(playlist_url)
                return
            
            if self.shuffle_within_playlists_var.get():
                random.shuffle(videos)
                self.log(f"Shuffled {len(videos)} videos in playlist", "blue")
            
            self.current_playlist_videos = videos
            self.current_playlist_index = 0
            self.current_item_type = 'playlist'
            self.playlist_exhausted = False
            
            while self.current_playlist_index < len(self.current_playlist_videos) and self.is_monitoring and not self.playlist_exhausted:
                video_url = self.current_playlist_videos[self.current_playlist_index]
                
                if not self.ignore_timestamps_for_session:
                    saved_status = self.get_saved_timestamp_status(video_url)
                    if saved_status == "finished":
                        self.log(f"Skipping finished video: {self.get_display_name(video_url)}", "blue")
                        self.current_playlist_index += 1
                        continue
                
                self.current_url = video_url
                self.root.after(0, self.update_playlist_info)
                self.log(f"Playing video {self.current_playlist_index + 1}/{len(self.current_playlist_videos)}: {self.get_display_name(video_url)}", "green")
                
                self.handle_single_video(video_url)
                
                if not hasattr(self, 'skip_to_next_in_playlist') or not self.skip_to_next_in_playlist:
                    self.current_playlist_index += 1
                else:
                    self.current_playlist_index += 1
                    self.skip_to_next_in_playlist = False
                
                if self.current_playlist_index < len(self.current_playlist_videos):
                    time.sleep(1)
            
            self.current_playlist_videos = []
            self.current_playlist_index = 0
            self.current_item_type = None
            self.playlist_exhausted = False
            self.log(f"Finished playlist: {self.get_display_name(playlist_url)}", "green")
            
        except Exception as e:
            self.log(f"Error in sequential playlist handler: {e}", "red")
            self.current_playlist_videos = []
            self.current_playlist_index = 0
            self.playlist_exhausted = False

    def get_display_name(self, url, format_type='title_only'):
        """ENHANCED: Now properly returns title for display."""
        if not url: return "N/A"
        
        url_type = self.get_url_type(url)
        type_emoji = {"Video": "🎬", "Playlist": "📃", "Local File": "💾", "Folder": "📂"}.get(url_type, "📄")

        title = self.get_video_title(url)
            
        if format_type == 'log': 
            return f"{title} ({url})"
        elif format_type == 'title_only':
            return title
        return f"{type_emoji} {title}"

    def update_playlist_info(self, *args):
        """Updates the new enhanced navigation panel with detailed info and progress."""
        # Determine if the panel should be visible based on playback state or the new setting
        is_visible = self.is_monitoring or self.always_show_nav_panel_var.get()

        if not is_visible:
            self.nav_frame.pack_forget()
            self.update_tray_menu()
            return
        else:
            self.nav_frame.pack(fill=tk.X, pady=5) # Ensure it's visible

        # If monitoring, update with active playback info
        if self.is_monitoring:
            current_index = 0
            total_count = 0
            queue_type = ""
            current_title = self.get_display_name(self.current_url)
            if len(current_title) > 40:
                current_title = current_title[:37] + "..."

            # Case 1: We are inside a sequential playlist
            if self.current_playlist_videos and len(self.current_playlist_videos) > 1:
                current_index = self.current_playlist_index
                total_count = len(self.current_playlist_videos)
                queue_type = "Playlist"
                self.prev_btn.config(state=tk.NORMAL if current_index > 0 else tk.DISABLED)
                self.next_btn.config(state=tk.NORMAL if current_index < total_count - 1 else tk.DISABLED)

            # Case 2: We are in the main queue
            elif hasattr(self, 'main_queue') and self.main_queue:
                current_index = self.main_queue_index
                total_count = len(self.main_queue)
                queue_type = "Queue"
                self.prev_btn.config(state=tk.NORMAL if current_index > 0 else tk.DISABLED)
                self.next_btn.config(state=tk.NORMAL if current_index < total_count - 1 else tk.DISABLED)

            # Case 3: A single video is playing directly
            else:
                current_index = 0
                total_count = 1
                queue_type = "Now Playing"
                self.prev_btn.config(state=tk.DISABLED)
                self.next_btn.config(state=tk.DISABLED)

            # Update all UI elements with the active state
            if total_count > 0:
                info_text = f"Playing: \"{current_title}\" • Position {current_index + 1} of {total_count} ({queue_type})"
                self.playlist_info_label.config(text=info_text)
                self.jump_entry_var.set(str(current_index + 1))
                self.total_videos_label.config(text=f"/ {total_count}")
                progress = ((current_index + 1) / total_count) * 100
                self.nav_progress_var.set(progress)
            else: # Fallback for an empty or invalid state
                self.playlist_info_label.config(text="No playlist loaded")
                self.jump_entry_var.set("0")
                self.total_videos_label.config(text="/ 0")
                self.nav_progress_var.set(0)
        
        # If not monitoring (but panel is visible due to setting), show an idle state
        else:
            total_items = len(self.get_items_from_display())
            self.playlist_info_label.config(text="Playback stopped. Press Play to begin.")
            self.jump_entry_var.set("0")
            self.total_videos_label.config(text=f"/ {total_items}")
            self.nav_progress_var.set(0)
            self.prev_btn.config(state=tk.DISABLED)
            self.next_btn.config(state=tk.DISABLED)

        self.update_tray_menu()
    
    def skip_videos(self, count):
        """Skips forward or backward in the current queue (playlist or main)."""
        if not self.is_monitoring:
            return
        
        # Case 1: We are inside a sequential playlist
        if self.current_playlist_videos:
            new_index = self.current_playlist_index + count
            new_index = max(0, min(new_index, len(self.current_playlist_videos) - 1))
            
            if new_index != self.current_playlist_index:
                self.current_playlist_index = new_index - 1 # Subtract 1 because the loop will increment
                self.skip_event.set()
                self.log(f"Jumping by {count} to video {new_index + 1}/{len(self.current_playlist_videos)}", "blue")
                
        # Case 2: We are in the main queue
        elif self.main_queue:
            new_index = self.main_queue_index + count
            new_index = max(0, min(new_index, len(self.main_queue) - 1))
            
            if new_index != self.main_queue_index:
                self.main_queue_index = new_index - 1 # Subtract 1 because the loop will increment
                self.skip_event.set()
                self.log(f"Jumping by {count} to video {new_index + 1}/{len(self.main_queue)}", "blue")
    
    def next_video(self):
        if not self.is_monitoring:
            return
        
        if self.current_playlist_videos and self.current_playlist_index < len(self.current_playlist_videos) - 1:
            self.current_playlist_index += 1
            self.skip_event.set()
            self.log(f"Next button: Jumping to {self.current_playlist_index + 1}/{len(self.current_playlist_videos)}", "blue")
            self.update_playlist_info()
        elif hasattr(self, 'main_queue') and self.main_queue and self.main_queue_index < len(self.main_queue) - 1:
            self.skip_event.set()
            self.log(f"Next button: Skipping to next in queue ({self.main_queue_index + 2}/{len(self.main_queue)})", "blue")
        else:
            self.log("Next button: Already at end of queue/playlist.", "orange")

    def on_jump_entry(self, event=None):
        """Handles the Enter key in the jump entry box for both queue types."""
        if not self.is_monitoring:
            return

        try:
            target_num = int(self.jump_entry_var.get())
            
            # Case 1: We are inside a sequential playlist
            if self.current_playlist_videos:
                if 1 <= target_num <= len(self.current_playlist_videos):
                    self.current_playlist_index = target_num - 2 # Will be incremented to target-1 by the loop
                    self.skip_event.set()
                    self.log(f"Jumping to video {target_num}/{len(self.current_playlist_videos)} in playlist", "blue")
                else:
                    self.log(f"Invalid video number. Please enter 1-{len(self.current_playlist_videos)}", "orange")
                    self.jump_entry_var.set(str(self.current_playlist_index + 1))
            
            # Case 2: We are in the main queue
            elif self.main_queue:
                if 1 <= target_num <= len(self.main_queue):
                    self.main_queue_index = target_num - 2 # Will be incremented to target-1 by the loop
                    self.skip_event.set()
                    self.log(f"Jumping to video {target_num}/{len(self.main_queue)} in main queue", "blue")
                else:
                    self.log(f"Invalid video number. Please enter 1-{len(self.main_queue)}", "orange")
                    self.jump_entry_var.set(str(self.main_queue_index + 1))
                    
        except ValueError:
            self.log("Please enter a valid number", "orange")
            if self.current_playlist_videos:
                self.jump_entry_var.set(str(self.current_playlist_index + 1))
            elif self.main_queue:
                self.jump_entry_var.set(str(self.main_queue_index + 1))

    def on_slider_change(self, value):
        if not self.is_monitoring or not self.current_playlist_videos:
            return
        
        target = int(float(value))
        
        if target - 1 != self.current_playlist_index:
            self.current_playlist_index = target - 1
            self.current_url = self.current_playlist_videos[self.current_playlist_index]
            
            self.update_video_title_display()
            
            if hasattr(self, '_slider_timer'):
                self.root.after_cancel(self._slider_timer)
            self._slider_timer = self.root.after(500, self.on_slider_released)

    def on_slider_released(self):
        if not self.is_monitoring:
            return
        
        self.skip_event.set()
        self.log(f"Jumped to video {self.current_playlist_index + 1}/{len(self.current_playlist_videos)} via slider", "blue")

    def update_video_title_display(self):
        if self.current_playlist_videos and 0 <= self.current_playlist_index < len(self.current_playlist_videos):
            current_video = self.current_playlist_videos[self.current_playlist_index]
            title = self.get_display_name(current_video, format_type='title_only')
            
            if len(title) > 60:
                title = title[:57] + "..."
            
            self.current_video_title_var.set(f"Video {self.current_playlist_index + 1}: {title}")
        else:
            self.current_video_title_var.set("")

    def previous_video(self):
        if not self.is_monitoring:
            return
        
        if self.current_playlist_videos and self.current_playlist_index > 0:
            self.current_playlist_index -= 1
            self.skip_event.set()
            self.log(f"Previous button: Jumping to {self.current_playlist_index + 1}/{len(self.current_playlist_videos)}", "blue")
            self.update_playlist_info()
        elif hasattr(self, 'main_queue') and self.main_queue and self.main_queue_index > 0:
            self.main_queue_index -= 2
            self.skip_event.set()
            self.log(f"Previous button: Going back in queue to {self.main_queue_index + 2}/{len(self.main_queue)})", "blue")
        else:
            self.log("Previous button: Already at start of queue/playlist.", "orange")

    def setup_system_tray(self):
        self.tray_icons = {
            "idle": self._create_tray_image("grey"),
            "playing": self._create_tray_image("green"),
            "paused": self._create_tray_image("yellow"),
            "afk": self._create_tray_image("orange")
        }
        self.tray_icon = icon('Silence Suzuka', self.tray_icons['idle'], "Silence Suzuka", menu=self.create_tray_menu())
        threading.Thread(target=self.tray_icon.run, daemon=True).start()
        self.update_tray_tooltip_loop()

    def _create_tray_image(self, color):
        """Creates a colored image for the system tray icon."""
        width, height = 64, 64
        image = Image.new('RGB', (width, height), 'black')
        dc = ImageDraw.Draw(image)
        dc.ellipse([(8, 8), (width - 8, height - 8)], fill=color)
        return image

    def update_tray_icon_state(self):
        """Updates the tray icon based on the current application state."""
        if not self.tray_icon: return
        
        state = "idle"
        if self.is_monitoring:
            if self.is_afk and self.afk_enabled_var.get():
                state = "afk"
            elif self.is_paused:
                state = "paused"
            else:
                state = "playing"
        
        if self.tray_icon.icon != self.tray_icons[state]:
            self.tray_icon.icon = self.tray_icons[state]

    def update_tray_tooltip_loop(self):
        """Periodically updates the hover tooltip for the tray icon."""
        if not self.tray_icon: return

        tooltip_text = "Silence Suzuka - Idle"
        if self.is_monitoring:
            state_text = "Playing"
            if self.is_afk and self.afk_enabled_var.get():
                state_text = "AFK"
            elif self.is_paused:
                state_text = "Paused"
            
            video_title = self.get_video_title(self.current_url)
            if len(video_title) > 30:
                video_title = video_title[:27] + "..."
            
            tooltip_text = f"🟢 {state_text} - {video_title}"

        self.tray_icon.title = tooltip_text
        self.root.after(1000, self.update_tray_tooltip_loop)

    def create_tray_menu(self):
        is_playlist = bool(self.current_playlist_videos)
        if not self.is_monitoring: return Menu(item('Show', self.tray_show_window, default=True), item('Exit', self.quit_application))
        
        now_playing_text = f"Playing: {self.get_video_title(self.current_url)}"
        now_playing_text = (now_playing_text[:50] + '...') if len(now_playing_text) > 50 else now_playing_text
        
        return Menu(item(now_playing_text, None, enabled=False), Menu.SEPARATOR, item('Pause' if not self.is_paused else 'Resume', self.tray_toggle_pause), item('Next', self.tray_next_video, enabled=is_playlist), item('Previous', self.tray_previous_video, enabled=is_playlist), item('Stop Playing', self.tray_stop_monitoring), Menu.SEPARATOR, item('Show Window', self.tray_show_window), item('Exit', self.quit_application))

    def update_tray_menu(self):
        if self.tray_icon: self.tray_icon.menu = self.create_tray_menu(); self.tray_icon.update_menu()

    def tray_toggle_pause(self):
        if self.is_paused: self.root.after(0, self.resume_monitoring)
        else: self.root.after(0, self.pause_monitoring)

    def tray_next_video(self): self.root.after(0, self.next_video)
    def tray_previous_video(self): self.root.after(0, self.previous_video)
    def tray_stop_monitoring(self): self.root.after(0, self.stop_monitoring)
    def tray_show_window(self): self.root.after(0, self.show_window)
    def hide_window(self): self.root.withdraw()
    def show_window(self): self.root.deiconify()
    def quit_application(self):
        if self.tray_icon: self.tray_icon.stop()
        self.on_closing()

    def remove_subscription(self):
        """Removes the selected subscription."""
        selected_item = self.subs_tree.selection()
        if not selected_item:
            return
        
        source_to_remove = self.subs_tree.item(selected_item[0], 'values')[0]
        self.subscriptions = [sub for sub in self.subscriptions if sub['source'] != source_to_remove]
        self.update_subscriptions_display()
        self.save_app_state()

    def update_subscriptions_display(self):
        """Updates the subscriptions treeview."""
        self.subs_tree.delete(*self.subs_tree.get_children())
        for sub in self.subscriptions:
            self.subs_tree.insert("", tk.END, values=(sub['source'], sub['type']))

    def refresh_subscriptions(self):
        """Refreshes all subscriptions and adds new videos."""
        threading.Thread(target=self._refresh_subscriptions_thread, daemon=True).start()

    def _refresh_subscriptions_thread(self):
        """The background thread for refreshing subscriptions."""
        self.log("Refreshing subscriptions...", "blue")
        new_videos_found = 0
        
        existing_urls = {item['url'] for item in self.all_tree_items}

        web_subscriptions = [sub for sub in self.subscriptions if sub['type'] == 'Channel']
        if web_subscriptions:
            self.log(f"Processing {len(web_subscriptions)} web channel(s) with a single browser instance.", "cyan")
            try:
                options = uc.ChromeOptions()
                options.add_argument("--headless=new")
                with uc.Chrome(options=options, patcher_force_close=True) as temp_browser:
                    for sub in web_subscriptions:
                        self.log(f"Checking Channel: {sub['source']}", "cyan")
                        try:
                            videos = self.get_playlist_videos(temp_browser, sub['source'])
                            for video_url in videos:
                                if video_url not in existing_urls:
                                    self.root.after(0, self.add_url_to_list, video_url)
                                    existing_urls.add(video_url)
                                    new_videos_found += 1
                        except Exception as e:
                            self.log(f"Error refreshing channel {sub['source']}: {e}", "red")
            except Exception as e:
                self.log(f"Failed to initialize browser for subscription refresh: {e}", "red")

        folder_subscriptions = [sub for sub in self.subscriptions if sub['type'] == 'Folder']
        if folder_subscriptions:
            self.log(f"Processing {len(folder_subscriptions)} local folder(s).", "cyan")
            for sub in folder_subscriptions:
                self.log(f"Checking Folder: {sub['source']}", "cyan")
                video_extensions = {'.mp4', '.mkv', '.avi', '.mov', '.wmv', '.flv', '.webm', '.m4v'}
                try:
                    for file in os.listdir(sub['source']):
                        if any(file.lower().endswith(ext) for ext in video_extensions):
                            file_path = os.path.join(sub['source'], file)
                            if file_path not in existing_urls:
                                self.root.after(0, self.add_url_to_list, file_path)
                                existing_urls.add(file_path)
                                new_videos_found += 1
                except Exception as e:
                    self.log(f"Error refreshing folder {sub['source']}: {e}", "red")
        
        if new_videos_found > 0:
            self.log(f"Found and added {new_videos_found} new videos from subscriptions.", "green")
            self.root.after(0, self.save_app_state)
        else:
            self.log("No new videos found in subscriptions.", "blue")

    def show_preview(self, item_id):
        """Shows a video preview tooltip."""
        if not self.url_tree.exists(item_id):
            self.hide_preview()
            return

        if self.preview_window:
            self.preview_window.destroy()

        values = self.url_tree.item(item_id, 'values')
        # CORRECTED: Get URL from index [2] instead of [1]
        url = values[2]

        if not url.startswith("http"):
            return

        x, y, _, height = self.url_tree.bbox(item_id)
        x_pos = self.url_tree.winfo_rootx() + self.url_tree.column("#1", "width") + 10
        y_pos = self.url_tree.winfo_rooty() + y + (height // 2)

        self.preview_window = tk.Toplevel(self.root)
        self.preview_window.wm_overrideredirect(True)
        
        loading_label = ttk.Label(self.preview_window, text="Loading preview...", padding=10)
        loading_label.pack()
        self.preview_window.update_idletasks()

        win_width = self.preview_window.winfo_width()
        win_height = self.preview_window.winfo_height()
        final_y = y_pos - (win_height // 2)
        self.preview_window.wm_geometry(f"+{x_pos}+{final_y}")

        if url in self.thumbnail_cache:
            self.display_thumbnail(self.thumbnail_cache[url])
        else:
            threading.Thread(target=self.fetch_thumbnail, args=(url,), daemon=True).start()

    def hide_preview(self):
        """Hides the video preview tooltip."""
        if self.preview_window:
            self.preview_window.destroy()
            self.preview_window = None

    def fetch_thumbnail(self, url, for_now_playing=False):
        """
        Fetches thumbnails for videos and playlists.
        """
        img_data = None
        thumbnail_url = None
        try:
            headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'}

            bilibili_list_match = re.search(r'space.bilibili.com/\d+/(?:lists|favlist)/(\d+)', url)
            if bilibili_list_match:
                media_id = bilibili_list_match.group(1)
                self.log(f"Fetching Bilibili list thumbnail via API for media_id: {media_id}", "cyan")
                api_url = f"https://api.bilibili.com/x/v3/fav/resource/info?media_id={media_id}"
                response = requests.get(api_url, headers=headers, timeout=5)
                response.raise_for_status()
                data = response.json()
                thumbnail_url = data.get('data', {}).get('info', {}).get('cover')

            if not thumbnail_url and ("youtube.com/playlist" in url or "youtube.com/watch" in url):
                self.log(f"Fetching YouTube thumbnail via oEmbed API for: {url}", "cyan")
                oembed_url = f"https://www.youtube.com/oembed?url={url}&format=json"
                response = requests.get(oembed_url, headers=headers, timeout=5)
                response.raise_for_status()
                data = response.json()
                thumbnail_url = data.get('thumbnail_url')

            bvid_match = re.search(r'/video/(BV[0-9A-Za-z]+)', url)
            if not thumbnail_url and bvid_match:
                self.log(f"Fetching Bilibili video thumbnail via API for: {url}", "cyan")
                bvid = bvid_match.group(1)
                api_url = f"https://api.bilibili.com/x/web-interface/view?bvid={bvid}"
                response = requests.get(api_url, headers=headers, timeout=5)
                response.raise_for_status()
                data = response.json()
                thumbnail_url = data.get('data', {}).get('pic')

            if thumbnail_url:
                if thumbnail_url.startswith("//"):
                    thumbnail_url = "https:" + thumbnail_url
                
                self.log(f"Found thumbnail URL: {thumbnail_url}", "green")
                img_response = requests.get(thumbnail_url, headers=headers, timeout=5)
                img_response.raise_for_status()
                img_data = img_response.content

            if img_data:
                self.thumbnail_cache[url] = img_data
                if for_now_playing:
                    self.root.after(0, self.display_now_playing_thumbnail, img_data)
                else:
                    self.root.after(0, self.display_thumbnail, img_data)
            else:
                self.log(f"Could not find a valid thumbnail for {url}", "orange")
                if for_now_playing:
                    self.root.after(0, self.set_placeholder_thumbnail)

        except Exception as e:
            self.log(f"Error fetching thumbnail for {url}: {e}", "red")
            if for_now_playing:
                self.root.after(0, self.set_placeholder_thumbnail)
    def display_thumbnail(self, img_data):
        """Displays the fetched thumbnail in the preview window."""
        if self.preview_window and self.preview_window.winfo_exists():
            try:
                for widget in self.preview_window.winfo_children():
                    widget.destroy()
                
                img = Image.open(BytesIO(img_data))
                img.thumbnail((240, 180))
                photo = ImageTk.PhotoImage(img)
                
                label = ttk.Label(self.preview_window, image=photo)
                label.image = photo 
                label.pack()
            except Exception as e:
                self.log(f"Error displaying thumbnail: {e}", "red")

    def update_now_playing_thumbnail(self, url):
        """Specifically updates the thumbnail on the 'Now Playing' card."""
        if not url.startswith("http"):
            self.set_placeholder_thumbnail()
            return

        if url in self.thumbnail_cache:
            self.display_now_playing_thumbnail(self.thumbnail_cache[url])
        else:
            threading.Thread(target=self.fetch_thumbnail, args=(url, True), daemon=True).start()

    def display_now_playing_thumbnail(self, img_data):
        """Displays the thumbnail on the 'Now Playing' card."""
        try:
            img = Image.open(BytesIO(img_data))
            img.thumbnail((120, 90))
            self.now_playing_thumbnail_photo = ImageTk.PhotoImage(img)
            self.now_playing_thumbnail_label.config(image=self.now_playing_thumbnail_photo)
        except Exception as e:
            self.log(f"Error displaying 'Now Playing' thumbnail: {e}", "red")

    def update_now_playing_card(self):
        """Periodically updates the progress bar on the Now Playing card."""
        if self.is_monitoring and not self.is_paused:
            duration = self.get_video_duration()
            current_time = self.get_video_timestamp()
            
            if duration and duration > 0:
                progress = (current_time / duration) * 100
                self.now_playing_progress_var.set(progress)
            else:
                self.now_playing_progress_var.set(0)
        
        if self.now_playing_frame.winfo_viewable():
            self.root.after(1000, self.update_now_playing_card)

    def show_first_time_welcome(self):
        """Displays a welcome message and setup instructions for first-time users."""
        messagebox.showinfo(
            "Welcome to Silence Suzuka!",
            "It looks like this is your first time running the application.\n\n"
            "**IMPORTANT AUDIO SETUP**:\n\n"
            "For the app to detect your computer's audio and automatically play the next video, "
            "you MUST enable a 'loopback' audio device.\n\n"
            "On Windows, this is usually called 'Stereo Mix'. You may need to enable it in your Sound Control Panel.\n\n"
            "After enabling it, please select it from the 'Audio Input Device' dropdown. "
            "You can find this in: Settings Tab -> Audio.\n\n"
            "Enjoy the app!",
            parent=self.root
        )

def extract_bilibili_title(html, url):
    """Helper function to extract Bilibili titles using multiple fallbacks."""
    og_title = re.search(r'<meta property="og:title" content="([^"]+)"', html)
    if og_title and og_title.group(1).strip():
        return og_title.group(1).strip()
    page_title = re.search(r'<title>(.*?)_哔哩哔哩_bilibili</title>', html)
    if not page_title:
        page_title = re.search(r'<title>(.*?)</title>', html)
    if page_title and page_title.group(1).strip():
        return page_title.group(1).strip()
    h1 = re.search(r'<h1[^>]*>(.*?)</h1>', html)
    if h1 and h1.group(1).strip():
        return h1.group(1).strip()
    fav_name = re.search(r'class="fav-name[^"]*"[^>]*>([^<]+)</', html)
    if fav_name and fav_name.group(1).strip():
        return fav_name.group(1).strip()
    media_title = re.search(r'class="media-title[^"]*"[^>]*>([^<]+)</', html)
    if media_title and media_title.group(1).strip():
        return media_title.group(1).strip()
    list_title = re.search(r'"listTitle":"([^"]+)"', html)
    if list_title and list_title.group(1).strip():
        return list_title.group(1).strip()
    if "upload/video" in url: return "User Uploads"
    if "/lists/" in url: return "User Playlist"
    if "/search" in url: return "Search Results"
    return "Bilibili Content"

if __name__ == "__main__":
    try:
        if sys.platform == "win32":
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        root = ttk.Window(themename="superhero")
        app = AudioMonitorApp(root)
        root.mainloop()
    except Exception as e:
        error_root = tk.Tk()
        error_root.withdraw()
        messagebox.showerror(
            "Fatal Error",
            f"An unexpected error occurred and the application must close:\n\n{e}\n\n"
            f"Please check the log file '{LOG_FILE}' for more details."
        )
        logging.critical("Fatal error on startup", exc_info=True)
