import tkinter as tk
from tkinter import ttk, messagebox
import random
import time
import math
import json
import os
import sys
import webbrowser
from pathlib import Path # pathlib is great for path manipulation
import platform
from datetime import datetime, timedelta
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from collections import defaultdict
import numpy as np
from typing import Dict, List, Tuple, Set, Optional, Union
import ctypes



def set_app_user_model_id(app_id_str: str):
    """
    Sets the Application User Model ID for the current process.
    This helps Windows group windows and use the correct taskbar icon.
    """
    if platform.system() == "Windows":
        try:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(app_id_str)
            print(f"AppUserModelID set to: {app_id_str}") # For debugging
        except AttributeError:
            print("Failed to set AppUserModelID: Attribute error (ctypes or shell32 issue).")
        except Exception as e:
            print(f"Failed to set AppUserModelID: {e}")




class MathSpeedTrainer:

    def resource_path(self, relative_path):
        """Get absolute path to resource, works for dev and PyInstaller"""
        try:
            # PyInstaller creates a temp folder and stores path in _MEIPASS
            base_path = sys._MEIPASS
        except AttributeError: # More specific: _MEIPASS not found
            base_path = os.path.abspath(".")
        except Exception as e: # Catch other potential errors during base_path detection
            print(f"Warning: Error determining base path for resources: {e}")
            base_path = os.path.abspath(".") # Fallback to current directory
        return os.path.join(base_path, relative_path)


    def __init__(self, root):
        self.root = root
        try:
            icon_path = self.resource_path("math.ico")
            self.root.iconbitmap(icon_path)
        except tk.TclError as e:
            print(f"Warning: Could not set window icon. File: '{icon_path}'. Error: {e}")
        except Exception as e:
            print(f"Warning: An unexpected error occurred while setting the window icon: {e}")

        self.root.iconbitmap(icon_path)
        self.root.title("Math Speed Trainer")
        self.root.geometry("1000x900") # Adjusted geometry
        self.root.resizable(True, True)

        self.theme = "light"
        self.define_color_palettes()

        self.style = ttk.Style()
        self.style.theme_use('clam')
        self.initialize_styles_structure()

        # --- Determine User Data Directory and File ---
        app_name = "MathSpeedTrainer"
        system = platform.system()

        if system == "Windows":
            base_dir = Path(os.getenv('APPDATA', Path.home() / "AppData" / "Roaming"))
        elif system == "Darwin":
            base_dir = Path.home() / "Library" / "Application Support"
        else:
            xdg_config_home = os.getenv('XDG_CONFIG_HOME')
            if xdg_config_home:
                base_dir = Path(xdg_config_home)
            else:
                base_dir = Path.home() / ".config"
        
        self.user_data_dir = base_dir / app_name
        
        try:
            self.user_data_dir.mkdir(parents=True, exist_ok=True)
        except OSError as e:
            print(f"Warning: Could not create user data directory {self.user_data_dir}: {e}")
            self.user_data_dir = Path(".") 
            messagebox.showwarning("Data Storage Warning", 
                                   f"Could not create application data folder.\nUser data will be saved in the program's current directory.",
                                   parent=self.root) # Added parent

        self.user_data_file = self.user_data_dir / "math_trainer_user_data.json"

        # --- App State Initializations ---
        self.current_frame = None
        self.game_active = False
        self.practice_active = False
        self.game_end_time = None
        self.current_question_details: Optional[Dict] = None
        self.question_start_time = None
        
        self.questions_answered = 0 # Session specific
        self.correct_answers = 0    # Session specific
        self.session_operation_times = defaultdict(list)
        self.session_operation_correct = defaultdict(int)
        self.session_operation_incorrect = defaultdict(int)
        
        # Persistent lists for practice modes
        self.persistently_wrong_questions = [] 
        self.persistently_slow_questions = []  
        
        # Practice mode state variables
        self.current_practice_type = None 
        self.current_practice_list = []
        self.current_practice_op_for_session = None # For targeted op practice

        # User progress
        self.current_level = 1
        self.current_xp = 0
        self.xp_needed = self.calculate_xp_for_level(2) # Initial XP for level 1->2
        self.session_history = []
        
        # Game settings defaults
        self.game_duration = 60
        self.operations = {
            "addition": True, "subtraction": True, "multiplication": True, "division": True,
            "powers": False, "roots": False, "percentages": False
        }
        self.answer_mode = "text"
        
        # Operation statistics
        self.operation_stats = {
            op: {"correct": 0, "incorrect": 0, "avg_time": 0.0, "total_answered_for_avg": 0}
            for op in self.operations.keys()
        }
        
        # Difficulty configuration
        self.difficulty_brackets = [
            (1, 5, {"range": (1, 10), "digits": 1}),
            (6, 10, {"range": (1, 50), "digits": 2}),
            (11, 15, {"range": (10, 100), "digits": 2}),
            (16, 20, {"range": (10, 200), "digits": 3, "mult_range": (2, 20)}),
            (21, 30, {"range": (50, 500), "digits": 3, "mult_range": (2, 50)}),
            (31, 50, {"range": (100, 1000), "digits": 3, "mult_range": (10, 100)}),
            (51, 100, {"range": (100, 9999), "digits": 4, "mult_range": (10, 200)})
        ]
        
        # Canvas and Figure Info for Matplotlib (for proper cleanup)
        self.overview_canvas_info = None
        self.operations_canvas_info = None
        self.progress_canvas_info = None
        self.predictions_canvas_info = None
        self.overall_time_trend_canvas_info = None
        self.op_time_trend_canvases_info = {}
        self.pred_text_widget_ref = None # Reference for the Text widget in predictions

        # Practice mode specific (already in your provided code, just ensuring it's here)
        self.practice_questions_total = 0
        self.practice_questions_answered = 0
        self.practice_correct_answers = 0
        # self.current_practice_op = "" # Replaced by current_practice_op_for_session and current_practice_type

        # --- Initial Self-Assessment ---
        self.initial_assessment_done = False 
        self.self_assessment_level = "good"  # Default

        # --- Load Data, Apply Theme, Setup UI ---
        self.load_user_data() # This will load theme and assessment status if saved
        self.apply_theme() 

        self.notebook = ttk.Notebook(root, style="TNotebook")
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)
        
        self.home_frame = ttk.Frame(self.notebook, padding=20)
        self.game_frame = ttk.Frame(self.notebook, padding=20)
        self.practice_frame = ttk.Frame(self.notebook, padding=20)
        self.stats_frame = ttk.Frame(self.notebook, padding=10)
        self.settings_frame = ttk.Frame(self.notebook, padding=20)
        
        self.notebook.add(self.home_frame, text="Home")
        self.notebook.add(self.game_frame, text="Game")
        self.notebook.add(self.practice_frame, text="Practice")
        self.notebook.add(self.stats_frame, text="Statistics")
        self.notebook.add(self.settings_frame, text="Settings")
        
        self.setup_home_frame()
        self.setup_game_frame()
        self.setup_practice_frame()
        self.setup_stats_frame()
        self.setup_settings_frame()
        
        self.root.bind("<Return>", self.handle_return_key)
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.auto_save_timer_id = self.root.after(300000, self.auto_save)

        # --- Prompt for initial assessment if not done ---
        # This needs to be called after the main UI is somewhat ready,
        # especially if the assessment window relies on themed elements.
        # Using `after` ensures the main loop has started and styles are applied.
        self.root.after(200, self.prompt_initial_assessment)





    def define_color_palettes(self):
        self.light_theme_colors = {
            "BG_COLOR": "#F0F0F0",
            "TEXT_COLOR": "#333333",
            "PRIMARY_COLOR": "#0078D4",
            "PRIMARY_COLOR_ACTIVE": "#005A9E", # Darker for active state
            "SECONDARY_COLOR": "#EAEAEA", 
            "ACCENT_COLOR_GREEN": "#28A745",
            "ACCENT_GREEN_ACTIVE": "#1E7E34",
            "ACCENT_COLOR_RED": "#DC3545",
            "ACCENT_RED_ACTIVE": "#A71D2A",
            "BUTTON_TEXT_COLOR": "#FFFFFF",
            "LISTBOX_BG": "#FFFFFF",
            "LISTBOX_SELECT_BG": "#0078D4",
            "LISTBOX_SELECT_FG": "#FFFFFF",
            "ENTRY_BG": "#FFFFFF",
            "ENTRY_FG": "#333333",
            "ENTRY_BORDER": "#CCCCCC",
            "TREEVIEW_BG": "#FFFFFF",
            "TREEVIEW_FG": "#333333",
            "TREEVIEW_HEADING_BG": "#0078D4",
            "TREEVIEW_HEADING_FG": "#FFFFFF",
            "TREEVIEW_HEADING_BG_ACTIVE": "#005A9E",
            "PROGRESS_TROUGH": "#D0D0D0",
            "TAB_ACTIVE_BG": "#D0D0D0", # For notebook tab hover
        }
        self.dark_theme_colors = {
            "BG_COLOR": "#2B2B2B",
            "TEXT_COLOR": "#D0D0D0",
            "PRIMARY_COLOR": "#0078D4", # Using the same blue for more pop on dark
            "PRIMARY_COLOR_ACTIVE": "#005A9E", 
            "SECONDARY_COLOR": "#3C3F41",
            "ACCENT_COLOR_GREEN": "#28A745", # Same green
            "ACCENT_GREEN_ACTIVE": "#1E7E34",
            "ACCENT_COLOR_RED": "#DC3545",   # Same red
            "ACCENT_RED_ACTIVE": "#A71D2A",
            "BUTTON_TEXT_COLOR": "#FFFFFF", # White text should be fine on these button colors
            "LISTBOX_BG": "#3C3F41",
            "LISTBOX_SELECT_BG": "#005A9E", 
            "LISTBOX_SELECT_FG": "#FFFFFF",
            "ENTRY_BG": "#3C3F41",
            "ENTRY_FG": "#D0D0D0",
            "ENTRY_BORDER": "#555555",
            "TREEVIEW_BG": "#313335", # Slightly different from frame for definition
            "TREEVIEW_FG": "#D0D0D0",
            "TREEVIEW_HEADING_BG": "#0078D4",
            "TREEVIEW_HEADING_FG": "#FFFFFF",
            "TREEVIEW_HEADING_BG_ACTIVE": "#005A9E",
            "PROGRESS_TROUGH": "#555555",
            "TAB_ACTIVE_BG": "#4F5254",
        }
        self.colors = self.light_theme_colors

    def initialize_styles_structure(self):
        self.style.configure("TFrame", padding=0) 
        self.style.configure("TLabel", font=("Segoe UI", 11))
        self.style.configure("Header.TLabel", font=("Segoe UI Semibold", 20))
        self.style.configure("SubHeader.TLabel", font=("Segoe UI Semibold", 16))
        self.style.configure("Question.TLabel", font=("Segoe UI Black", 36))
        self.style.configure("Timer.TLabel", font=("Segoe UI Semibold", 16))
        self.style.configure("Score.TLabel", font=("Segoe UI", 14))
        self.style.configure("LevelInfo.TLabel", font=("Segoe UI Semibold", 14))

        self.style.configure("TButton", font=("Segoe UI Semibold", 11), padding=(10, 5), borderwidth=0)

        self.style.configure("TNotebook", borderwidth=0)
        self.style.configure("TNotebook.Tab", font=("Segoe UI Semibold", 11), padding=(10, 5))

        self.style.configure("TLabelframe", relief="solid", borderwidth=1)
        self.style.configure("TLabelframe.Label", font=("Segoe UI Semibold", 12), padding=(5,2))

        self.style.configure("TProgressbar", thickness=20)
        
        self.style.configure("TEntry", font=("Segoe UI", 12), padding=5, relief="flat")
        self.style.configure("TSpinbox", font=("Segoe UI", 10), padding=3, relief="flat", arrowsize=12)


        self.style.configure("Treeview.Heading", font=("Segoe UI Semibold", 10), relief="flat")
        self.style.configure("Treeview", rowheight=25, font=("Segoe UI", 10))
        
        self.style.configure("TRadiobutton", font=("Segoe UI", 10))
        self.style.configure("TCheckbutton", font=("Segoe UI", 10))
        self.style.configure("TCombobox", font=("Segoe UI", 10))


    def apply_theme(self):
        if self.theme == "dark":
            self.colors = self.dark_theme_colors
        else:
            self.colors = self.light_theme_colors

        self.root.configure(bg=self.colors["BG_COLOR"])

        self.style.configure("TFrame", background=self.colors["BG_COLOR"])
        self.style.configure("TLabel", background=self.colors["BG_COLOR"], foreground=self.colors["TEXT_COLOR"])
        self.style.configure("Header.TLabel", foreground=self.colors["PRIMARY_COLOR"], background=self.colors["BG_COLOR"])
        self.style.configure("SubHeader.TLabel", foreground=self.colors["PRIMARY_COLOR"], background=self.colors["BG_COLOR"])
        self.style.configure("Question.TLabel", foreground=self.colors["TEXT_COLOR"], background=self.colors["BG_COLOR"])
        self.style.configure("Timer.TLabel", foreground=self.colors["ACCENT_COLOR_RED"], background=self.colors["BG_COLOR"])
        self.style.configure("Score.TLabel", foreground=self.colors["TEXT_COLOR"], background=self.colors["BG_COLOR"])
        self.style.configure("LevelInfo.TLabel", foreground=self.colors["PRIMARY_COLOR"], background=self.colors["BG_COLOR"])

        self.style.map("TButton",
                       background=[('active', self.colors["PRIMARY_COLOR_ACTIVE"]), ('!disabled', self.colors["PRIMARY_COLOR"])],
                       foreground=[('!disabled', self.colors["BUTTON_TEXT_COLOR"])])
        self.style.configure("Green.TButton", background=self.colors["ACCENT_COLOR_GREEN"], foreground=self.colors["BUTTON_TEXT_COLOR"])
        self.style.map("Green.TButton", background=[('active', self.colors["ACCENT_GREEN_ACTIVE"])])
        self.style.configure("Red.TButton", background=self.colors["ACCENT_COLOR_RED"], foreground=self.colors["BUTTON_TEXT_COLOR"])
        self.style.map("Red.TButton", background=[('active', self.colors["ACCENT_RED_ACTIVE"])])
        self.style.configure("Accent.TButton", background=self.colors["PRIMARY_COLOR"], foreground=self.colors["BUTTON_TEXT_COLOR"])
        self.style.map("Accent.TButton", background=[('active', self.colors["PRIMARY_COLOR_ACTIVE"])])

        self.style.configure("TNotebook", background=self.colors["BG_COLOR"])
        self.style.configure("TNotebook.Tab", background=self.colors["SECONDARY_COLOR"], foreground=self.colors["TEXT_COLOR"])
        self.style.map("TNotebook.Tab",
                       background=[("selected", self.colors["PRIMARY_COLOR"]), ('active', self.colors["TAB_ACTIVE_BG"])],
                       foreground=[("selected", self.colors["BUTTON_TEXT_COLOR"]), ('active', self.colors["TEXT_COLOR"])])

        self.style.configure("TLabelframe", background=self.colors["SECONDARY_COLOR"], bordercolor=self.colors["PRIMARY_COLOR"])
        self.style.configure("TLabelframe.Label", background=self.colors["SECONDARY_COLOR"], foreground=self.colors["PRIMARY_COLOR"])

        self.style.configure("TProgressbar", background=self.colors["ACCENT_COLOR_GREEN"], troughcolor=self.colors["PROGRESS_TROUGH"])
        
        self.style.configure("TEntry", fieldbackground=self.colors["ENTRY_BG"], foreground=self.colors["ENTRY_FG"], bordercolor=self.colors["ENTRY_BORDER"], lightcolor=self.colors["ENTRY_BORDER"], darkcolor=self.colors["ENTRY_BORDER"])
        self.style.map("TEntry", bordercolor=[('focus', self.colors["PRIMARY_COLOR"])])
        
        self.style.configure("TSpinbox", fieldbackground=self.colors["ENTRY_BG"], foreground=self.colors["ENTRY_FG"], bordercolor=self.colors["ENTRY_BORDER"], background=self.colors["ENTRY_BG"], troughcolor=self.colors["SECONDARY_COLOR"]) # troughcolor for arrows bg
        self.style.map("TSpinbox", bordercolor=[('focus', self.colors["PRIMARY_COLOR"])])

        self.style.configure("Secondary.TFrame", background=self.colors["SECONDARY_COLOR"])
        self.style.configure("Treeview.Heading", background=self.colors["TREEVIEW_HEADING_BG"], foreground=self.colors["TREEVIEW_HEADING_FG"])
        self.style.map("Treeview.Heading", background=[('active', self.colors["TREEVIEW_HEADING_BG_ACTIVE"])])
        self.style.configure("Treeview", background=self.colors["TREEVIEW_BG"], fieldbackground=self.colors["TREEVIEW_BG"], foreground=self.colors["TREEVIEW_FG"])
        
        self.style.configure("TRadiobutton", background=self.colors["SECONDARY_COLOR"], foreground=self.colors["TEXT_COLOR"])
        self.style.map("TRadiobutton", indicatorcolor=[('selected', self.colors["PRIMARY_COLOR"]), ('!selected', self.colors["TEXT_COLOR"])],
                                      foreground=[('active', self.colors["PRIMARY_COLOR"])]) # Text color on hover
        self.style.configure("TCheckbutton", background=self.colors["SECONDARY_COLOR"], foreground=self.colors["TEXT_COLOR"])
        self.style.map("TCheckbutton", indicatorcolor=[('selected', self.colors["PRIMARY_COLOR"]), ('!selected', self.colors["TEXT_COLOR"])],
                                       foreground=[('active', self.colors["PRIMARY_COLOR"])])
        
        self.style.map('TCombobox', fieldbackground=[('readonly', self.colors["ENTRY_BG"])])
        self.style.map('TCombobox', selectbackground=[('readonly', self.colors["ENTRY_BG"])]) # Background of selected item in list
        self.style.map('TCombobox', selectforeground=[('readonly', self.colors["ENTRY_FG"])]) # Foreground of selected item in list
        self.style.map('TCombobox', foreground=[('readonly', self.colors["ENTRY_FG"])])      # Text color in entry part
        self.root.option_add("*TCombobox*Listbox*Background", self.colors["LISTBOX_BG"])
        self.root.option_add("*TCombobox*Listbox*Foreground", self.colors["TEXT_COLOR"])
        self.root.option_add("*TCombobox*Listbox*selectBackground", self.colors["LISTBOX_SELECT_BG"])
        self.root.option_add("*TCombobox*Listbox*selectForeground", self.colors["LISTBOX_SELECT_FG"])

        mcq_button_bg = self.colors["PRIMARY_COLOR"]
        mcq_button_active_bg = self.colors["PRIMARY_COLOR_ACTIVE"]
        mcq_button_fg = self.colors["BUTTON_TEXT_COLOR"]
        self.style.configure("MCQ.TButton", background=mcq_button_bg, foreground=mcq_button_fg)
        self.style.map("MCQ.TButton", background=[('active', mcq_button_active_bg)])

        if hasattr(self, 'weakness_list'):
            self.weakness_list.configure(bg=self.colors["LISTBOX_BG"], fg=self.colors["TEXT_COLOR"], 
                                         selectbackground=self.colors["LISTBOX_SELECT_BG"], selectforeground=self.colors["LISTBOX_SELECT_FG"])
        if hasattr(self, 'session_listbox'):
            self.session_listbox.configure(bg=self.colors["LISTBOX_BG"], fg=self.colors["TEXT_COLOR"],
                                           selectbackground=self.colors["LISTBOX_SELECT_BG"], selectforeground=self.colors["LISTBOX_SELECT_FG"])
        if hasattr(self, 'pred_text_widget_ref') and self.pred_text_widget_ref: 
             self.pred_text_widget_ref.configure(bg=self.colors["BG_COLOR"], fg=self.colors["TEXT_COLOR"])
        if hasattr(self, 'hint_label'):
            self.hint_label.configure(foreground=self.colors["PRIMARY_COLOR"])


        if hasattr(self, 'home_session_listbox') and self.home_session_listbox:
            self.home_session_listbox.configure(
                bg=self.colors["LISTBOX_BG"], fg=self.colors["TEXT_COLOR"],
                selectbackground=self.colors["LISTBOX_SELECT_BG"], 
                selectforeground=self.colors["LISTBOX_SELECT_FG"]
            )



        if self.theme == "dark":
            pink_button_bg = "#E91E63"  # Hot Pink (good contrast on dark)
            pink_button_active_bg = "#C2185B" # Darker Pink
            pink_button_fg = "#FFFFFF"
        else: # Light theme
            pink_button_bg = "#FF80AB"  # Lighter Pink (good contrast on light)
            pink_button_active_bg = "#F06292" # Slightly Darker Pink
            pink_button_fg = "#FFFFFF" # White text usually works on pink

        self.style.configure("Pink.TButton", background=pink_button_bg, foreground=pink_button_fg)
        self.style.map("Pink.TButton", background=[('active', pink_button_active_bg)])



        if hasattr(self, 'stats_notebook'): 
            self.refresh_stats()





    def prompt_initial_assessment(self):
        if self.initial_assessment_done:
            return

        assessment_window = tk.Toplevel(self.root)
        assessment_window.title("Initial Math Skill Assessment")
        assessment_window.geometry("500x400")
        assessment_window.resizable(False, False)
        assessment_window.transient(self.root)
        assessment_window.grab_set() # Make it modal
        assessment_window.protocol("WM_DELETE_WINDOW", lambda: None) # Prevent closing with 'X'

        assessment_window.configure(bg=self.colors["BG_COLOR"])
        main_frame = ttk.Frame(assessment_window, padding=20)
        main_frame.pack(expand=True, fill=tk.BOTH)
        main_frame.configure(style="TFrame")

        ttk.Label(main_frame, text="Welcome to Math Speed Trainer!", style="SubHeader.TLabel", anchor="center").pack(pady=(0,10))
        ttk.Label(main_frame, text="To help tailor the experience, please rate your current math comfort level:",
                  wraplength=400, justify=tk.CENTER, style="TLabel").pack(pady=(0, 15))

        assessment_var = tk.StringVar(value="good") # Default selection

        options = [
            ("Bad (I need a lot of practice)", "bad"),
            ("Okay (I know the basics)", "good"),
            ("Nice (I'm fairly comfortable)", "nice"),
            ("Perfect (I'm a math whiz!)", "perfect")
        ]

        for text, value in options:
            rb = ttk.Radiobutton(main_frame, text=text, variable=assessment_var, value=value, style="TRadiobutton")
            rb.pack(anchor="w", pady=3, padx=20)

        ttk.Label(main_frame, text="Note: This setting influences long-term difficulty scaling and can only be changed by deleting all your data.",
                  wraplength=400, justify=tk.CENTER, font=("Segoe UI Italic", 9), style="TLabel").pack(pady=(15, 10))

        def submit_assessment():
            self.self_assessment_level = assessment_var.get()
            self.initial_assessment_done = True
            self.save_user_data() # Save this choice immediately
            assessment_window.destroy()
            # No need to grab_release, destroy does it.
            # Re-enable main window interaction if it was somehow disabled beyond grab_set
            self.root.attributes('-disabled', False)


        submit_btn = ttk.Button(main_frame, text="Confirm and Start", command=submit_assessment, style="Green.TButton")
        submit_btn.pack(pady=(10,0))
        
        self.root.eval(f'tk::PlaceWindow {str(assessment_window)} center')
        assessment_window.focus_set()
        # Temporarily disable interaction with the main window while this is up
        # This is an alternative to grab_set if grab_set causes issues on some platforms
        # self.root.attributes('-disabled', True) 
        assessment_window.wait_window() # Crucial: Halts execution here until assessment_window is destroyed




    def calculate_xp_for_level(self, level):
        if level <= 1: return 100
        return int(100 * (1.5 ** (level - 1)))

    def on_closing(self):
        print("Attempting to close application...") # For debugging
        try:
            # 1. Attempt to save user data
            print("Saving user data...")
            self.save_user_data()
            print("User data saved.")
        except Exception as e:
            print(f"Error saving data on close: {e}")
            # Optionally, show a messagebox to the user if saving failed critically
            # messagebox.showerror("Save Error", f"Could not save data before closing: {e}", parent=self.root)

        try:
            # 2. Cancel any pending 'after' events (like auto-save)
            if hasattr(self, 'auto_save_timer_id') and self.auto_save_timer_id:
                print(f"Cancelling auto_save_timer: {self.auto_save_timer_id}")
                self.root.after_cancel(self.auto_save_timer_id)
                self.auto_save_timer_id = None # Clear the ID
                print("Auto-save timer cancelled.")
        except Exception as e:
            print(f"Error cancelling auto_save_timer: {e}")

        try:
            # 3. Stop the Tkinter main event loop
            print("Quitting Tkinter mainloop...")
            self.root.quit() # This stops the mainloop
            print("Mainloop quit.")
        except Exception as e:
            print(f"Error quitting mainloop: {e}")
        
        try:
            # 4. Destroy the main window and its widgets
            # This should happen after quit() to ensure the event loop is not processing destroy events
            # while also trying to destroy.
            print("Destroying root window...")
            self.root.destroy()
            print("Root window destroyed.")
        except Exception as e:
            print(f"Error destroying root window: {e}")
        
        # 5. As a final measure if the script is still running (shouldn't be common with quit() and destroy())
        # This is a more forceful exit. Use with caution, but can be necessary.
        # print("Exiting Python interpreter.")
        # sys.exit(0) # Uncomment this line if the above steps are not enough


    def auto_save(self):
        self.save_user_data()
        self.auto_save_timer_id = self.root.after(300000, self.auto_save)
    
    def load_user_data(self):
        if os.path.exists(self.user_data_file):
            try:
                with open(self.user_data_file, "r") as f:
                    user_data = json.load(f)
                self.current_level = user_data.get("level", 1)
                self.current_xp = user_data.get("xp", 0)
                self.xp_needed = user_data.get("xp_needed", self.calculate_xp_for_level(self.current_level +1))
                self.operations = user_data.get("operations", self.operations)
                self.game_duration = user_data.get("game_duration", 60)
                self.answer_mode = user_data.get("answer_mode", "text")
                self.theme = user_data.get("theme", "dark") 
                self.persistently_wrong_questions = user_data.get("persistently_wrong_questions", [])
                self.persistently_slow_questions = user_data.get("persistently_slow_questions", [])
                self.initial_assessment_done = user_data.get("initial_assessment_done", False)
                self.self_assessment_level = user_data.get("self_assessment_level", "good")

                loaded_op_stats = user_data.get("operation_stats", {})
                for op_key in self.operations.keys(): 
                    if op_key in loaded_op_stats:
                        self.operation_stats[op_key] = loaded_op_stats[op_key]
                    else: 
                         self.operation_stats[op_key] = {"correct": 0, "incorrect": 0, "avg_time": 0.0, "total_answered_for_avg": 0}
                self.session_history = user_data.get("session_history", [])
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load user data: {e}")
        else:
            self.xp_needed = self.calculate_xp_for_level(self.current_level + 1)

    def save_user_data(self):
        user_data = {
            "level": self.current_level,
            "xp": self.current_xp,
            "xp_needed": self.xp_needed,
            "operations": self.operations,
            "game_duration": self.game_duration,
            "answer_mode": self.answer_mode,
            "theme": self.theme, 
            "operation_stats": self.operation_stats,
            "session_history": self.session_history,
            "persistently_wrong_questions": self.persistently_wrong_questions,
            "persistently_slow_questions": self.persistently_slow_questions,
            "initial_assessment_done": self.initial_assessment_done,
            "self_assessment_level": self.self_assessment_level,
        }
        try:
            with open(self.user_data_file, "w") as f:
                json.dump(user_data, f, indent=4)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save user data: {e}")

    def handle_return_key(self, event=None):
        focused_widget = self.root.focus_get()
        if not hasattr(self, 'notebook') or not self.notebook.tabs():
            return
            
        try:
            current_tab_index = self.notebook.index(self.notebook.select())
        except tk.TclError: 
            return

        if current_tab_index == 1: 
            if self.game_active and self.answer_mode == "text" and focused_widget == self.answer_entry:
                self.check_answer()
        elif current_tab_index == 2: 
             if self.practice_active and self.answer_mode == "text" and focused_widget == self.practice_answer_entry:
                self.check_practice_answer()
    
    def setup_home_frame(self):
        for widget in self.home_frame.winfo_children():
            widget.destroy()

        # --- Main Title ---
        title_label = ttk.Label(self.home_frame, text="Math Speed Trainer", style="Header.TLabel")
        title_label.pack(pady=(10, 30), anchor="center") # Increased top padding

        # --- User Progress Section ---
        progress_lf = ttk.LabelFrame(self.home_frame, text="Your Progress", padding=(20, 15))
        progress_lf.pack(pady=20, padx=40, fill=tk.X)

        level_info_frame = ttk.Frame(progress_lf) # No style needed, just for layout
        level_info_frame.pack(pady=(0,10), fill=tk.X)
        level_info_frame.configure(style="Secondary.TFrame") # Use secondary color for this frame's bg if defined

        self.level_label = ttk.Label(level_info_frame, text=f"Level: {self.current_level}", style="LevelInfo.TLabel")
        self.level_label.pack(side=tk.LEFT, padx=(0,30))
        
        self.xp_label = ttk.Label(level_info_frame, text=f"XP: {self.current_xp}/{self.xp_needed}", style="LevelInfo.TLabel")
        self.xp_label.pack(side=tk.LEFT)
        
        self.xp_progress = ttk.Progressbar(progress_lf, orient="horizontal", length=400, mode="determinate", style="TProgressbar")
        self.xp_progress.pack(pady=(5, 10), fill=tk.X)
        self.update_xp_display()
        

        # --- Main Action Buttons Section ---
        buttons_lf = ttk.LabelFrame(self.home_frame, text="Get Started", padding=(20,15))
        buttons_lf.pack(pady=20, padx=40, fill=tk.X)
        
        # Use a frame inside the labelframe for better button layout control
        action_buttons_frame = ttk.Frame(buttons_lf)
        action_buttons_frame.pack(pady=10)
        action_buttons_frame.configure(style="Secondary.TFrame")


        button_width = 22 # Consistent width for main action buttons
        ttk.Button(action_buttons_frame, text="🚀 Start Normal Game", command=self.start_normal_game_tab, style="Green.TButton", width=button_width).pack(pady=7, ipadx=10, ipady=6)
        ttk.Button(action_buttons_frame, text="🏋️ Practice Mode", command=self.open_practice_tab, style="Accent.TButton", width=button_width).pack(pady=7, ipadx=10, ipady=6)
        ttk.Button(action_buttons_frame, text="📊 View Statistics", command=self.open_stats_tab, style="TButton", width=button_width).pack(pady=7, ipadx=10, ipady=6)
        ttk.Button(action_buttons_frame, text="⚙️ Settings", command=self.open_settings_tab, style="TButton", width=button_width).pack(pady=7, ipadx=10, ipady=6)
        

        # --- Recent Sessions Section ---
        if self.session_history:
            recent_sessions_to_show = 7 # Show more recent sessions
            recent_frame_height = 8     # Taller listbox

            recent_lf = ttk.LabelFrame(self.home_frame, text="Recent Activity", padding=(20,15))
            recent_lf.pack(pady=20, padx=40, fill=tk.BOTH, expand=True) # Allow to expand
            
            # Listbox for recent sessions
            self.home_session_listbox = tk.Listbox(recent_lf, font=("Segoe UI", 10), height=recent_frame_height, 
                                             relief="flat", borderwidth=1,
                                             bg=self.colors["LISTBOX_BG"], fg=self.colors["TEXT_COLOR"],
                                             selectbackground=self.colors["LISTBOX_SELECT_BG"], 
                                             selectforeground=self.colors["LISTBOX_SELECT_FG"],
                                             activestyle='none') # No selection box needed here
            self.home_session_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, pady=(0,5))
            
            recent_scrollbar = ttk.Scrollbar(recent_lf, orient="vertical", command=self.home_session_listbox.yview)
            recent_scrollbar.pack(side=tk.RIGHT, fill=tk.Y, pady=(0,5))
            self.home_session_listbox.config(yscrollcommand=recent_scrollbar.set)
            
            # Populate the listbox
            for session in reversed(self.session_history[-recent_sessions_to_show:]): # Show more logs
                date_str = session.get("date", "Unknown")
                correct = session.get("correct", 0)
                total = session.get("total", 0)
                accuracy = session.get("accuracy", 0)
                avg_time = session.get("avg_time", 0)
                level_at_end = session.get("level_at_end", "-")
                
                session_text = f"📅 {date_str} | Lvl: {level_at_end} | ✅ {correct}/{total} ({accuracy:.0f}%) | ⏱️ {avg_time:.1f}s avg"
                self.home_session_listbox.insert(tk.END, session_text)
        else:
            no_history_lf = ttk.LabelFrame(self.home_frame, text="Recent Activity", padding=15)
            no_history_lf.pack(pady=20, padx=40, fill=tk.X)
            ttk.Label(no_history_lf, text="No game sessions recorded yet. Play a game to see your history!", 
                      font=("Segoe UI Italic", 10), style="TLabel", wraplength=300, justify=tk.CENTER).pack(pady=10)
    
    def update_xp_display(self):
        if hasattr(self, 'level_label'):
            self.level_label.config(text=f"Level: {self.current_level}")
        if hasattr(self, 'xp_label'):
            self.xp_label.config(text=f"XP: {self.current_xp}/{self.xp_needed}")
        if hasattr(self, 'xp_progress'):
            self.xp_progress["maximum"] = self.xp_needed
            self.xp_progress["value"] = self.current_xp
        if hasattr(self, 'game_level_label'):
             self.game_level_label.config(text=f"Level: {self.current_level}")

    def start_normal_game_tab(self):
        self.notebook.select(self.game_frame)

    def open_practice_tab(self):
        self.notebook.select(self.practice_frame)
        self.update_weakness_list()
        self.update_practice_answer_mode_ui()

    def open_stats_tab(self):
        self.notebook.select(self.stats_frame)
        self.refresh_stats() # Ensure stats are current when tab is explicitly opened

    def open_settings_tab(self):
        self.notebook.select(self.settings_frame)

    def setup_game_frame(self):
        for widget in self.game_frame.winfo_children(): widget.destroy() 

        # ... (game_header setup as before) ...
        self.game_header = ttk.Frame(self.game_frame, padding=(0, 0, 0, 10)) 
        self.game_header.pack(fill=tk.X, pady=(0, 20))
        timer_frame = ttk.Frame(self.game_header) 
        timer_frame.pack(side=tk.LEFT, padx=(0,20))
        ttk.Label(timer_frame, text="⏳", font=("Segoe UI Symbol", 18), foreground=self.colors["ACCENT_COLOR_RED"]).pack(side=tk.LEFT, padx=(0,5)) 
        self.timer_label = ttk.Label(timer_frame, text=f"Time: {self.game_duration}s", style="Timer.TLabel")
        self.timer_label.pack(side=tk.LEFT)
        level_frame = ttk.Frame(self.game_header)
        level_frame.pack(side=tk.LEFT, padx=(20,20), expand=True) 
        ttk.Label(level_frame, text="🌟", font=("Segoe UI Symbol", 18), foreground=self.colors["PRIMARY_COLOR"]).pack(side=tk.LEFT, padx=(0,5))
        self.game_level_label = ttk.Label(level_frame, text=f"Level: {self.current_level}", style="LevelInfo.TLabel")
        self.game_level_label.pack(side=tk.LEFT)
        score_frame = ttk.Frame(self.game_header)
        score_frame.pack(side=tk.RIGHT, padx=(20,0))
        ttk.Label(score_frame, text="🎯", font=("Segoe UI Symbol", 18), foreground=self.colors["ACCENT_COLOR_GREEN"]).pack(side=tk.LEFT, padx=(0,5))
        self.score_label = ttk.Label(score_frame, text="Score: 0/0", style="Score.TLabel")
        self.score_label.pack(side=tk.LEFT)


        question_display_lf = ttk.LabelFrame(self.game_frame, text="Current Question", padding=(20, 25))
        question_display_lf.pack(pady=20, fill=tk.X, padx=20) 
        self.question_label_frame = ttk.Frame(question_display_lf) 
        self.question_label_frame.pack(expand=True) 
        self.question_label_frame.configure(style="Secondary.TFrame") 
        self.question_label = ttk.Label(self.question_label_frame, text="Press Start to begin", style="Question.TLabel", anchor="center")
        self.question_label.pack(pady=10) 
        
        # --- Answer Input Area ---
        self.answer_input_frame = ttk.Frame(self.game_frame, padding=(0,15,0,15))
        self.answer_input_frame.pack(pady=10, expand=True) 

        self.text_answer_frame = ttk.Frame(self.answer_input_frame) 
        self.answer_entry = ttk.Entry(self.text_answer_frame, font=("Segoe UI Semibold", 24), width=8, justify="center") 
        self.answer_entry.pack(pady=10, ipady=8) 
        
        self.mc_answer_frame = ttk.Frame(self.answer_input_frame) 
        self.mc_buttons = []
        mc_button_style = "MCQ.TButton" 
        self.style.configure(mc_button_style, font=("Segoe UI Semibold", 14), padding=(15,10))
        for i in range(4):
            btn = ttk.Button(self.mc_answer_frame, text="", style=mc_button_style, width=10, 
                           command=lambda idx=i: self.check_mc_answer(idx))
            btn.grid(row=i//2, column=i%2, padx=10, pady=10, ipadx=20, ipady=10) 
            self.mc_buttons.append(btn)
        
        # --- Initially hide answer input frames ---
        self.text_answer_frame.pack_forget()
        self.mc_answer_frame.pack_forget()
        # self.update_game_answer_mode_ui() # Called by start_game or when settings change
        
        # --- Control Buttons: Start/Stop ---
        # ... (control_frame setup as before) ...
        self.control_frame = ttk.Frame(self.game_frame, padding=(0,10,0,0)) 
        self.control_frame.pack(pady=(20,0), side=tk.BOTTOM, fill=tk.X) 
        centered_control_frame = ttk.Frame(self.control_frame)
        centered_control_frame.pack() 
        centered_control_frame.configure(style="TFrame")
        self.start_button = ttk.Button(centered_control_frame, text="▶ Start Game", command=self.start_game, style="Green.TButton", width=15)
        self.start_button.pack(side=tk.LEFT, padx=10, ipady=5) 
        self.stop_button = ttk.Button(centered_control_frame, text="⏹ Stop Game", command=self.stop_game, style="Red.TButton", state=tk.DISABLED, width=15)
        self.stop_button.pack(side=tk.LEFT, padx=10, ipady=5)

    def update_game_answer_mode_ui(self):
        if not hasattr(self, 'text_answer_frame'): return 

        if self.game_active: # Only show if game is active
            if self.answer_mode == "text":
                self.mc_answer_frame.pack_forget()
                self.text_answer_frame.pack() # Pack it to show
                if hasattr(self, 'answer_entry'): self.answer_entry.focus_set()
            else: # mc mode
                self.text_answer_frame.pack_forget()
                self.mc_answer_frame.pack() # Pack it to show
        else: # Game not active, hide both
            self.text_answer_frame.pack_forget()
            self.mc_answer_frame.pack_forget()
    
# Inside MathSpeedTrainer class

    def setup_practice_frame(self):
        for widget in self.practice_frame.winfo_children():
            widget.destroy()

        ttk.Label(self.practice_frame, text="Practice Mode", style="SubHeader.TLabel").pack(pady=(0,15), anchor="center")
        
        self.options_main_frame_practice = ttk.Frame(self.practice_frame) 
        self.options_main_frame_practice.pack(fill=tk.X, pady=(0,15))

        # --- MODIFICATION: Frame for different practice type buttons ---
        practice_type_selection_lf = ttk.LabelFrame(self.options_main_frame_practice, text="Choose Practice Type", padding=10)
        practice_type_selection_lf.pack(side=tk.TOP, fill=tk.X, pady=(0,10))

        ttk.Button(practice_type_selection_lf, text="Targeted Operations", command=self.show_targeted_op_practice_options, style="Accent.TButton").grid(row=0, column=0, padx=5, pady=5, sticky="ew")
        ttk.Button(practice_type_selection_lf, text="Practice Mistakes", command=lambda: self.start_practice_specific_list("wrong_ones"), style="Red.TButton").grid(row=0, column=1, padx=5, pady=5, sticky="ew")
        ttk.Button(practice_type_selection_lf, text="Practice Slow Ones", command=lambda: self.start_practice_specific_list("slow_ones"), style="TButton").grid(row=0, column=2, padx=5, pady=5, sticky="ew")
        practice_type_selection_lf.grid_columnconfigure((0,1,2), weight=1)


        # --- Frame for Targeted Operation Practice (initially hidden or shown by default) ---
        self.targeted_op_practice_options_frame = ttk.Frame(self.options_main_frame_practice)
        # self.targeted_op_practice_options_frame.pack(fill=tk.X, pady=(0,15)) # Packed by show_targeted_op_practice_options

        weakness_frame = ttk.LabelFrame(self.targeted_op_practice_options_frame, text="Your Weaknesses (Lowest Accuracy First)", padding=10)
        weakness_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,10))
        
        self.weakness_list = tk.Listbox(weakness_frame, font=("Segoe UI", 10), height=5, relief="flat", borderwidth=1, 
                                        bg=self.colors["LISTBOX_BG"], fg=self.colors["TEXT_COLOR"],
                                        selectbackground=self.colors["LISTBOX_SELECT_BG"], selectforeground=self.colors["LISTBOX_SELECT_FG"])
        self.weakness_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        # ... (scrollbar for weakness_list as before) ...
        weakness_scrollbar = ttk.Scrollbar(weakness_frame, orient="vertical", command=self.weakness_list.yview)
        weakness_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.weakness_list.config(yscrollcommand=weakness_scrollbar.set)


        practice_options_lf = ttk.LabelFrame(self.targeted_op_practice_options_frame, text="Practice Options", padding=10)
        practice_options_lf.pack(side=tk.LEFT, fill=tk.Y, padx=(10,0))
        # ... (Comboboxes for operation and question count as before) ...
        op_select_frame = ttk.Frame(practice_options_lf)
        op_select_frame.pack(fill=tk.X, pady=5)
        ttk.Label(op_select_frame, text="Operation:", font=("Segoe UI", 10)).pack(side=tk.LEFT, padx=(0,5))
        self.practice_operation_var = tk.StringVar(value="Based on weakness")
        # ...
        self.practice_op_combobox = ttk.Combobox(op_select_frame, textvariable=self.practice_operation_var, state="readonly", width=18, style="TCombobox")
        self.practice_op_combobox.pack(side=tk.LEFT, expand=True, fill=tk.X)
        
        q_count_frame = ttk.Frame(practice_options_lf)
        q_count_frame.pack(fill=tk.X, pady=5)
        ttk.Label(q_count_frame, text="Questions:", font=("Segoe UI", 10)).pack(side=tk.LEFT, padx=(0,5))
        self.practice_question_count_var = tk.IntVar(value=10)
        # ...
        self.practice_q_count_combobox = ttk.Combobox(q_count_frame, textvariable=self.practice_question_count_var, state="readonly", width=5, style="TCombobox")
        self.practice_q_count_combobox.pack(side=tk.LEFT)
        
        self.start_practice_button = ttk.Button(practice_options_lf, text="Start Practice", command=self.start_practice, style="Green.TButton", width=15) # This now starts "targeted op" practice
        self.start_practice_button.pack(pady=(10,0), fill=tk.X)
        
        # --- Practice Area (common for all practice types) ---
        self.practice_area = ttk.Frame(self.practice_frame) 
        # ... (practice_question_label, hint_label, answer inputs, feedback, control buttons as before) ...
        self.practice_question_label_frame = ttk.Frame(self.practice_area)
        self.practice_question_label_frame.pack(pady=20)
        self.practice_question_label = ttk.Label(self.practice_question_label_frame, text="", style="Question.TLabel")
        self.practice_question_label.pack()
        
        self.hint_label = ttk.Label(self.practice_area, text="", font=("Segoe UI Italic", 11), wraplength=600, justify=tk.CENTER, foreground=self.colors["PRIMARY_COLOR"])
        self.hint_label.pack(pady=10)
        
        self.practice_answer_input_frame = ttk.Frame(self.practice_area)
        self.practice_answer_input_frame.pack(pady=10)

        self.practice_text_answer_frame = ttk.Frame(self.practice_answer_input_frame)
        self.practice_answer_entry = ttk.Entry(self.practice_text_answer_frame, font=("Segoe UI Semibold", 18), width=10, justify="center")
        self.practice_answer_entry.pack(pady=5, ipady=4)
        
        self.practice_mc_frame = ttk.Frame(self.practice_answer_input_frame)
        self.practice_mc_buttons = []
        # ... (mc buttons setup)
        for i in range(4):
            btn = ttk.Button(self.practice_mc_frame, text="", style="TButton", width=10,
                           command=lambda idx=i: self.check_practice_mc_answer(idx))
            btn.grid(row=i//2, column=i%2, padx=5, pady=5, ipadx=10, ipady=8)
            self.practice_mc_buttons.append(btn)


        self.practice_feedback_label = ttk.Label(self.practice_area, text="", font=("Segoe UI Semibold", 14)) 
        self.practice_feedback_label.pack(pady=10)

        self.practice_control_buttons_frame = ttk.Frame(self.practice_area)
        self.practice_control_buttons_frame.pack(pady=10)
        self.practice_submit_button = ttk.Button(self.practice_control_buttons_frame, text="Submit Answer", command=self.check_practice_answer, style="Accent.TButton", width=15)
        self.next_practice_q_button = ttk.Button(self.practice_control_buttons_frame, text="Next Question", command=self.next_practice_question, style="Accent.TButton", width=15)
        self.stop_practice_button = ttk.Button(self.practice_control_buttons_frame, text="Stop Practice", command=self.end_practice_session, style="Red.TButton", width=15)
        # Stop button initially hidden, shown when practice starts

        self.update_weakness_list() # Populates combobox values
        self.update_practice_answer_mode_ui()
        self.show_targeted_op_practice_options() # Show this by default

    def update_practice_answer_mode_ui(self):
        if not hasattr(self, 'practice_text_answer_frame'): return 

        if self.answer_mode == "text":
            self.practice_text_answer_frame.pack()
            self.practice_mc_frame.pack_forget()
            if self.practice_active:
                self.practice_submit_button.pack(side=tk.LEFT, padx=5)
                if hasattr(self, 'practice_answer_entry'): self.practice_answer_entry.focus_set()
        else: 
            self.practice_text_answer_frame.pack_forget()
            self.practice_mc_frame.pack()
            if hasattr(self, 'practice_submit_button'): self.practice_submit_button.pack_forget() 
        
        if self.practice_active and hasattr(self, 'practice_feedback_label') and self.practice_feedback_label.cget("text") != "":
            if hasattr(self, 'next_practice_q_button'): self.next_practice_q_button.pack(side=tk.LEFT, padx=5)
            if self.answer_mode == "text" and hasattr(self, 'practice_submit_button'): self.practice_submit_button.pack_forget()
        else:
            if hasattr(self, 'next_practice_q_button'): self.next_practice_q_button.pack_forget()
            if self.practice_active and self.answer_mode == "text" and hasattr(self, 'practice_submit_button'): self.practice_submit_button.pack(side=tk.LEFT, padx=5)





    def show_targeted_op_practice_options(self):
        """Shows the UI for selecting operations, weaknesses, and question count."""
        if hasattr(self, 'targeted_op_practice_options_frame'):
            self.targeted_op_practice_options_frame.pack(fill=tk.X, pady=(0,0)) # Show it
        # Potentially hide other specific list practice UI elements if they exist and are visible

    def start_practice(self): # This is now for "Targeted Operation" practice
        self.current_practice_type = "targeted_op" # Identify the type
        selected_op_display = self.practice_operation_var.get()
        
        if selected_op_display == "Based on weakness":
            # ... (existing logic to pick weakest op) ...
            if not self.weakness_list.get(0): 
                messagebox.showinfo("Practice", "No weaknesses identified. Defaulting to Addition.", parent=self.root)
                self.current_practice_op_for_session = "addition" # Use a session-specific var
            else:
                weakest_op_str = self.weakness_list.get(0).split(":")[0].lower()
                self.current_practice_op_for_session = weakest_op_str
        else: 
            self.current_practice_op_for_session = selected_op_display.lower()

        # ... (rest of existing start_practice logic: check if op enabled, set question count) ...
        if not self.operations.get(self.current_practice_op_for_session, False) and self.current_practice_op_for_session not in ["addition", "subtraction", "multiplication", "division"]:
            enabled_ops_list = [op for op, enabled in self.operations.items() if enabled]
            if not enabled_ops_list:
                messagebox.showerror("Error", "No operations enabled in settings.", parent=self.root)
                return
            self.current_practice_op_for_session = random.choice(enabled_ops_list)
            messagebox.showinfo("Practice", f"Selected practice operation was disabled. Practicing {self.current_practice_op_for_session.capitalize()} instead.", parent=self.root)

        self.practice_questions_total = self.practice_question_count_var.get()
        self.practice_questions_answered = 0
        self.practice_correct_answers = 0
        self.practice_active = True

        if hasattr(self, 'options_main_frame_practice'): self.options_main_frame_practice.pack_forget()
        if hasattr(self, 'practice_area'): self.practice_area.pack(fill=tk.BOTH, expand=True, pady=10)
        if hasattr(self, 'stop_practice_button'): self.stop_practice_button.pack(side=tk.RIGHT, padx=5)


        self.next_practice_question() # This will use self.current_practice_op_for_session
        self.update_practice_answer_mode_ui()


    def start_practice_specific_list(self, list_type):
        self.current_practice_type = list_type # "wrong_ones" or "slow_ones"
        
        if list_type == "wrong_ones":
            self.current_practice_list = list(self.persistently_wrong_questions) # Work on a copy
            if not self.current_practice_list:
                messagebox.showinfo("Practice Mistakes", "No mistakes recorded to practice!", parent=self.root)
                return
            practice_title = "Practicing Your Mistakes"
        elif list_type == "slow_ones":
            self.current_practice_list = list(self.persistently_slow_questions)
            if not self.current_practice_list:
                messagebox.showinfo("Practice Slow Ones", "No slow questions recorded to practice!", parent=self.root)
                return
            practice_title = "Practicing Your Slower Questions"
        else:
            return

        random.shuffle(self.current_practice_list) # Shuffle the list for variety
        self.practice_questions_total = len(self.current_practice_list)
        self.practice_questions_answered = 0
        self.practice_correct_answers = 0
        self.practice_active = True
        
        # Hide main options, show practice area
        if hasattr(self, 'options_main_frame_practice'): self.options_main_frame_practice.pack_forget()
        if hasattr(self, 'practice_area'): self.practice_area.pack(fill=tk.BOTH, expand=True, pady=10)
        if hasattr(self, 'stop_practice_button'): self.stop_practice_button.pack(side=tk.RIGHT, padx=5)


        # Update a label to show what kind of practice it is (optional)
        # e.g., self.practice_mode_info_label.config(text=practice_title)

        self.next_practice_question() # This will now use the specific list
        self.update_practice_answer_mode_ui()






    def update_weakness_list(self):
        if not hasattr(self, 'weakness_list'): return 
        self.weakness_list.delete(0, tk.END)
        weaknesses = []
        for op, stats in self.operation_stats.items():
            if not self.operations.get(op, False): continue
            total_answered = stats["correct"] + stats["incorrect"]
            if total_answered > 0:
                accuracy = (stats["correct"] / total_answered) * 100
                avg_time = stats["avg_time"]
                weaknesses.append({"name": op.capitalize(), "accuracy": accuracy, "avg_time": avg_time, "total_answered": total_answered})
        weaknesses.sort(key=lambda x: (x["accuracy"], -x["avg_time"]) if x["total_answered"] >=5 else (101, -x["avg_time"]))
        for weakness in weaknesses:
            self.weakness_list.insert(tk.END, f"{weakness['name']}: {weakness['accuracy']:.1f}% ({weakness['avg_time']:.2f}s)")
        
        if hasattr(self, 'practice_op_combobox'):
            current_selection = self.practice_operation_var.get()
            operations_list = ["Based on weakness"] + [op.capitalize() for op in self.operations.keys() if self.operations[op]]
            self.practice_op_combobox['values'] = operations_list
            if current_selection in operations_list:
                self.practice_operation_var.set(current_selection)
            elif operations_list:
                 self.practice_operation_var.set(operations_list[0])
            else:
                self.practice_operation_var.set("")

    def setup_stats_frame(self):
        for widget in self.stats_frame.winfo_children():
            widget.destroy()

        header_frame = ttk.Frame(self.stats_frame)
        header_frame.pack(fill=tk.X, pady=(0, 10))
        ttk.Label(header_frame, text="Your Statistics", style="SubHeader.TLabel").pack(anchor="center")
        
        self.stats_notebook = ttk.Notebook(self.stats_frame, style="TNotebook")
        self.stats_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.overview_tab = ttk.Frame(self.stats_notebook, padding=15)
        self.operations_tab = ttk.Frame(self.stats_notebook, padding=15)
        self.progress_tab = ttk.Frame(self.stats_notebook, padding=15)
        self.predictions_tab = ttk.Frame(self.stats_notebook, padding=15)
        # --- MODIFICATION START for Time Trends Tab ---
        self.time_trends_tab = ttk.Frame(self.stats_notebook, padding=15) # New Tab
        # --- MODIFICATION END ---
        
        self.stats_notebook.add(self.overview_tab, text="Overview")
        self.stats_notebook.add(self.operations_tab, text="Operations")
        self.stats_notebook.add(self.progress_tab, text="Progress")
        self.stats_notebook.add(self.predictions_tab, text="Predictions")
        # --- MODIFICATION START for Time Trends Tab ---
        self.stats_notebook.add(self.time_trends_tab, text="Time Trends") # Add new tab to notebook
        
        ttk.Button(self.stats_frame, text="Refresh Stats", command=self.refresh_stats, style="Accent.TButton", width=15).pack(pady=(10,0))
        self.refresh_stats() 




    def refresh_stats(self):
        if not hasattr(self, 'overview_tab'): return 
        self.setup_overview_tab_content(self.overview_tab)
        self.setup_operations_tab_content(self.operations_tab)
        self.setup_progress_tab_content(self.progress_tab)
        self.setup_predictions_tab_content(self.predictions_tab)
        if hasattr(self, 'time_trends_tab'): # Ensure tab exists
            self.setup_time_trends_tab_content(self.time_trends_tab) # New function to call
        self.update_weakness_list()

    def clear_tab_content(self, tab):
        for widget in tab.winfo_children():
            widget.destroy()
        
        # Helper to destroy canvas and close figure
        def destroy_canvas_and_fig_from_info(canvas_info_dict):
            if canvas_info_dict and canvas_info_dict.get('canvas') and canvas_info_dict.get('fig'):
                try:
                    # Check if the canvas widget still exists before trying to destroy
                    if canvas_info_dict['canvas'].get_tk_widget().winfo_exists():
                        canvas_info_dict['canvas'].get_tk_widget().destroy()
                    plt.close(canvas_info_dict['fig']) # Close the Matplotlib figure
                except Exception as e:
                    print(f"Error destroying canvas/fig: {e}")
            return None # Return None to reset the attribute

        # Corrected conditional checks to use the '_info' attributes
        if tab == self.overview_tab:
            self.overview_canvas_info = destroy_canvas_and_fig_from_info(self.overview_canvas_info)
        elif tab == self.operations_tab:
            self.operations_canvas_info = destroy_canvas_and_fig_from_info(self.operations_canvas_info)
        elif tab == self.progress_tab:
            self.progress_canvas_info = destroy_canvas_and_fig_from_info(self.progress_canvas_info)
        elif tab == self.predictions_tab:
            self.predictions_canvas_info = destroy_canvas_and_fig_from_info(self.predictions_canvas_info)
            if hasattr(self, 'pred_text_widget_ref'): 
                self.pred_text_widget_ref = None 
        elif hasattr(self, 'time_trends_tab') and tab == self.time_trends_tab:
            self.overall_time_trend_canvas_info = destroy_canvas_and_fig_from_info(self.overall_time_trend_canvas_info)
            if hasattr(self, 'op_time_trend_canvases_info'):
                for op_name in list(self.op_time_trend_canvases_info.keys()): 
                    canvas_info_dict = self.op_time_trend_canvases_info.get(op_name)
                    if canvas_info_dict: 
                        destroy_canvas_and_fig_from_info(canvas_info_dict) # This helper already returns None
                self.op_time_trend_canvases_info = {}
            
    def setup_overview_tab_content(self, tab):
        self.clear_tab_content(tab)
        
        top_frame = ttk.Frame(tab)
        top_frame.pack(fill=tk.X, pady=(0,15))

        general_frame = ttk.LabelFrame(top_frame, text="General Statistics", padding=15)
        general_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,10))
        
        total_questions_all_time = sum(stats["correct"] + stats["incorrect"] for stats in self.operation_stats.values())
        total_correct_all_time = sum(stats["correct"] for stats in self.operation_stats.values())
        accuracy_all_time = (total_correct_all_time / total_questions_all_time * 100) if total_questions_all_time > 0 else 0

        ttk.Label(general_frame, text=f"Total Questions (All Time): {total_questions_all_time}", font=("Segoe UI", 10)).pack(anchor="w", pady=2)
        ttk.Label(general_frame, text=f"Total Correct (All Time): {total_correct_all_time}", font=("Segoe UI", 10)).pack(anchor="w", pady=2)
        ttk.Label(general_frame, text=f"Overall Accuracy (All Time): {accuracy_all_time:.1f}%", font=("Segoe UI", 10)).pack(anchor="w", pady=2)
        ttk.Label(general_frame, text=f"Current Level: {self.current_level}", font=("Segoe UI", 10)).pack(anchor="w", pady=2)
        ttk.Label(general_frame, text=f"XP: {self.current_xp}/{self.xp_needed}", font=("Segoe UI", 10)).pack(anchor="w", pady=2)

        history_frame = ttk.LabelFrame(top_frame, text="Session History (Recent)", padding=15)
        history_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(10,0))
        
        self.session_listbox = tk.Listbox(history_frame, font=("Segoe UI", 9), height=6, relief="flat", borderwidth=1,
                                          bg=self.colors["LISTBOX_BG"], fg=self.colors["TEXT_COLOR"],
                                          selectbackground=self.colors["LISTBOX_SELECT_BG"], selectforeground=self.colors["LISTBOX_SELECT_FG"])
        self.session_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        history_scrollbar = ttk.Scrollbar(history_frame, orient="vertical", command=self.session_listbox.yview)
        history_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.session_listbox.config(yscrollcommand=history_scrollbar.set)
        for session in reversed(self.session_history):
            date = session.get("date", "N/A")
            acc = session.get("accuracy", 0)
            avg_t = session.get("avg_time", 0)
            self.session_listbox.insert(tk.END, f"{date}: {session['correct']}/{session['total']} ({acc:.1f}%) {avg_t:.2f}s avg")

        vis_frame = ttk.LabelFrame(tab, text="Accuracy Trend (Last 10 Sessions)", padding=10)
        vis_frame.pack(fill=tk.BOTH, expand=True, pady=(10,0))
        if self.session_history:
            try:
                fig, ax = plt.subplots(figsize=(6, 3)) 
                fig.patch.set_facecolor(self.colors["BG_COLOR"]) 
                ax.set_facecolor(self.colors["BG_COLOR"])

                dates_str = [session["date"] for session in self.session_history[-10:]]
                dates = [datetime.strptime(d, "%Y-%m-%d %H:%M") for d in dates_str]
                accuracies = [session["accuracy"] for session in self.session_history[-10:]]
                
                ax.plot(dates, accuracies, marker='o', linestyle='-', color=self.colors["PRIMARY_COLOR"], linewidth=2)
                ax.set_ylim(0, 105)
                ax.set_ylabel("Accuracy (%)", fontdict={'fontsize': 9, 'color': self.colors["TEXT_COLOR"]})
                ax.tick_params(axis='x', labelsize=8, colors=self.colors["TEXT_COLOR"])
                ax.tick_params(axis='y', labelsize=8, colors=self.colors["TEXT_COLOR"])
                for spine in ax.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])
                fig.autofmt_xdate()
                plt.tight_layout(pad=1.5)
                
                self.overview_canvas_widget = FigureCanvasTkAgg(fig, master=vis_frame)
                self.overview_canvas_widget.draw()
                self.overview_canvas_widget.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)
            except Exception as e:
                ttk.Label(vis_frame, text=f"Error generating accuracy trend: {e}").pack()
        else:
            ttk.Label(vis_frame, text="No session data for trend chart.").pack(pady=20)

    def setup_operations_tab_content(self, tab): # Example for fixing tick labels
        self.clear_tab_content(tab)
        # ... (op_stats_lf and op_tree setup as before) ...
        op_stats_lf = ttk.LabelFrame(tab, text="Performance by Operation", padding=15)
        op_stats_lf.pack(fill=tk.BOTH, expand=True, pady=(0,10))
        # ... (op_tree setup)
        cols = ("operation", "correct", "incorrect", "total", "accuracy", "avg_time")
        self.op_tree = ttk.Treeview(op_stats_lf, columns=cols, show="headings", style="Treeview")
        
        self.op_tree.heading("operation", text="Operation")
        self.op_tree.heading("correct", text="Correct")
        self.op_tree.heading("incorrect", text="Incorrect")
        self.op_tree.heading("total", text="Total")
        self.op_tree.heading("accuracy", text="Accuracy (%)")
        self.op_tree.heading("avg_time", text="Avg Time (s)")

        self.op_tree.column("operation", width=120, anchor="w")
        for col_name in cols[1:]:
            self.op_tree.column(col_name, width=80, anchor="center")

        valid_ops_for_chart = []
        for op_name, stats in self.operation_stats.items():
            correct = stats["correct"]
            incorrect = stats["incorrect"]
            total = correct + incorrect
            accuracy = (correct / total * 100) if total > 0 else 0
            avg_time = stats["avg_time"]
            self.op_tree.insert("", "end", values=(op_name.capitalize(), correct, incorrect, total, f"{accuracy:.1f}", f"{avg_time:.2f}"))
            if total > 0:
                 valid_ops_for_chart.append({
                    "name": op_name.capitalize(), "correct": correct, "incorrect": incorrect, 
                    "accuracy": accuracy, "avg_time": avg_time
                })
        self.op_tree.pack(fill=tk.BOTH, expand=True)


        vis_frame = ttk.LabelFrame(tab, text="Visualizations", padding=10)
        vis_frame.pack(fill=tk.BOTH, expand=True, pady=(10,0))

        if valid_ops_for_chart:
            try:
                fig_ops, (ax1, ax2) = plt.subplots(1, 2, figsize=(8, 3)) 
                fig_ops.patch.set_facecolor(self.colors["BG_COLOR"])
                ax1.set_facecolor(self.colors["BG_COLOR"])
                ax2.set_facecolor(self.colors["BG_COLOR"])
                
                op_names_chart = [op['name'] for op in valid_ops_for_chart]
                correct_counts = [op['correct'] for op in valid_ops_for_chart]
                incorrect_counts = [op['incorrect'] for op in valid_ops_for_chart]
                avg_times_list = [op['avg_time'] for op in valid_ops_for_chart]

                x_indices = np.arange(len(op_names_chart)) # Use indices for x-axis
                width = 0.35
                
                ax1.bar(x_indices - width/2, correct_counts, width, label='Correct', color=self.colors["ACCENT_COLOR_GREEN"])
                ax1.bar(x_indices + width/2, incorrect_counts, width, label='Incorrect', color=self.colors["ACCENT_COLOR_RED"])
                ax1.set_title('Correct vs Incorrect', fontsize=10, color=self.colors["TEXT_COLOR"])
                ax1.set_xticks(x_indices) # Set tick locations
                ax1.set_xticklabels(op_names_chart, rotation=45, ha="right", fontsize=8, color=self.colors["TEXT_COLOR"]) # Then set labels
                legend1 = ax1.legend(fontsize=8, facecolor=self.colors["SECONDARY_COLOR"], edgecolor=self.colors["TEXT_COLOR"])
                for text in legend1.get_texts(): text.set_color(self.colors["TEXT_COLOR"])
                ax1.set_ylabel("Count", fontsize=9, color=self.colors["TEXT_COLOR"])
                ax1.tick_params(axis='y', labelsize=8, colors=self.colors["TEXT_COLOR"])
                for spine in ax1.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])
                
                ax2.bar(x_indices, avg_times_list, color=self.colors["PRIMARY_COLOR"]) # Use indices for bar plotting
                ax2.set_title('Average Time', fontsize=10, color=self.colors["TEXT_COLOR"])
                ax2.set_ylabel('Time (s)', fontsize=9, color=self.colors["TEXT_COLOR"])
                ax2.set_xticks(x_indices) # Set tick locations
                ax2.set_xticklabels(op_names_chart, rotation=45, ha="right", fontsize=8, color=self.colors["TEXT_COLOR"]) # Then set labels
                ax2.tick_params(axis='y', labelsize=8, colors=self.colors["TEXT_COLOR"])
                for spine in ax2.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])
                
                plt.tight_layout(pad=1.5)
                canvas_ops_obj = FigureCanvasTkAgg(fig_ops, master=vis_frame)
                canvas_ops_obj.draw()
                canvas_ops_obj.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)
                self.operations_canvas_info = {'canvas': canvas_ops_obj, 'fig': fig_ops} # Store fig
            except Exception as e:
                ttk.Label(vis_frame, text=f"Error generating operations chart: {e}").pack()
        else:
            ttk.Label(vis_frame, text="No data for operation charts.").pack(pady=20)

    def setup_progress_tab_content(self, tab):
        self.clear_tab_content(tab)
        
        progress_lf = ttk.LabelFrame(tab, text="Level Progress", padding=15)
        progress_lf.pack(fill=tk.X, pady=(0,15))
        
        ttk.Label(progress_lf, text=f"Current Level: {self.current_level}", style="LevelInfo.TLabel").pack(anchor="w", pady=2)
        ttk.Label(progress_lf, text=f"XP: {self.current_xp}/{self.xp_needed}", style="LevelInfo.TLabel").pack(anchor="w", pady=2)
        
        xp_bar = ttk.Progressbar(progress_lf, orient="horizontal", length=400, mode="determinate", maximum=self.xp_needed, value=self.current_xp, style="TProgressbar")
        xp_bar.pack(fill=tk.X, pady=(5,0))

        vis_frame = ttk.LabelFrame(tab, text="Level Progression Over Sessions", padding=10)
        vis_frame.pack(fill=tk.BOTH, expand=True, pady=(10,0))
        if self.session_history:
            try:
                fig, ax = plt.subplots(figsize=(7, 3.5))
                fig.patch.set_facecolor(self.colors["BG_COLOR"])
                ax.set_facecolor(self.colors["BG_COLOR"])

                session_indices = range(len(self.session_history))
                levels_at_session_end = [session.get("level_at_end", 1) for session in self.session_history]
                
                ax.plot(session_indices, levels_at_session_end, marker='o', linestyle='-', color=self.colors["PRIMARY_COLOR"], linewidth=2)
                ax.set_xlabel("Session Number", fontsize=9, color=self.colors["TEXT_COLOR"])
                ax.set_ylabel("Level", fontsize=9, color=self.colors["TEXT_COLOR"])
                ax.set_ylim(bottom=0.5)
                ax.yaxis.set_major_locator(plt.MaxNLocator(integer=True))
                ax.tick_params(axis='x', labelsize=8, colors=self.colors["TEXT_COLOR"])
                ax.tick_params(axis='y', labelsize=8, colors=self.colors["TEXT_COLOR"])
                for spine in ax.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])
                if len(session_indices) > 0:
                    ax.set_xticks(session_indices)
                    if len(session_indices) > 15:
                         ax.xaxis.set_major_locator(plt.MaxNLocator(nbins=10, integer=True))

                plt.tight_layout(pad=1.5)
                self.progress_canvas_widget = FigureCanvasTkAgg(fig, master=vis_frame)
                self.progress_canvas_widget.draw()
                self.progress_canvas_widget.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)
            except Exception as e:
                ttk.Label(vis_frame, text=f"Error generating progress chart: {e}").pack()
        else:
            ttk.Label(vis_frame, text="No session data for progress chart.").pack(pady=20)




    def setup_predictions_tab_content(self, tab):
        self.clear_tab_content(tab) 
        
        predictions_info_lf = ttk.LabelFrame(tab, text="Performance Predictions", padding=15)
        predictions_info_lf.pack(fill=tk.X, pady=(0,15))

        MIN_SESSIONS_FOR_PREDICTION = 7 
        RECENT_SESSIONS_TO_CONSIDER_FOR_TREND = 15 
        RECENT_SESSIONS_FOR_WAVE_PATTERN = 7 

        if len(self.session_history) < MIN_SESSIONS_FOR_PREDICTION:
            ttk.Label(predictions_info_lf, text=f"Need at least {MIN_SESSIONS_FOR_PREDICTION} game sessions for predictions.", font=("Segoe UI", 10)).pack(pady=20)
            return

        trend_history_slice = self.session_history[-RECENT_SESSIONS_TO_CONSIDER_FOR_TREND:]
        
        avg_times_trend_hist = [s['avg_time'] for s in trend_history_slice if 'avg_time' in s and s['avg_time'] is not None and s['avg_time'] > 0]
        accuracies_trend_hist = [s['accuracy'] for s in trend_history_slice if 'accuracy' in s and s['accuracy'] is not None]
        
        can_predict_speed = len(avg_times_trend_hist) >= 3 
        can_predict_accuracy = len(accuracies_trend_hist) >= 3

        if not (can_predict_speed or can_predict_accuracy):
            ttk.Label(predictions_info_lf, text="Not enough consistent recent data for main trend prediction.", font=("Segoe UI", 10)).pack(pady=20)
            return

        trend_indices_fit_speed = np.arange(len(trend_history_slice) - len(avg_times_trend_hist), len(trend_history_slice)) if can_predict_speed else np.array([])
        trend_indices_fit_acc = np.arange(len(trend_history_slice) - len(accuracies_trend_hist), len(trend_history_slice)) if can_predict_accuracy else np.array([])
        
        session_numbers_plot_trend = np.arange(max(0, len(self.session_history) - RECENT_SESSIONS_TO_CONSIDER_FOR_TREND), len(self.session_history))
        
        self.pred_text_widget_ref = tk.Text(predictions_info_lf, height=5, width=70, relief="flat", font=("Segoe UI", 10), 
                                       bg=self.colors["BG_COLOR"], fg=self.colors["TEXT_COLOR"], 
                                       wrap=tk.WORD, borderwidth=0)
        self.pred_text_widget_ref.pack(anchor="w", padx=5, pady=5)
        self.pred_text_widget_ref.tag_configure("bold", font=("Segoe UI Semibold", 10))
        self.pred_text_widget_ref.tag_configure("small_italic", font=("Segoe UI Italic", 8))

        prediction_horizon_sessions = 30 
        future_trend_indices_pred = np.arange(len(trend_history_slice), len(trend_history_slice) + prediction_horizon_sessions)
        future_session_numbers_plot = np.arange(len(self.session_history), len(self.session_history) + prediction_horizon_sessions)

        # --- MODIFIED Helper function to extract and apply fluctuation pattern with randomness ---
        def get_randomized_fluctuation_pattern(historical_data, num_pattern_sessions, horizon_length, fit_degree=1, amplitude_variation_factor=0.2):
            if len(historical_data) < num_pattern_sessions or num_pattern_sessions < 2:
                return np.zeros(horizon_length) 

            pattern_data = np.array(historical_data[-num_pattern_sessions:])
            pattern_indices = np.arange(len(pattern_data))
            
            try:
                p_pattern_trend = np.polyfit(pattern_indices, pattern_data, fit_degree)
                local_trend_line = np.poly1d(p_pattern_trend)(pattern_indices)
                residuals_base = pattern_data - local_trend_line # This is our core wave shape
                
                generated_fluctuations = np.zeros(horizon_length)
                len_residuals = len(residuals_base)

                for i in range(0, horizon_length, len_residuals):
                    segment_len = min(len_residuals, horizon_length - i)
                    # Apply a random amplitude scaling to this segment of the pattern
                    random_amplitude_scale = 1.0 + random.uniform(-amplitude_variation_factor, amplitude_variation_factor)
                    
                    # Take a segment of the base residuals (possibly wrapped)
                    # And apply random phase shift by selecting a random start point in residuals_base
                    start_index_in_residuals = random.randint(0, len_residuals -1)
                    
                    current_segment_pattern = np.zeros(segment_len)
                    for j in range(segment_len):
                        current_segment_pattern[j] = residuals_base[(start_index_in_residuals + j) % len_residuals]

                    generated_fluctuations[i : i + segment_len] = current_segment_pattern * random_amplitude_scale
                
                return generated_fluctuations
            except np.linalg.LinAlgError: 
                return np.zeros(horizon_length)
        # --- End helper function ---

        predicted_time_30_sessions_trend = None
        poly_speed_trend = None
        speed_fluctuations = np.zeros(prediction_horizon_sessions)

        if can_predict_speed:
            try:
                degree_speed = 1 
                p_speed = np.polyfit(trend_indices_fit_speed, avg_times_trend_hist, degree_speed)
                poly_speed_trend = np.poly1d(p_speed)
                
                predicted_time_30_sessions_trend = poly_speed_trend(future_trend_indices_pred[-1]) 
                predicted_time_30_sessions_trend = max(0.5, predicted_time_30_sessions_trend) 
                
                current_avg_time = avg_times_trend_hist[-1]
                self.pred_text_widget_ref.insert(tk.END, "Avg. Time/Question (Trend): ", "bold")
                self.pred_text_widget_ref.insert(tk.END, f"Current {current_avg_time:.2f}s → Predicted {predicted_time_30_sessions_trend:.2f}s\n")

                if len(avg_times_trend_hist) >= RECENT_SESSIONS_FOR_WAVE_PATTERN:
                    speed_fluctuations = get_randomized_fluctuation_pattern(
                        avg_times_trend_hist, 
                        RECENT_SESSIONS_FOR_WAVE_PATTERN,
                        prediction_horizon_sessions,
                        amplitude_variation_factor=0.3 # Time can vary a bit more
                    )
            except Exception as e:
                 self.pred_text_widget_ref.insert(tk.END, "Avg. Time/Question (Trend): ", "bold")
                 self.pred_text_widget_ref.insert(tk.END, "Prediction unavailable.\n")

        predicted_acc_30_sessions_trend = None
        poly_acc_trend = None
        acc_fluctuations = np.zeros(prediction_horizon_sessions)

        if can_predict_accuracy:
            try:
                degree_acc = 1
                p_acc = np.polyfit(trend_indices_fit_acc, accuracies_trend_hist, degree_acc)
                poly_acc_trend = np.poly1d(p_acc)

                predicted_acc_30_sessions_trend = poly_acc_trend(future_trend_indices_pred[-1])
                predicted_acc_30_sessions_trend = min(100.0, max(0.0, predicted_acc_30_sessions_trend)) 
                
                current_accuracy = accuracies_trend_hist[-1]
                self.pred_text_widget_ref.insert(tk.END, "Accuracy (Trend): ", "bold")
                self.pred_text_widget_ref.insert(tk.END, f"Current {current_accuracy:.1f}% → Predicted {predicted_acc_30_sessions_trend:.1f}%\n")

                if len(accuracies_trend_hist) >= RECENT_SESSIONS_FOR_WAVE_PATTERN:
                    acc_fluctuations = get_randomized_fluctuation_pattern(
                        accuracies_trend_hist, 
                        RECENT_SESSIONS_FOR_WAVE_PATTERN,
                        prediction_horizon_sessions,
                        amplitude_variation_factor=0.15 # Accuracy fluctuations should be smaller
                    )
            except Exception as e:
                self.pred_text_widget_ref.insert(tk.END, "Accuracy (Trend): ", "bold")
                self.pred_text_widget_ref.insert(tk.END, "Prediction unavailable.\n")
        
        self.pred_text_widget_ref.insert(tk.END, f"\nPredictions based on trend of last {len(trend_history_slice)} sessions, with visual fluctuations from last {RECENT_SESSIONS_FOR_WAVE_PATTERN} sessions.", "small_italic")
        self.pred_text_widget_ref.config(state=tk.DISABLED)

        vis_frame = ttk.LabelFrame(tab, text="Prediction Visualizations", padding=10)
        vis_frame.pack(fill=tk.BOTH, expand=True, pady=(10,0))
        
        try:
            fig, ax1 = plt.subplots(figsize=(8, 3.5)) 
            fig.patch.set_facecolor(self.colors["BG_COLOR"])
            ax1.set_facecolor(self.colors["BG_COLOR"])

            color_time = self.colors["ACCENT_COLOR_RED"]
            ax1.set_xlabel('Session Number (Overall)', fontsize=9, color=self.colors["TEXT_COLOR"])
            ax1.set_ylabel('Avg. Time (s)', color=color_time, fontsize=9)

            # --- Small overall noise parameters ---
            overall_noise_amplitude_time = 0.05 * np.mean(avg_times_trend_hist) if avg_times_trend_hist else 0.1
            overall_noise_amplitude_acc = 0.5 # Small absolute noise for accuracy %

            if can_predict_speed and poly_speed_trend is not None:
                ax1.plot(session_numbers_plot_trend[-len(avg_times_trend_hist):], avg_times_trend_hist, color=color_time, marker='o', linestyle='-', label='Recent Avg. Time')
                
                base_future_speed_trend = poly_speed_trend(future_trend_indices_pred)
                visual_future_speed_trend = base_future_speed_trend + speed_fluctuations
                
                # Add a tiny bit of overall random noise for less smoothness
                visual_future_speed_trend += np.random.normal(0, overall_noise_amplitude_time, len(visual_future_speed_trend))
                visual_future_speed_trend = np.maximum(0.5, visual_future_speed_trend) 
                
                ax1.plot(future_session_numbers_plot, visual_future_speed_trend, color=color_time, linestyle='--', label='Predicted Avg. Time')

            ax1.tick_params(axis='y', labelcolor=color_time, labelsize=8, colors=self.colors["TEXT_COLOR"])
            ax1.tick_params(axis='x', labelsize=8, colors=self.colors["TEXT_COLOR"])
            if can_predict_speed and any(t > 0 for t in avg_times_trend_hist): 
                 ax1.invert_yaxis() 
            for spine in ax1.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])

            ax2 = ax1.twinx()
            color_acc = self.colors["PRIMARY_COLOR"]
            ax2.set_ylabel('Accuracy (%)', color=color_acc, fontsize=9)

            if can_predict_accuracy and poly_acc_trend is not None:
                ax2.plot(session_numbers_plot_trend[-len(accuracies_trend_hist):], accuracies_trend_hist, color=color_acc, marker='s', linestyle='-', label='Recent Accuracy')

                base_future_acc_trend = poly_acc_trend(future_trend_indices_pred)
                visual_future_acc_trend = base_future_acc_trend + acc_fluctuations
                
                # Add a tiny bit of overall random noise
                visual_future_acc_trend += np.random.normal(0, overall_noise_amplitude_acc, len(visual_future_acc_trend))
                visual_future_acc_trend = np.clip(visual_future_acc_trend, 0, 100) 

                ax2.plot(future_session_numbers_plot, visual_future_acc_trend, color=color_acc, linestyle='--', label='Predicted Accuracy')
                
            ax2.tick_params(axis='y', labelcolor=color_acc, labelsize=8, colors=self.colors["TEXT_COLOR"])
            ax2.set_ylim(0, 105)
            for spine in ax2.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])
            
            lines, labels = ax1.get_legend_handles_labels()
            lines2, labels2 = ax2.get_legend_handles_labels()
            legend = ax2.legend(lines + lines2, labels + labels2, loc='lower center', bbox_to_anchor=(0.5, -0.40), ncol=2, fontsize=8, frameon=False) 
            for text in legend.get_texts(): text.set_color(self.colors["TEXT_COLOR"])
            
            plt.title("Performance Trends and Future Prediction", fontsize=10, color=self.colors["TEXT_COLOR"])
            fig.tight_layout(rect=[0, 0.15, 1, 1]) 
            
            self.predictions_canvas_widget = FigureCanvasTkAgg(fig, master=vis_frame)
            self.predictions_canvas_widget.draw()
            self.predictions_canvas_widget.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        except Exception as e:
            ttk.Label(vis_frame, text=f"Error generating prediction chart: {e}").pack()
    
    def setup_settings_frame(self):
        for widget in self.settings_frame.winfo_children():
            widget.destroy()

        ttk.Label(self.settings_frame, text="Application Settings", style="SubHeader.TLabel").pack(pady=(0,20), anchor="center")

        main_settings_frame = ttk.Frame(self.settings_frame)
        main_settings_frame.pack(fill=tk.BOTH, expand=True)

        # ... (your existing theme, duration, operations, answer mode LabelFrames) ...
        theme_lf = ttk.LabelFrame(main_settings_frame, text="Appearance Theme", padding=15)
        theme_lf.pack(pady=10, fill="x", padx=20)
        self.theme_var = tk.StringVar(value=self.theme)
        ttk.Radiobutton(theme_lf, text="Light Mode", variable=self.theme_var, value="light", style="TRadiobutton").pack(anchor="w", pady=3)
        ttk.Radiobutton(theme_lf, text="Dark Mode", variable=self.theme_var, value="dark", style="TRadiobutton").pack(anchor="w", pady=3)


        duration_lf = ttk.LabelFrame(main_settings_frame, text="Game Duration", padding=15)
        duration_lf.pack(pady=10, fill="x", padx=20)
        ttk.Label(duration_lf, text="Duration (seconds):", font=("Segoe UI", 10)).pack(side=tk.LEFT, padx=(0,10))
        self.duration_var = tk.IntVar(value=self.game_duration)
        duration_spinbox = ttk.Spinbox(duration_lf, from_=30, to=300, increment=15, textvariable=self.duration_var, width=5, style="TSpinbox")
        duration_spinbox.pack(side=tk.LEFT)

        ops_lf = ttk.LabelFrame(main_settings_frame, text="Enabled Operations", padding=15)
        ops_lf.pack(pady=10, fill="x", padx=20)
        self.op_vars = {}
        op_keys = list(self.operations.keys())
        cols = 3 
        for i, op_name in enumerate(op_keys):
            var = tk.BooleanVar(value=self.operations.get(op_name, True))
            self.op_vars[op_name] = var
            cb = ttk.Checkbutton(ops_lf, text=op_name.capitalize(), variable=var, style="TCheckbutton")
            cb.grid(row=i//cols, column=i%cols, sticky="w", padx=10, pady=5)
        
        answer_mode_lf = ttk.LabelFrame(main_settings_frame, text="Answer Input Mode", padding=15)
        answer_mode_lf.pack(pady=10, fill="x", padx=20)
        self.answer_mode_var = tk.StringVar(value=self.answer_mode)
        ttk.Radiobutton(answer_mode_lf, text="Text Input (More XP)", variable=self.answer_mode_var, value="text", style="TRadiobutton").pack(anchor="w", pady=3)
        ttk.Radiobutton(answer_mode_lf, text="Multiple Choice (Less XP)", variable=self.answer_mode_var, value="mc", style="TRadiobutton").pack(anchor="w", pady=3)

        ttk.Button(main_settings_frame, text="Save Settings", command=self.save_settings, style="Green.TButton", width=18).pack(pady=20) # Adjusted pady

        # --- MODIFICATION: Add Support Button ---
        support_button_frame = ttk.Frame(main_settings_frame) # Use a frame to center or position if needed
        support_button_frame.pack(pady=(10, 0), fill=tk.X) # Add some space above

        # Define a new style for the pink button if it doesn't fit existing ones
        # This style will be configured in apply_theme
        self.style.configure("Pink.TButton", font=("Segoe UI Semibold", 10), padding=(8,4))
        # The actual background/foreground will be set in apply_theme based on current theme for contrast

        support_btn = ttk.Button(support_button_frame, text="Click me ♡",
                                 command=self.open_support_window,
                                 style="Pink.TButton", width=15) # Use a distinct style
        support_btn.pack(pady=5) # Pack it within its frame

        # --- MODIFICATION: Add Delete Data Section ---
        delete_data_lf = ttk.LabelFrame(main_settings_frame, text="Data Management", padding=15)
        delete_data_lf.pack(pady=10, fill="x", padx=20)

        delete_info_label = ttk.Label(delete_data_lf, 
                                      text="Warning: This will permanently delete all your progress, statistics, and settings, including your initial skill assessment. The application will effectively reset.",
                                      wraplength=main_settings_frame.winfo_width() - 80, # Adjust wraplength dynamically
                                      justify=tk.LEFT, style="TLabel", font=("Segoe UI Italic", 9))
        delete_info_label.pack(anchor="w", pady=(0,10))
        
        # Bind to update wraplength if window resizes (optional, can be tricky)
        # main_settings_frame.bind("<Configure>", lambda e: delete_info_label.config(wraplength=e.width - 80))


        delete_btn = ttk.Button(delete_data_lf, text="Delete All My Data",
                                command=self.confirm_delete_all_data,
                                style="Red.TButton", width=20)
        delete_btn.pack(pady=5)
        # --- END MODIFICATION ---







    def confirm_delete_all_data(self):
        response = messagebox.askyesno("Confirm Deletion", 
                                       "ARE YOU ABSOLUTELY SURE?\n\nThis will delete all your saved data (progress, stats, settings) and cannot be undone. The application will need to be restarted or will reset to its initial state.\n\nDo you want to proceed?",
                                       icon='warning', parent=self.root)
        if response:
            self.delete_all_data_action()

    def delete_all_data_action(self):
        # 1. Delete the data file
        try:
            if os.path.exists(self.user_data_file):
                os.remove(self.user_data_file)
                print(f"User data file {self.user_data_file} deleted.")
        except OSError as e:
            messagebox.showerror("Error", f"Could not delete data file: {e}\nPlease try deleting it manually:\n{self.user_data_file}", parent=self.root)
            return # Stop if file deletion fails

        # 2. Reset all relevant self attributes to defaults
        self.current_level = 1
        self.current_xp = 0
        self.xp_needed = self.calculate_xp_for_level(2)
        self.session_history = []
        self.operations = { # Reset to default operations enabled
            "addition": True, "subtraction": True, "multiplication": True, "division": True,
            "powers": False, "roots": False, "percentages": False
        }
        self.answer_mode = "text"
        self.theme = "light" # Reset theme to default
        self.operation_stats = {
            op: {"correct": 0, "incorrect": 0, "avg_time": 0.0, "total_answered_for_avg": 0}
            for op in self.operations.keys()
        }
        self.persistently_wrong_questions = []
        self.persistently_slow_questions = []
        self.initial_assessment_done = False # This is key for re-prompting
        self.self_assessment_level = "good"

        # 3. Inform user and suggest restart / or attempt a soft reset
        messagebox.showinfo("Data Deleted", "All your data has been deleted. The application will now reset to its initial state.", parent=self.root)
        
        # Soft reset: Re-initialize UI components
        # This is a bit of a heavy-handed way to "restart" without actually exiting and relaunching.
        # It might not be perfect for all scenarios but can work for many.
        
        # Destroy all widgets in notebook tabs first
        for tab_frame_name in ["home_frame", "game_frame", "practice_frame", "stats_frame", "settings_frame"]:
            if hasattr(self, tab_frame_name):
                tab_widget = getattr(self, tab_frame_name)
                for widget in tab_widget.winfo_children():
                    widget.destroy()
        
        # Re-apply theme (important after resetting self.theme)
        self.apply_theme()

        # Re-setup all frames
        self.setup_home_frame()
        self.setup_game_frame()
        self.setup_practice_frame()
        self.setup_stats_frame()
        self.setup_settings_frame() # This will now show default settings

        # Switch to home tab
        if hasattr(self, 'notebook') and self.home_frame:
            self.notebook.select(self.home_frame)

        # Re-prompt initial assessment because initial_assessment_done is False
        self.prompt_initial_assessment()






    def open_support_window(self):
        support_window = tk.Toplevel(self.root)
        support_window.title("Support Developer")
        support_window.geometry("400x200")
        support_window.resizable(False, False)
        support_window.transient(self.root) # Keep it on top of the main window
        support_window.grab_set() # Modal behavior

        # Apply theme to the Toplevel window and its internal frame
        support_window.configure(bg=self.colors["BG_COLOR"])
        main_frame = ttk.Frame(support_window, padding=20)
        main_frame.pack(expand=True, fill=tk.BOTH)
        main_frame.configure(style="TFrame") # Apply frame style for BG

        message_text = "I put a lot of effort into developing this app (really).\n\nIf you like this app, consider supporting its development!"
        
        msg_label = ttk.Label(main_frame, text=message_text, wraplength=360, justify=tk.CENTER, font=("Segoe UI", 11))
        msg_label.pack(pady=(0, 20))
        msg_label.configure(style="TLabel") # Apply label style for BG/FG

        # "Buy me a coffee" button
        coffee_button_url = "https://buymeacoffee.com/verlorengest"
        
        # Use the Pink.TButton style we defined
        coffee_btn = ttk.Button(main_frame, text="Buy me a coffee ☕", 
                                command=lambda: webbrowser.open_new_tab(coffee_button_url),
                                style="Pink.TButton", width=20)
        coffee_btn.pack(pady=10)

        # Optional: Close button for the support window
        close_btn = ttk.Button(main_frame, text="Close", command=support_window.destroy, style="TButton")
        close_btn.pack(pady=(5,0))

        # Center the window
        self.root.eval(f'tk::PlaceWindow {str(support_window)} center')
        support_window.focus_set()




    def setup_time_trends_tab_content(self, tab):
        self.clear_tab_content(tab) # Clear previous content and canvases for this specific tab
        self.setup_time_trend_charts(tab) # Call the chart generation function

    def setup_time_trend_charts(self, parent_tab_frame):
        # --- Overall Average Time Trend ---
        overall_time_lf = ttk.LabelFrame(parent_tab_frame, text="Overall Average Solve Time Trend", padding=10)
        overall_time_lf.pack(fill=tk.BOTH, expand=True, pady=(10,0))

        if len(self.session_history) >= 2:
            try:
                fig_overall, ax_overall = plt.subplots(figsize=(7, 3))
                fig_overall.patch.set_facecolor(self.colors["BG_COLOR"])
                ax_overall.set_facecolor(self.colors["BG_COLOR"])

                session_numbers = range(len(self.session_history))
                avg_times_overall = [s.get('avg_time', 0) for s in self.session_history] # Overall avg time per session

                ax_overall.plot(session_numbers, avg_times_overall, marker='o', linestyle='-', color=self.colors["PRIMARY_COLOR"], linewidth=2)
                ax_overall.set_xlabel("Session Number", fontsize=9, color=self.colors["TEXT_COLOR"])
                ax_overall.set_ylabel("Avg. Time (s)", fontsize=9, color=self.colors["TEXT_COLOR"])
                ax_overall.set_title("Overall Session Avg. Solve Time", fontsize=10, color=self.colors["TEXT_COLOR"])
                ax_overall.tick_params(axis='x', labelsize=8, colors=self.colors["TEXT_COLOR"])
                ax_overall.tick_params(axis='y', labelsize=8, colors=self.colors["TEXT_COLOR"])
                for spine in ax_overall.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])
                if len(session_numbers) > 15:
                    ax_overall.xaxis.set_major_locator(plt.MaxNLocator(nbins=10, integer=True))
                
                plt.tight_layout(pad=1.5)
                canvas_overall = FigureCanvasTkAgg(fig_overall, master=overall_time_lf)
                canvas_overall.draw()
                canvas_overall.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)
                # Store this canvas if you need to destroy it later on theme change/refresh
                # self.overall_time_trend_canvas = canvas_overall 
            except Exception as e:
                ttk.Label(overall_time_lf, text=f"Error generating overall time trend: {e}").pack()
        else:
            ttk.Label(overall_time_lf, text="Not enough session data for overall time trend.").pack(pady=20)


        # --- Per-Operation Average Time Trends ---
        op_time_lf = ttk.LabelFrame(parent_tab_frame, text="Average Solve Time Trends by Operation", padding=10)
        op_time_lf.pack(fill=tk.BOTH, expand=True, pady=(10,0))

        # Create a sub-notebook or scrollable frame if many operations
        op_trend_notebook = ttk.Notebook(op_time_lf, style="TNotebook") # Or a scrollable frame
        op_trend_notebook.pack(fill=tk.BOTH, expand=True)

        active_ops_with_data = set()
        for session in self.session_history:
            if "operations_performance" in session:
                for op_name in session["operations_performance"].keys():
                    active_ops_with_data.add(op_name)
        
        if not active_ops_with_data:
             ttk.Label(op_time_lf, text="No per-operation time data available across sessions.").pack(pady=20)
             return

        for op_name in sorted(list(active_ops_with_data)):
            op_tab = ttk.Frame(op_trend_notebook, padding=5)
            op_trend_notebook.add(op_tab, text=op_name.capitalize())

            session_indices_with_op_data = []
            op_avg_times = []

            for i, session in enumerate(self.session_history):
                if "operations_performance" in session and \
                   op_name in session["operations_performance"] and \
                   session["operations_performance"][op_name]["total"] > 0: # Ensure some questions were answered for this op
                    session_indices_with_op_data.append(i)
                    op_avg_times.append(session["operations_performance"][op_name]["avg_time"])
            
            if len(op_avg_times) >= 2:
                try:
                    fig_op, ax_op = plt.subplots(figsize=(6, 2.5)) # Smaller for tabs
                    fig_op.patch.set_facecolor(self.colors["BG_COLOR"])
                    ax_op.set_facecolor(self.colors["BG_COLOR"])

                    ax_op.plot(session_indices_with_op_data, op_avg_times, marker='.', linestyle='-', color=self.colors["ACCENT_COLOR_GREEN"], linewidth=1.5)
                    ax_op.set_xlabel("Session Number", fontsize=8, color=self.colors["TEXT_COLOR"])
                    ax_op.set_ylabel("Avg. Time (s)", fontsize=8, color=self.colors["TEXT_COLOR"])
                    # ax_op.set_title(f"{op_name.capitalize()} Avg. Time", fontsize=9, color=self.colors["TEXT_COLOR"]) # Title per tab is enough
                    ax_op.tick_params(axis='x', labelsize=7, colors=self.colors["TEXT_COLOR"])
                    ax_op.tick_params(axis='y', labelsize=7, colors=self.colors["TEXT_COLOR"])
                    for spine in ax_op.spines.values(): spine.set_edgecolor(self.colors["TEXT_COLOR"])
                    if len(session_indices_with_op_data) > 10:
                         ax_op.xaxis.set_major_locator(plt.MaxNLocator(nbins=8, integer=True))

                    plt.tight_layout(pad=1)
                    canvas_op = FigureCanvasTkAgg(fig_op, master=op_tab)
                    canvas_op.draw()
                    canvas_op.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)
                    # Store these canvases in a list/dict if you need to destroy them later
                    # if not hasattr(self, 'op_time_trend_canvases'): self.op_time_trend_canvases = {}
                    # self.op_time_trend_canvases[op_name] = canvas_op
                except Exception as e:
                    ttk.Label(op_tab, text=f"Error: {e}").pack()
            else:
                ttk.Label(op_tab, text=f"Not enough data for {op_name.capitalize()} time trend.").pack(pady=10)

    # Then, in your `setup_stats_frame` or `refresh_stats`, you would call:
    # self.setup_time_trend_charts(self.predictions_tab) # Or a new dedicated tab
    #
    # And in `clear_tab_content` for the respective tab, you'd destroy these canvases:
    # if hasattr(self, 'overall_time_trend_canvas') and self.overall_time_trend_canvas:
    #     self.overall_time_trend_canvas.get_tk_widget().destroy()
    #     self.overall_time_trend_canvas = None
    # if hasattr(self, 'op_time_trend_canvases'):
    #     for op_name, canvas in self.op_time_trend_canvases.items():
    #         if canvas: canvas.get_tk_widget().destroy()
    #     self.op_time_trend_canvases = {}




    def save_settings(self):
        new_theme = self.theme_var.get()
        if new_theme != self.theme:
            self.theme = new_theme
            self.apply_theme() 

        self.game_duration = self.duration_var.get()
        for op_name, var in self.op_vars.items():
            self.operations[op_name] = var.get()
        self.answer_mode = self.answer_mode_var.get()
        
        self.save_user_data() 
        messagebox.showinfo("Settings Saved", "Your settings have been saved.", parent=self.root)
        
        if hasattr(self, 'timer_label'): self.timer_label.config(text=f"Time: {self.game_duration}s")
        self.update_game_answer_mode_ui()
        self.update_practice_answer_mode_ui()
        self.update_weakness_list()


    def get_difficulty_params(self, level):
        params = {"range": (1,10), "digits": 1, "mult_range": (2,10)} 
        for min_lvl, max_lvl, p_bracket in self.difficulty_brackets:
            if min_lvl <= level <= max_lvl:
                params = p_bracket 
                break 
        
        if level > self.difficulty_brackets[-1][1]: 
            params = self.difficulty_brackets[-1][2].copy() 
            
            # --- MODIFICATION: Adjust scaling factor based on self_assessment_level ---
            base_scaling_divisor = 20.0 # Default scaling speed
            if self.self_assessment_level == "bad":
                base_scaling_divisor = 30.0 # Slower scaling
            elif self.self_assessment_level == "nice":
                base_scaling_divisor = 15.0 # Faster scaling
            elif self.self_assessment_level == "perfect":
                base_scaling_divisor = 10.0 # Even faster scaling
            # "good" uses the default 20.0

            factor = 1.0 + (level - self.difficulty_brackets[-1][1]) / base_scaling_divisor
            # --- END MODIFICATION ---
            
            if "range" in params:
                params["range"] = (int(params["range"][0] * factor), int(params["range"][1] * factor))
            if "mult_range" in params:
                 params["mult_range"] = (int(params["mult_range"][0] * factor), int(params["mult_range"][1] * factor))
            if "digits" in params: 
                digit_scaling_divisor = 15.0 # How many levels per digit increase
                if self.self_assessment_level == "bad": digit_scaling_divisor = 20.0
                elif self.self_assessment_level == "perfect": digit_scaling_divisor = 10.0
                params["digits"] = min(params["digits"] + int((level - self.difficulty_brackets[-1][1]) / digit_scaling_divisor) , 6) 

        # ... (rest of the range validation as before) ...
        if "range" in params and params["range"][0] >= params["range"][1]: 
            params["range"] = (max(1, params["range"][1]-1), params["range"][1]) if params["range"][1]>1 else (1,2)
        if "mult_range" in params and params["mult_range"][0] >= params["mult_range"][1]:
            params["mult_range"] = (max(1, params["mult_range"][1]-1), params["mult_range"][1]) if params["mult_range"][1]>1 else (1,2)
            params["mult_range"] = (max(1, params["mult_range"][0]), params["mult_range"][1])
        return params

    def generate_question(self, level, chosen_operation=None):
        params = self.get_difficulty_params(level)
        min_val, max_val = params["range"]
        
        enabled_ops = [op for op, enabled in self.operations.items() if enabled]
        if not enabled_ops:
            return {"text": "No operations selected!", "answer": 0, "op_type": "error", "num1":0, "num2":0, "raw_question": (0,0,"error")}

        if chosen_operation and chosen_operation in enabled_ops:
            op_type = chosen_operation
        else:
            op_type = random.choice(enabled_ops)
        
        q_text, answer, n1, n2, raw_q = "", 0, 0, 0, None

        if op_type == "addition":
            n1 = random.randint(min_val, max_val)
            n2 = random.randint(min_val, max_val)
            answer = n1 + n2
            q_text = f"{n1} + {n2} = ?"
            raw_q = (n1, n2, '+')
        elif op_type == "subtraction":
            n1 = random.randint(min_val, max_val)
            n2 = random.randint(min_val, n1) 
            if level < 10 and n1 < n2 : n1, n2 = n2, n1 
            answer = n1 - n2
            q_text = f"{n1} - {n2} = ?"
            raw_q = (n1, n2, '-')
        elif op_type == "multiplication":
            mult_min, mult_max = params.get("mult_range", (2,10))
            mult_min = max(1, mult_min) 
            mult_max = max(mult_min + 1, mult_max) 
            n1 = random.randint(mult_min, mult_max)
            n2 = random.randint(mult_min, mult_max)
            if level <= 3: n1, n2 = random.randint(1,5), random.randint(1,5)
            elif level <=7: n1, n2 = random.randint(1,10), random.randint(1,10)
            answer = n1 * n2
            q_text = f"{n1} × {n2} = ?"
            raw_q = (n1, n2, '*')
        elif op_type == "division":
            for _ in range(100): 
                div_min = 2 if level > 3 else 1
                div_max = params.get("mult_range", (2,12))[1] // 2 + 1 
                div_max = max(div_min +1, div_max)
                n2 = random.randint(div_min, div_max) 
                if n2 == 0: n2 = 1 
                quotient_min = 1
                quotient_max = params.get("mult_range", (2,12))[0] 
                quotient_max = max(quotient_min+1, quotient_max)
                answer_candidate = random.randint(quotient_min, quotient_max) 
                n1 = n2 * answer_candidate 
                if min_val <= n1 <= max_val : 
                    answer = answer_candidate
                    q_text = f"{n1} ÷ {n2} = ?"
                    raw_q = (n1, n2, '/')
                    break
            else: return self.generate_question(level, "addition")
        elif op_type == "powers" and level >= 10:
            base_max = 15 if level < 20 else (10 if level < 30 else 20) 
            exp_max = 3 if level < 25 else (4 if level < 40 else 3) 
            base_max = max(2,base_max)
            n1 = random.randint(2, base_max) 
            n2 = random.randint(2, exp_max) 
            try:
                answer = n1 ** n2
                if answer > 10000 and level < 40: 
                    return self.generate_question(level, random.choice(["addition", "multiplication"]))
                q_text = f"{n1}^{n2} = ?"
                raw_q = (n1, n2, '^')
            except OverflowError:
                 return self.generate_question(level, random.choice(["addition", "multiplication"]))
        elif op_type == "roots" and level >= 15:
            root_type = random.choice([2, 2, 3]) 
            max_base_for_root = 20 if root_type == 2 else (10 if root_type == 3 else 15)
            max_base_for_root = max(2, max_base_for_root)
            n1_ans = random.randint(2, max_base_for_root) 
            n_val = n1_ans ** root_type
            if n_val > max_val * 2 and level < 40: 
                return self.generate_question(level, random.choice(["addition", "subtraction"]))
            answer = n1_ans
            q_text = f"{'√' if root_type == 2 else '∛'}{n_val} = ?"
            raw_q = (n_val, root_type, '√')
        elif op_type == "percentages" and level >= 8:
            percent = random.randint(1, 4) * random.choice([5, 10, 20, 25]) 
            percent = min(percent, 100) 
            base_num_options = [10, 20, 40, 50, 60, 80, 100, 120, 150, 200, 250, 300, 400, 500]
            if level > 25: base_num_options.extend([600, 750, 800, 1000])
            n2 = random.choice(base_num_options) 
            n1 = percent 
            res_float = (n1 / 100) * n2
            if res_float == int(res_float): 
                answer = int(res_float)
                q_text = f"{n1}% of {n2} = ?"
                raw_q = (n1, n2, '%')
            else: return self.generate_question(level, random.choice(["addition", "multiplication"]))
        else: return self.generate_question(level, random.choice(["addition", "subtraction"]))
        return {"text": q_text, "answer": answer, "op_type": op_type, "num1": n1, "num2": n2, "raw_question": raw_q}

    def generate_mc_options(self, correct_answer, level): # Copied from previous good version
        options = {correct_answer} 
        params = self.get_difficulty_params(level)
        
        if correct_answer == 1:
            possible_distractors = [0, 2, 3, correct_answer * 2, correct_answer + random.randint(1,3)]
            if correct_answer * 10 <= 20 : possible_distractors.append(correct_answer*10) 
            random.shuffle(possible_distractors)
            for d in possible_distractors:
                if len(options) < 4:
                    options.add(d)
        else: 
            variation = max(1, int(correct_answer * 0.1)) 
            variation = min(variation, params["range"][1] // 10) 
            if variation == 0 and correct_answer != 0 : variation = 1
            if variation == 0 and correct_answer == 0: variation = random.randint(1,5)
            
            attempts = 0
            while len(options) < 4 and attempts < 20:
                offset_type = random.choice([-1, 1, -2, 2, -0.5, 0.5, -0.1, 0.1]) 
                offset_val = random.randint(1, variation + level//5) * offset_type
                
                if isinstance(correct_answer, float) or abs(offset_val) < 1: 
                    distractor = correct_answer + offset_val
                    if isinstance(correct_answer, int) and not math.isclose(distractor, round(distractor)):
                         distractor = round(distractor,1) 
                    elif isinstance(correct_answer, int):
                         distractor = round(distractor)
                else: 
                    distractor = correct_answer + int(round(offset_val)) 

                if distractor >= 0 or correct_answer < 0 : 
                    options.add(distractor)
                attempts += 1
        
        additional_attempts = 0
        base_num_for_distractors = correct_answer if correct_answer != 0 else 1
        while len(options) < 4 and additional_attempts < 20:
            op_choice = random.choice(['add', 'sub', 'mul'])
            val_offset = random.randint(1, 5)
            if op_choice == 'add':
                distractor = base_num_for_distractors + val_offset
            elif op_choice == 'sub':
                distractor = base_num_for_distractors - val_offset
            else: 
                distractor = base_num_for_distractors * random.choice([2,3,0.5]) 
                if isinstance(correct_answer, int): distractor = round(distractor)

            if distractor >= 0 or correct_answer < 0:
                 options.add(distractor)
            additional_attempts +=1

        final_options = list(options)
        if correct_answer not in final_options: 
            if len(final_options) >= 4:
                final_options.pop(random.randrange(len(final_options))) 
            final_options.append(correct_answer)

        final_options = list(dict.fromkeys(final_options)) 
        
        idx = 1
        safety_break = 0
        while len(final_options) < 4 and safety_break < 20:
            val_to_add_plus = correct_answer + idx
            val_to_add_minus = correct_answer - idx
            
            if val_to_add_plus not in final_options and (val_to_add_plus >= 0 or correct_answer < 0):
                final_options.append(val_to_add_plus)
            if len(final_options) == 4: break
            
            if val_to_add_minus not in final_options and (val_to_add_minus >= 0 or correct_answer < 0):
                final_options.append(val_to_add_minus)
            idx +=1
            safety_break +=1
            
        last_resort_val = (max(final_options) if final_options else correct_answer) + 10
        while len(final_options) < 4:
            final_options.append(last_resort_val + random.randint(1,5))
            final_options = list(dict.fromkeys(final_options)) 

        random.shuffle(final_options)
        return final_options[:4]

    def start_game(self):
        if not any(self.operations.values()):
            messagebox.showerror("Error", "No operations selected. Please enable at least one operation in Settings.", parent=self.root)
            return
        self.game_active = True
        # ... (reset session stats as before) ...
        self.questions_answered = 0
        self.correct_answers = 0
        self.session_operation_times.clear()
        self.session_operation_correct.clear()
        self.session_operation_incorrect.clear()

        self.start_button.config(state=tk.DISABLED)
        self.stop_button.config(state=tk.NORMAL)
        
        self.game_end_time = time.time() + self.game_duration
        self.update_timer()
        self.update_game_answer_mode_ui() # Show the input method
        self.next_question() # Then generate the first question

    def stop_game(self, timed_out=False):
        was_active = self.game_active # Store state before changing
        self.game_active = False
        
        # --- Hide answer input frames ---
        if hasattr(self, 'text_answer_frame'): self.text_answer_frame.pack_forget()
        if hasattr(self, 'mc_answer_frame'): self.mc_answer_frame.pack_forget()

        self.start_button.config(state=tk.NORMAL)
        self.stop_button.config(state=tk.DISABLED)
        
        if was_active and self.questions_answered > 0: # Only process if game was truly active and questions answered
            # ... (session summary and saving logic as before) ...
            accuracy = (self.correct_answers / self.questions_answered) * 100
            # ... (calculate avg_time_per_q) ...
            total_session_time_spent = 0
            total_session_questions_for_avg = 0
            for op_type_key in self.session_operation_times: # Use a different variable name
                total_session_time_spent += sum(self.session_operation_times[op_type_key])
                total_session_questions_for_avg += len(self.session_operation_times[op_type_key])
            avg_time_per_q = (total_session_time_spent / total_session_questions_for_avg) if total_session_questions_for_avg > 0 else 0

            session_data = {
                "date": datetime.now().strftime("%Y-%m-%d %H:%M"),
                "duration_setting": self.game_duration,
                "actual_duration": self.game_duration - max(0, self.game_end_time - time.time()) if self.game_end_time else self.game_duration,
                "total": self.questions_answered,
                "correct": self.correct_answers,
                "accuracy": accuracy,
                "avg_time": avg_time_per_q,
                "xp_gained_raw": self.calculate_total_session_xp(),
                "level_at_end": self.current_level,
                "operations_performance": {
                    op: {
                        "correct": self.session_operation_correct[op],
                        "total": len(self.session_operation_times[op]), # Corrected: use len of list of times
                        "avg_time": np.mean(self.session_operation_times[op]) if self.session_operation_times[op] else 0
                    } for op in self.session_operation_times # Iterate over keys of session_operation_times
                }
            }
            self.session_history.append(session_data)
            summary_msg = f"Game Over!\n\nQuestions Answered: {self.questions_answered}\nCorrect: {self.correct_answers} ({accuracy:.1f}%)\nAverage Time: {avg_time_per_q:.2f}s"
            if timed_out: summary_msg = "Time's up!\n\n" + summary_msg.split("\n\n",1)[1]
            messagebox.showinfo("Game Over", summary_msg, parent=self.root)

        elif was_active and not timed_out : # Stopped manually with no questions
             messagebox.showinfo("Game Stopped", "Game stopped. No questions were answered.", parent=self.root)
        
        self.question_label.config(text="Press Start to begin")
        if hasattr(self, 'answer_entry'): self.answer_entry.delete(0, tk.END)
        self.save_user_data()
        self.setup_home_frame()
        self.refresh_stats()

    def calculate_total_session_xp(self):
        return self.correct_answers * 10 

    def update_timer(self):
        if self.game_active:
            remaining_time = self.game_end_time - time.time()
            if remaining_time <= 0:
                self.timer_label.config(text="Time: 0s")
                self.stop_game(timed_out=True)
                return
            self.timer_label.config(text=f"Time: {int(remaining_time)}s")
            self.root.after(1000, self.update_timer)

    def next_question(self):
        if not self.game_active: return
        self.current_question_details = self.generate_question(self.current_level)
        self.question_label.config(text=self.current_question_details["text"])
        self.question_start_time = time.time()
        if self.answer_mode == "text":
            if hasattr(self, 'answer_entry'):
                self.answer_entry.delete(0, tk.END)
                self.answer_entry.focus_set()
        else: 
            options = self.generate_mc_options(self.current_question_details["answer"], self.current_level)
            if hasattr(self, 'mc_buttons'):
                for i, btn in enumerate(self.mc_buttons):
                    btn.config(text=str(options[i]), state=tk.NORMAL)
                    btn.option_value = options[i] 

    def check_answer(self, event=None): 
        if not self.game_active or self.answer_mode != "text" or not hasattr(self, 'answer_entry'): return
        try:
            user_ans_str = self.answer_entry.get().strip()
            if not user_ans_str: return 
            correct_answer = self.current_question_details["answer"]
            if isinstance(correct_answer, float):
                user_ans = float(user_ans_str)
                is_correct = math.isclose(user_ans, correct_answer, rel_tol=1e-5)
            else: 
                user_ans = int(user_ans_str)
                is_correct = (user_ans == correct_answer)
        except ValueError: is_correct = False
        self.process_answer_result(is_correct)

    def check_mc_answer(self, choice_idx):
        if not self.game_active or self.answer_mode != "mc" or not hasattr(self, 'mc_buttons'): return
        chosen_option_value = self.mc_buttons[choice_idx].option_value
        correct_answer = self.current_question_details["answer"]
        if isinstance(correct_answer, float):
            is_correct = math.isclose(float(chosen_option_value), correct_answer, rel_tol=1e-5)
        else: is_correct = (str(chosen_option_value) == str(correct_answer)) 
        for btn in self.mc_buttons: btn.config(state=tk.DISABLED)
        self.process_answer_result(is_correct)


    def process_answer_result(self, is_correct):
        if not self.current_question_details or self.question_start_time is None: return
        time_taken = time.time() - self.question_start_time
        op_type = self.current_question_details["op_type"]
        raw_question_tuple = self.current_question_details["raw_question"]
        correct_answer_val = self.current_question_details["answer"]

        # --- For Game Mode & General Stats ---
        if self.game_active or self.practice_active: # Update stats for both, but persistence logic might differ
            self.questions_answered += 1 # This is session-specific questions_answered
            self.session_operation_times[op_type].append(time_taken)

            xp_gained = 0
            if is_correct:
                if self.game_active or self.practice_active: # Only session_correct_answers for game/practice session
                    self.correct_answers += 1 # This is session-specific correct_answers
                self.session_operation_correct[op_type] += 1
                
                xp_gained = 10 
                if time_taken < 3: xp_gained += 5
                elif time_taken < 5: xp_gained += 2
                xp_gained += self.current_level // 5
                if self.answer_mode == "mc": xp_gained = int(xp_gained * 0.7)
                
                if self.game_active: # Only add XP in game mode
                    self.current_xp += xp_gained
                
                self.operation_stats[op_type]["correct"] += 1

                # --- Check if this question was in the persistently_wrong_questions list ---
                # And if we are in a "practice wrong questions" mode (to be added)
                # For now, let's assume if it's answered correctly anywhere, it could be removed
                # A better approach is to remove it only when practiced from the "wrong list"
                # This part will be handled by the specific practice mode for wrong questions.

                # --- Check for Slow Questions ---
                # Define "slow": e.g., > 1.5x average for this op_type, or > avg + 3s
                # Ensure op_stats has been populated enough for a meaningful average
                if self.operation_stats[op_type]["total_answered_for_avg"] > 5: # Need some baseline
                    avg_op_time = self.operation_stats[op_type]["avg_time"]
                    # Example thresholds for "slow"
                    is_significantly_slow = (time_taken > avg_op_time * 1.75) or \
                                            (time_taken > avg_op_time + 4 and avg_op_time > 2) # More than 4s slower if avg is already >2s

                    if is_significantly_slow:
                        # Avoid adding duplicates if already in the slow list from a previous attempt
                        already_slow = any(
                            item['raw_q'] == raw_question_tuple and item['op_type'] == op_type 
                            for item in self.persistently_slow_questions
                        )
                        if not already_slow and len(self.persistently_slow_questions) < 20: # Limit list size
                            self.persistently_slow_questions.append({
                                'raw_q': raw_question_tuple, 
                                'answer': correct_answer_val, 
                                'op_type': op_type,
                                'original_time': round(time_taken, 2),
                                'avg_at_detection': round(avg_op_time, 2)
                            })
                            # print(f"Added slow question: {raw_question_tuple}, time: {time_taken:.2f}s, avg: {avg_op_time:.2f}s")


            else: # Incorrect answer
                if self.game_active or self.practice_active:
                    self.session_operation_incorrect[op_type] += 1
                self.operation_stats[op_type]["incorrect"] += 1
                
                # --- Add to Persistently Wrong Questions ---
                # Avoid adding duplicates
                already_wrong = any(
                    item['raw_q'] == raw_question_tuple and item['op_type'] == op_type
                    for item in self.persistently_wrong_questions
                )
                if not already_wrong and len(self.persistently_wrong_questions) < 30: # Limit list size
                    self.persistently_wrong_questions.append({
                        'raw_q': raw_question_tuple, 
                        'answer': correct_answer_val, 
                        'op_type': op_type
                    })
                    # print(f"Added wrong question: {raw_question_tuple}")


            # Update running average time in persistent stats
            prev_total_answered_for_avg = self.operation_stats[op_type]["total_answered_for_avg"]
            prev_avg_time = self.operation_stats[op_type]["avg_time"]
            new_total_answered_for_avg = prev_total_answered_for_avg + 1
            self.operation_stats[op_type]["avg_time"] = \
                ((prev_avg_time * prev_total_answered_for_avg) + time_taken) / new_total_answered_for_avg
            self.operation_stats[op_type]["total_answered_for_avg"] = new_total_answered_for_avg

        # --- UI Updates based on mode ---
        if self.game_active:
            self.update_xp_and_level()
            if hasattr(self, 'score_label'): self.score_label.config(text=f"Score: {self.correct_answers}/{self.questions_answered}")
            self.next_question()
        elif self.practice_active: 
            # This is the generic practice mode handling
            # Specific practice modes (wrong/slow) will have their own logic after this call
            self.practice_questions_answered +=1
            if is_correct: self.practice_correct_answers +=1
            
            feedback_text = "Correct!" if is_correct else f"Incorrect. Answer: {self.current_question_details['answer']}"
            feedback_color = self.colors["ACCENT_COLOR_GREEN"] if is_correct else self.colors["ACCENT_COLOR_RED"]
            
            if hasattr(self, 'practice_feedback_label'): self.practice_feedback_label.config(text=feedback_text, foreground=feedback_color)
            
            # --- Handle removal for specific practice types ---
            if self.current_practice_type == "wrong_ones" and is_correct:
                # Find and remove the question from self.persistently_wrong_questions
                q_to_remove = {'raw_q': raw_question_tuple, 'op_type': op_type} # Answer not needed for matching raw_q
                self.persistently_wrong_questions = [
                    q for q in self.persistently_wrong_questions if not (q['raw_q'] == q_to_remove['raw_q'] and q['op_type'] == q_to_remove['op_type'])
                ]
                self.save_user_data() # Save immediately after removal
                feedback_text += " (Removed from your mistakes list!)"
                if hasattr(self, 'practice_feedback_label'): self.practice_feedback_label.config(text=feedback_text)


            elif self.current_practice_type == "slow_ones":
                # If re-attempted, remove from slow list (or mark as improved)
                # For simplicity, let's remove it on any re-attempt from this mode.
                # A more advanced system could check if the new time is better.
                q_to_remove = {'raw_q': raw_question_tuple, 'op_type': op_type}
                self.persistently_slow_questions = [
                    q for q in self.persistently_slow_questions if not (q['raw_q'] == q_to_remove['raw_q'] and q['op_type'] == q_to_remove['op_type'])
                ]
                self.save_user_data()
                if is_correct:
                    feedback_text += " (Re-attempted slow question.)"
                    if hasattr(self, 'practice_feedback_label'): self.practice_feedback_label.config(text=feedback_text)


            if self.answer_mode == "text":
                if hasattr(self, 'practice_answer_entry'): self.practice_answer_entry.config(state=tk.DISABLED)
                if hasattr(self, 'practice_submit_button'): self.practice_submit_button.pack_forget()
            else:
                if hasattr(self, 'practice_mc_buttons'):
                    for btn in self.practice_mc_buttons: btn.config(state=tk.DISABLED)
            
            if hasattr(self, 'next_practice_q_button'):
                self.next_practice_q_button.pack(side=tk.LEFT, padx=5)
                self.next_practice_q_button.focus_set()


    def update_xp_and_level(self):
        leveled_up = False
        while self.current_xp >= self.xp_needed:
            self.current_xp -= self.xp_needed
            self.current_level += 1
            self.xp_needed = self.calculate_xp_for_level(self.current_level + 1)
            leveled_up = True
        if leveled_up: messagebox.showinfo("Level Up!", f"Congratulations! You've reached Level {self.current_level}!", parent=self.root)
        self.update_xp_display()
        if hasattr(self, 'game_level_label'):
            self.game_level_label.config(text=f"Level: {self.current_level}")

    def start_practice(self):
        selected_op_display = self.practice_operation_var.get()
        if selected_op_display == "Based on weakness":
            if not self.weakness_list.get(0): 
                messagebox.showinfo("Practice", "No weaknesses identified. Defaulting to Addition.", parent=self.root)
                self.current_practice_op = "addition"
            else:
                weakest_op_str = self.weakness_list.get(0).split(":")[0].lower()
                self.current_practice_op = weakest_op_str
        else: self.current_practice_op = selected_op_display.lower()
        if not self.operations.get(self.current_practice_op, False) and self.current_practice_op not in ["addition", "subtraction", "multiplication", "division"]:
            enabled_ops_list = [op for op, enabled in self.operations.items() if enabled]
            if not enabled_ops_list:
                messagebox.showerror("Error", "No operations enabled in settings.", parent=self.root)
                return
            self.current_practice_op = random.choice(enabled_ops_list)
            messagebox.showinfo("Practice", f"Selected practice op was disabled. Practicing {self.current_practice_op.capitalize()} instead.", parent=self.root)
        self.practice_questions_total = self.practice_question_count_var.get()
        self.practice_questions_answered = 0
        self.practice_correct_answers = 0
        self.practice_active = True
        
        if hasattr(self, 'options_main_frame_practice'): self.options_main_frame_practice.pack_forget()
        if hasattr(self, 'practice_area'): self.practice_area.pack(fill=tk.BOTH, expand=True, pady=10)
        self.next_practice_question()
        self.update_practice_answer_mode_ui()

# Inside MathSpeedTrainer class

    def next_practice_question(self):
        if not self.practice_active or self.practice_questions_answered >= self.practice_questions_total:
            self.end_practice_session()
            return

        if self.current_practice_type == "targeted_op":
            # Generate question based on selected operation (self.current_practice_op_for_session)
            self.current_question_details = self.generate_question(self.current_level, self.current_practice_op_for_session)
        
        elif self.current_practice_type in ["wrong_ones", "slow_ones"]:
            if not self.current_practice_list: # Should be caught by the check above, but good safety
                self.end_practice_session()
                return
            
            question_data = self.current_practice_list[self.practice_questions_answered] # Get next from list
            raw_q = question_data['raw_q']
            n1, n2, op_char_from_raw = raw_q[0], raw_q[1], raw_q[2]
            
            # Reconstruct question text (this might need refinement based on how raw_q is stored)
            q_text_display = f"{n1} {op_char_from_raw} {n2} = ?"
            if question_data['op_type'] == "powers": q_text_display = f"{n1}^{n2} = ?"
            elif question_data['op_type'] == "roots": q_text_display = f"{'√' if n2==2 else '∛'}{n1} = ?" # n2 is root type here
            elif question_data['op_type'] == "percentages": q_text_display = f"{n1}% of {n2} = ?"


            self.current_question_details = {
                "text": q_text_display,
                "answer": question_data['answer'],
                "op_type": question_data['op_type'],
                "num1": n1, # For hint generation primarily
                "num2": n2, # For hint generation
                "raw_question": raw_q 
            }
            if self.current_practice_type == "slow_ones" and 'original_time' in question_data:
                 self.hint_label.config(text=f"Original time: {question_data['original_time']}s (Avg then: {question_data.get('avg_at_detection','N/A')}s). Try faster!")
            else:
                 if hasattr(self, 'hint_label'): self.hint_label.config(text=self.generate_hint())

        else: # Fallback or unknown practice type
            self.current_question_details = self.generate_question(self.current_level, "addition")


        # --- Common UI updates for any practice question ---
        if hasattr(self, 'practice_question_label'): self.practice_question_label.config(text=self.current_question_details["text"])
        if self.current_practice_type != "slow_ones": # Avoid overwriting slow_ones specific hint
            if hasattr(self, 'hint_label'): self.hint_label.config(text=self.generate_hint())

        if hasattr(self, 'practice_feedback_label'): self.practice_feedback_label.config(text="") 
        self.question_start_time = time.time()

        if self.answer_mode == "text":
            # ... (as before: enable entry, clear, focus, show submit button) ...
            if hasattr(self, 'practice_answer_entry'):
                self.practice_answer_entry.config(state=tk.NORMAL)
                self.practice_answer_entry.delete(0, tk.END)
                self.practice_answer_entry.focus_set()
            if hasattr(self, 'practice_submit_button'): self.practice_submit_button.pack(side=tk.LEFT, padx=5)
        else: 
            options = self.generate_mc_options(self.current_question_details["answer"], self.current_level)
            # ... (as before: configure MC buttons) ...
            if hasattr(self, 'practice_mc_buttons'):
                for i, btn in enumerate(self.practice_mc_buttons):
                    btn.config(text=str(options[i]), state=tk.NORMAL)
                    btn.option_value = options[i]

        if hasattr(self, 'next_practice_q_button'): self.next_practice_q_button.pack_forget()

    def check_practice_answer(self, event=None): 
        if not self.practice_active or self.answer_mode != "text" or not hasattr(self, 'practice_answer_entry'): return
        try:
            user_ans_str = self.practice_answer_entry.get().strip()
            if not user_ans_str: return
            correct_answer = self.current_question_details["answer"]
            if isinstance(correct_answer, float):
                user_ans = float(user_ans_str)
                is_correct = math.isclose(user_ans, correct_answer, rel_tol=1e-5)
            else:
                user_ans = int(user_ans_str)
                is_correct = (user_ans == correct_answer)
        except ValueError: is_correct = False
        self.process_answer_result(is_correct)

    def check_practice_mc_answer(self, choice_idx):
        if not self.practice_active or self.answer_mode != "mc" or not hasattr(self, 'practice_mc_buttons'): return
        chosen_option_value = self.practice_mc_buttons[choice_idx].option_value
        correct_answer = self.current_question_details["answer"]
        if isinstance(correct_answer, float):
            is_correct = math.isclose(float(chosen_option_value), correct_answer, rel_tol=1e-5)
        else: is_correct = (str(chosen_option_value) == str(correct_answer))
        self.process_answer_result(is_correct)


    def end_practice_session(self):
        self.practice_active = False
        accuracy = (self.practice_correct_answers / self.practice_questions_total * 100) if self.practice_questions_total > 0 else 0
        
        practice_type_msg = self.current_practice_type.replace("_", " ").title()
        if self.current_practice_type == "targeted_op":
            practice_type_msg = f"Targeted: {self.current_practice_op_for_session.capitalize()}"

        messagebox.showinfo("Practice Complete", 
                            f"Practice session finished!\n\nType: {practice_type_msg}\n"
                            f"Answered: {self.practice_correct_answers}/{self.practice_questions_total} ({accuracy:.1f}%)", parent=self.root)
        
        if hasattr(self, 'practice_area'): self.practice_area.pack_forget()
        if hasattr(self, 'options_main_frame_practice'): self.options_main_frame_practice.pack(fill=tk.X, pady=(0,15)) # Show the main options frame again
        if hasattr(self, 'stop_practice_button'): self.stop_practice_button.pack_forget()


        self.current_practice_type = None # Reset practice type
        self.current_practice_list = []
        self.current_practice_op_for_session = None


        self.save_user_data()
        self.refresh_stats() # Update stats display including weaknesses
        self.update_weakness_list() # Update lists on practice tab itself

    def generate_hint(self):
        if not self.current_question_details: return ""
        q_details = self.current_question_details
        op, raw_q = q_details["op_type"], q_details.get("raw_question")
        if raw_q is None: return "Hint: Double check the numbers."
        val1, val2, op_char = raw_q
        hint_text = ""
        if op == "addition":
            if val1 > 10 and val2 > 10: hint_text = f"Hint: Try ({val1//10*10} + {val2//10*10}) + ({val1%10} + {val2%10})."
            else: hint_text = "Hint: Count up from the larger number."
        elif op == "subtraction":
            if val2 > 10 and val1 - val2 > 10 : hint_text = f"Hint: Try {val1} - {val2//10*10}, then subtract {val2%10}."
            else: hint_text = f"Hint: What plus {val2} equals {val1}?"
        elif op == "multiplication":
            if val2 == 10: hint_text = f"Hint: {val1} × 10 = {val1}0."
            elif val2 == 11 and val1 < 100: hint_text = f"Hint: {val1} × 11 = ({val1} × 10) + {val1}."
            elif val2 == 5: hint_text = f"Hint: {val1} × 5 = ({val1} × 10) ÷ 2."
            elif val2 == 25: hint_text = f"Hint: {val1} × 25 = ({val1} × 100) ÷ 4."
            elif val1 > 10 and val2 > 10 and (val2 % 10 != 0) and abs(val2 - round(val2,-1)) <=2 :
                near_ten, diff = round(val2, -1), val2 - round(val2, -1)
                op_sign = "+" if diff >= 0 else "-"
                hint_text = f"Hint: {val1} × ({near_ten} {op_sign} {abs(diff)}) = ({val1}×{near_ten}) {op_sign} ({val1}×{abs(diff)})."
            else: hint_text = "Hint: Break down one number into easier parts."
        elif op == "division":
            hint_text = f"Hint: What number × {val2} = {val1}?"
            if val2 !=0 and val1 % val2 == 0 and val1/val2 < 12 and val2 < 12: hint_text += f"\nThink of your {val2} times table."
        elif op == "powers":
            hint_text = f"Hint: {val1}^{val2} means {val1} multiplied by itself {val2} times."
        elif op == "roots":
            hint_text = f"Hint: What number, times itself {val2} times, gives {val1}?"
        elif op == "percentages":
            hint_text = f"Hint: {val1}% of {val2} = ({val1}/100) × {val2}.\n"
            if val1 % 10 == 0: hint_text += f"Or, 10% of {val2} is {val2/10}. You need {val1//10} of these."
        return hint_text if hint_text else "Hint: Think step by step!"

if __name__ == "__main__":
    # Create a unique AppUserModelID for your application
    MY_APP_ID = "KaanSoyler.MathSpeedTrainer.MST.1.0" 
    set_app_user_model_id(MY_APP_ID)

    root = tk.Tk()
    app = MathSpeedTrainer(root)
    root.mainloop()