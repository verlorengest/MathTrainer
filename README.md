# Math Speed Trainer

##  Overview

Math Speed Trainer is a desktop application designed to help users improve their mental arithmetic speed and accuracy. It offers various game modes, practice sessions tailored to weaknesses, detailed statistics tracking, and a progressive leveling system to keep users engaged. The application features a modern, themable user interface built with Tkinter and ttk.

##  Features

* **Adaptive Difficulty:** Questions adjust to the user's current skill level, ensuring a challenging yet manageable experience. Difficulty scaling is also influenced by an initial self-assessment.
* **Multiple Game Modes:**
    * **Normal Game:** Timed sessions where users answer as many questions as possible.
    * **Practice Mode:**
        * **Targeted Operations:** Focus on specific mathematical operations (addition, subtraction, multiplication, division, powers, roots, percentages).
        * **Practice Mistakes:** Revisit questions previously answered incorrectly.
        * **Practice Slow Ones:** Tackle questions that took longer than average to answer correctly.
* **Answer Input Options:**
    * **Text Input:** Type in the answer directly (offers more XP).
    * **Multiple Choice:** Select from four options (offers less XP).
* **User Progression:**
    * **Leveling System:** Gain XP for correct answers and level up.
    * **XP Calculation:** XP needed for the next level increases progressively.
* **Comprehensive Statistics:**
    * **Overview:** General performance, accuracy trends, recent session history.
    * **Operations:** Detailed breakdown of performance (correct, incorrect, total, accuracy, average time) for each operation.
    * **Progress:** Track level progression over sessions.
    * **Predictions:** Visualizes performance trends and offers a speculative future prediction based on recent activity.
    * **Time Trends:** Shows overall average solve time and per-operation time trends across sessions.
* **Customizable Settings:**
    * **Theme:** Light and Dark modes available.
    * **Game Duration:** Adjust the length of normal game sessions (30-300 seconds).
    * **Enabled Operations:** Select which math operations to include in games and practice.
    * **Answer Mode:** Choose between text input or multiple choice.
* **Persistent Data:** User progress, settings, and statistics are saved locally.
    * Data is stored in a platform-specific user data directory (e.g., `APPDATA` on Windows, `Application Support` on macOS, `.config` on Linux).
    * Option to delete all user data and reset the application.
* **Initial Skill Assessment:** A one-time prompt on first launch to gauge user comfort, influencing long-term difficulty scaling.
* **Hints:** Provides contextual hints during practice sessions to guide users.
* **Auto-Save:** Automatically saves progress every 5 minutes.
* **Modern UI:** Utilizes `ttk` for a more modern look and feel, with custom styling for widgets.
* **Cross-Platform:** Designed to run on Windows, macOS, and Linux.

## 🛠 Technologies Used

* **Python 3:** Core programming language.
* **Tkinter (with ttk):** For the graphical user interface.
* **Matplotlib:** For generating statistical charts and graphs.
* **NumPy:** For numerical operations, especially in data analysis for predictions.
* **Standard Python Libraries:** `json` (for data serialization), `os`, `sys`, `pathlib` (for file system operations), `platform` (for OS-specific paths), `datetime`, `time`, `random`, `math`, `collections`, `typing`, `webbrowser`.

## 🚀 Getting Started

### Prerequisites

* Python 3.x installed on your system.
* The following Python libraries:
    * `matplotlib`
    * `numpy`

    You can install them using pip:
    ```bash
    pip install matplotlib numpy
    ```

### Running the Application

1.  Ensure you have the `math_trainer_4.py` file.
2.  (Optional but Recommended) Place a `math.ico` file in the same directory as the script for the application icon.
3.  Navigate to the directory containing the script in your terminal.
4.  Run the script using Python:
    ```bash
    python math_trainer_4.py
    ```

## 💾 User Data

User data, including progress, statistics, and settings, is stored in a JSON file (`math_trainer_user_data.json`) located in a platform-specific application data directory:

* **Windows:** `C:\Users\<YourUser>\AppData\Roaming\MathSpeedTrainer`
* **macOS:** `/Users/<YourUser>/Library/Application Support/MathSpeedTrainer`
* **Linux:** `~/.config/MathSpeedTrainer` (or `$XDG_CONFIG_HOME/MathSpeedTrainer` if `XDG_CONFIG_HOME` is set)

If the application cannot create this directory, it will attempt to save data in the program's current directory and show a warning.

Users can delete all their data via an option in the Settings tab.

## 🎨 Theming

The application supports both Light and Dark themes. The theme can be changed in the Settings tab. UI elements are styled to adapt to the selected theme.


## 🐛 Known Issues/Troubleshooting

* **Icon Error (`_tkinter.TclError: bitmap ... not defined`):** This usually means the `math.ico` file was not correctly bundled with the application when creating an executable with PyInstaller, or the icon file is corrupted. Ensure you use the `--add-data "math.ico:."` flag (or equivalent in a `.spec` file) correctly.
* **Graph Rendering Issues:** Ensure Matplotlib and its TkAgg backend are functioning correctly. Older versions might have compatibility issues.
* Performance on very old systems might be impacted by frequent graph updates.
