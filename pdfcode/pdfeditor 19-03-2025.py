"""
PDF Annotation Tool - PDF EDITOR
Copyright (C) 2025 Agira Tech

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.
"""

import os
import io
import math
from datetime import date
import cairosvg
import fitz
import textwrap
from PIL import Image, ImageTk, ImageOps
import requests
from urllib.parse import urlparse, unquote
from duplicate_window import DuplicateStickyNotesPDFApp
import socket
import threading
import sys
from protocol_handler import ProtocolHandler
import customtkinter as ctk
from tkinter import filedialog, messagebox
import mysql.connector
from dotenv import load_dotenv

# to get the environment variables for exe
base_dir = getattr(sys, '_MEIPASS', os.path.abspath(os.path.dirname(__file__)))
env_path = os.path.join(base_dir, '.env')

# ✅ Load .env from the correct location
load_dotenv(env_path)


host = os.getenv("MYSQL_HOST")
user = os.getenv("MYSQL_USER")
password = os.getenv("MYSQL_PASSWORD")
database = os.getenv("MYSQL_DATABASE")

# Establish db connection
# mydb = mysql.connector.connect(
#     host="127.0.0.1",
#     user=user,
#     password=password,
#     database=database,
#     unix_socket=None
# )


# mycursor = mydb.cursor()


class StickyNotesPDFApp:
    SOCKET_PORT = 65432 # default socket port for handling the url

    def __init__(self, root):
        self.root = root
        self.root.title("IDMS PDF Editor")
        # icon for the window title
        icon_path = os.path.join(os.path.dirname(__file__), '..', 'assets', 'Atic.png')
        self.root.iconbitmap(self.set_window_icon(icon_path))
        self.zoom_factor = 1.0
        self.annotations = [] 
        self.time_redact_used = 0
        self.lock_screen = "no"
        self.stickynotezoomy = 1.0
        self.annotation_is_available = False
        self.redact_is_available = False
        self.page_rotation = 0
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.is_drawing_hollow_rect = False  # For hollow rectangle tool
        self.is_drawing_filled_rect = False
        self.is_drawing_hollow_circle = False  # Initialize the attribute
        self.is_drawing_filled_circle = False  # Initialize for filled circle too
        self.current_rectangle = None
        self.rectangle_id = None
        self.change_history = []
        self.sticky_notes = {}
        self.thumbnails = []
        self.thumbnail_labels = []  # Initialize the missing attribute
        self.thumbnail_cache = {}
        self.freehand_drawings = []
        self.redactions = []  # To store redaction info (coordinates)
        self.redo_redactions = []
        self.redaction_mode = False
        self.text_annotations = {}
        self.text_annotations_bg = {}
        self.delete_mode = False
        self.pdf_document = None
        self.current_page = None
        self.is_inverted = False
        self.is_drawing = False  # Default state of the drawing mode
        self.page_drawings = {}
        self.last_x, self.last_y = None, None  # Initialize these as well
        self.icons = {}
        self.polygon_mode = None  # 'filled' or 'hollow'
        self.polygon_size = 50
        self.start_point = None
        self.polygons = []
        self.pagenumber_url = None
        # create buttons on the window frame
        self.create_widgets()
        self.canvas.bind("<Button-1>", self.on_canvas_click) # Left click to draw
        self.canvas.bind("<Motion>", self.on_mouse_hover) # Hover to show
        self.root.bind("<Left>", self.prev_page)  # Left arrow for previous page
        self.root.bind("<Right>", self.next_page)  # Right arrow for next page
        self.active_tooltip = None
        # default page size
        self.page_width = 0
        self.page_height = 0
        self.duplicate_windows = []
        self.root.protocol("WM_DELETE_WINDOW", self.close_main_window) # to allow the main window to close
        self.setup_ipc_server()
        self.temp_file_path = None
        # api to save the annotated and redact file
        self.server_url = "https://idms-backend.blockchaincloudapps.com/api/v1/uploads/file-annotations"
        # recieving the url from the protocol handler
        if len(sys.argv) > 1:
            pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
            self.handle_url(pdf_url)

    # window icon 
    def set_window_icon(self, icon_path):
        if os.path.exists(icon_path):
            try:
                self.root.iconphoto(True, ImageTk.PhotoImage(file=icon_path))
            except Exception as e:
                print(f"Failed to set window icon. Error: {e}")
        else:
            print(f"Icon file not found: {icon_path}")

    def create_widgets(self):
        toolbar = ctk.CTkFrame(self.root)
        toolbar.pack(fill=ctk.X, pady=8)
        # button design and size
        def create_button(parent, text="", image=None, command=None, tooltip_text=""):
            button = ctk.CTkButton(
                parent,
                text=text,
                image=image,
                command=command,
                fg_color="#00498f",
                text_color="white",
                hover_color="#023261",
                font=("Arial", 12),
                width=45
            )
            button.pack(side=ctk.LEFT, padx=3, pady=2)
            button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
            button.bind("<Leave>", self.hide_tooltip)
            return button
    # load images in the button
        def load_image(relative_path, size=(25, 25)):
            if getattr(sys, 'frozen', False):
                base_dir = sys._MEIPASS
            else:
                base_dir = os.path.dirname(os.path.abspath(__file__))
            full_path = os.path.join(base_dir, relative_path)
            if relative_path.lower().endswith('.svg'):
                png_data = cairosvg.svg2png(url=full_path)
                image = Image.open(io.BytesIO(png_data))
            else:
                image = Image.open(full_path)
            image = image.resize(size, Image.LANCZOS)
            return ImageTk.PhotoImage(image)
        # for tool tip and image identification   
        self.icons = {
            "lock": load_image("assets/lock.svg"),
            "unlock": load_image("assets/unlock.svg"),
            "load_pdf": load_image("assets/folder.svg"),
            "new_window": load_image("assets/new_window.svg"),
            "zoom_out": load_image("assets/zoom_out.svg"),
            "zoom_in": load_image("assets/zoom_in.svg"),
            "refresh_pdf": load_image("assets/refresh.svg"),
            "prev_page": load_image("assets/prev_page.svg"),
            "next_page": load_image("assets/next_page.svg"),
            "undo": load_image("assets/undo.svg"),
            "highlight": load_image("assets/highlight.svg"),
            "sticky_note": load_image("assets/note.svg"),
            "thumb_pin": load_image("assets/thumb_pin_yellow.svg"),
            "rotate_90": load_image("assets/rotate_90.svg"),
            "rotate_180": load_image("assets/rotate_180.svg"),
            "rotate_270": load_image("assets/rotate_270.svg"),
            "best_fit": load_image("assets/fit_to_page.svg"),
            "best_width": load_image("assets/width.svg"),
            "best_height": load_image("assets/height.svg"),
            "invert_colors": load_image("assets/ying_yang.svg"),
            "save_pdf": load_image("assets/save.svg"),
            "zoom_area": load_image("assets/Area.svg"),
            "free_line": load_image("assets/line.svg"),
            "filled_polygon": load_image("assets/filled5polygon.svg"),
            "hollow_polygon": load_image("assets/hollow5polygon.svg"),
            "straightline": load_image("assets/straightline.svg"),
            "arrow": load_image("assets/arrow.svg"),
            "hollow_rectangle": load_image("assets/hollow_rectangle.svg"),
            "filled_rectangle": load_image("assets/filled_rectangle.svg"),
            "hollow_ellipse": load_image("assets/hollow_ellipse.svg"),
            "filled_ellipse": load_image("assets/filled_ellipse.svg"),
            "text": load_image("assets/text.svg"),
            "filled_text": load_image("assets/filled_text.svg"),
            "image": load_image("assets/image.svg"),
            "selectarrow": load_image("assets/selectarrow.svg"), 
            "redact": load_image("assets/redact.svg"), 
            "removeredact": load_image("assets/remove.svg"), 
            "eye": load_image("assets/eye.svg"), 
        }
        if self.lock_screen == "no":
            button_configs = [
                {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Annotations"},
                {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area"},
                {"image": self.icons['eye'], "command": self.show_annotated_file, "tooltip": "Show Annotated File"},
                {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Page"},
                # {"image": self.icons['load_pdf'], "command": self.load_pdf, "tooltip": "Load PDF"},
                {"image": self.icons['new_window'], "command": lambda: self.create_duplicate_window(fileurl), "tooltip": "New Window"},
                {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                # {"image": self.icons['zoom_area'], "command": self.toggle_zoom_in_area_mode, "tooltip": "Zoom Area"},
                {"image": self.icons['highlight'], "command": self.enable_highlight_mode, "tooltip": "Highlight"},
                {"image": self.icons['sticky_note'], "command": self.toggle_sticky_note_mode, "tooltip": "Sticky Note"},
                {"image": self.icons['undo'], "command": self.undo_change, "tooltip": "Undo"},
                {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors"},
                {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
                # Buttons with instance variables
                {"image": self.icons['text'], "command": self.add_text_to_pdf, "tooltip": "Add Text"},
                {"image": self.icons['filled_text'], "command": self.add_text_with_background, "tooltip": "Add Text Stamp"},
                {"image": self.icons['free_line'], "command": self.toggle_drawing, "tooltip": "Free Hand Line", "instance_var": "draw_button"},
                {"image": self.icons['filled_polygon'], "command": self.toggle_filled_polygon_mode, "tooltip": "Draw Filled Polygon", "instance_var": "filled_polygon_button"},
                {"image": self.icons['hollow_polygon'], "command": self.toggle_hollow_polygon_mode, "tooltip": "Draw Hollow Polygon", "instance_var": "hollow_polygon_button"},
                {"image": self.icons.get('image'), "command": lambda: self.attach_image_to_pdf(), "tooltip": "Attach Image"},
                {"image": self.icons['straightline'], "command": self.activate_line_tool, "tooltip": "Draw Straight Line"},
                {"image": self.icons['arrow'], "command": self.activate_arrow_tool, "tooltip": "Draw Arrow"},
                {"image": self.icons['hollow_rectangle'], "command": self.activate_hollow_rectangle_tool, "tooltip": "Draw Hollow Rectangle"},
                {"image": self.icons['filled_rectangle'], "command": self.activate_filled_rectangle_tool, "tooltip": "Filled Rectangle"},
                {"image": self.icons['hollow_ellipse'], "command": self.activate_hollow_circle_tool, "tooltip": "Draw Hollow Ellipse"},
                {"image": self.icons['filled_ellipse'], "command": self.activate_filled_circle_tool, "tooltip": "Draw Filled Ellipse"},
                {"image": self.icons['redact'], "command": self.toggle_redaction_mode, "tooltip": "Add Redaction"},
                {"image": self.icons['removeredact'], "command": self.remove_black_boxes, "tooltip": "Remove Redaction"},
            ]
        else:
            button_configs = [
                {"image": self.icons['unlock'], "command": self.lock_function, "tooltip": "Unlock Annotations"},
                {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
            ]
        current_frame = ctk.CTkFrame(toolbar)
        current_frame.pack(fill=ctk.X)
        buttons_in_row = 0

        for config in button_configs:
            if buttons_in_row >= 23:  # Start a new line
                current_frame = ctk.CTkFrame(toolbar)
                current_frame.pack(fill=ctk.X)
                buttons_in_row = 0

            # Create the button
            button = create_button(
                current_frame,
                image=config["image"],
                command=config["command"],
                tooltip_text=config["tooltip"]
            )
            buttons_in_row += 1

            # Assign to instance variable if specified
            if "instance_var" in config:
                setattr(self, config["instance_var"], button)
        # button frame        
        nav_frame = ctk.CTkFrame(current_frame, height=25)  # Place inside current_frame    
        nav_frame.pack(side=ctk.LEFT, pady=0, padx=5)  # Align with buttons
        # navigation buttons
        prev_button = ctk.CTkButton(nav_frame, text="<<<", command=self.prev_page, width=30, fg_color="transparent", text_color="black")
        prev_button.pack(side=ctk.LEFT, padx=0)
        # button for page jump
        self.page_entry = ctk.CTkEntry(nav_frame, width=45, justify="center", height=20)
        self.page_entry.pack(side=ctk.LEFT, padx=0)
        self.page_entry.insert(0, "1")
        self.page_entry.bind("<Return>", lambda event: self.go_to_page())
        # total page count
        self.page_total_label = ctk.CTkLabel(nav_frame, text="/ ?", width=25, fg_color="transparent", text_color="black")
        self.page_total_label.pack(side=ctk.LEFT, padx=0)
        # next button navigation
        next_button = ctk.CTkButton(nav_frame, text=">>>", command=self.next_page, width=30, fg_color="transparent", text_color="black")
        next_button.pack(side=ctk.LEFT, padx=0)
        # go button but hidden
        go_button = ctk.CTkButton(nav_frame, text="Go", command=self.go_to_page, width=30, fg_color="#00498f", text_color="white")
        go_button.pack_forget()

        canvas_frame = ctk.CTkFrame(self.root)
        canvas_frame.pack(fill=ctk.BOTH, expand=True)
        # thumbnail frame size
        self.thumbnail_frame = ctk.CTkFrame(canvas_frame, width=175, fg_color="lightgray")
        self.thumbnail_frame.pack(side=ctk.LEFT, fill=ctk.Y)
        self.page_entry.bind("<Return>", self.go_to_page)
        # this one is with the total thumnail frame incliding scrollbar
        self.thumbnail_canvas = ctk.CTkCanvas(self.thumbnail_frame, bg="lightgray", width=250)
        self.thumbnail_scrollbar = ctk.CTkScrollbar(self.thumbnail_frame, orientation="vertical", command=self.thumbnail_canvas.yview)
        self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
        self.thumbnail_canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
        self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        # self.thumbnail_canvas.bind("<MouseWheel>", self.on_thumbnail_scroll)
        self.inner_thumbnail_frame = ctk.CTkFrame(self.thumbnail_canvas, fg_color="lightgray")
        self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
        self.inner_thumbnail_frame.bind("<Configure>", lambda e: self.update_scroll_region())
        # total main frame size
        self.canvas = ctk.CTkCanvas(canvas_frame, bg="lightgray", width=1050, height=750) # 
        self.h_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="horizontal", command=self.canvas.xview)
        self.v_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="vertical", command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
        self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
        self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        self.canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
        # mouse wheel event for pdf render window for scrolling the pdf render
        self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
        self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
        
    # to show the button name when hover
    def button_tooltip(self, event, button_text, tooltip_text):
        """Display tooltip when hovering over a button."""
        if self.active_tooltip:
            self.active_tooltip.destroy() # to destroy automatiacally each second
        tooltip = ctk.CTkToplevel(self.root)
        tooltip.wm_overrideredirect(True) # it used for closing tooltip
        tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")  # text Position near the mouse hover
        # tooltip design
        label = ctk.CTkLabel(tooltip, text=tooltip_text, fg_color="light yellow",text_color="black", padx=5, pady=5)
        label.pack()
        if self.active_tooltip:
            self.active_tooltip.destroy()
        # activating tool tip
        self.active_tooltip = tooltip
        
    # remove or deactivate when not over
    def hide_tooltip(self, event):
        """Hide tooltip when the mouse leaves the button."""
        if self.active_tooltip: 
            self.active_tooltip.destroy()
            self.active_tooltip = None
    # load the pdf in the same frame
    def setup_ipc_server(self):
        """Set up a socket server for inter-process communication."""
        self.ipc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            self.ipc_socket.bind(("localhost", self.SOCKET_PORT)) # localhost should be changes to server doman
            self.ipc_socket.listen(1)
            threading.Thread(target=self.ipc_listener, daemon=True).start()
        except socket.error:
            # Another instance is running; send the URL to it
            if len(sys.argv) > 1:
                pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
                self.send_to_running_instance(pdf_url)
            sys.exit()
    # to listen the the url recieved from the server
    def ipc_listener(self):
        """Listen for incoming URLs and handle them."""
        while True:
            conn, _ = self.ipc_socket.accept()
            with conn:
                data = conn.recv(1024).decode("utf-8")
                if data:
                    self.root.after(0, self.handle_url, data)
    # to establish the url connection from the server
    def send_to_running_instance(self, url):
        """Send the URL to the running instance."""
        try:
            with socket.create_connection(("localhost", self.SOCKET_PORT)) as client_socket:
                client_socket.sendall(url.encode("utf-8"))
        except socket.error:
            print("Failed to send URL to running instance.")

    # to handle url and filter the page number when passed
    def handle_url(self, url):
        """Handle a new URL (load the PDF)."""
        try:
            if "?page" in url:
                self.pagenumber_url = url.split("=")[-1]
                url = url.rsplit("?", 1)[0]
                self.load_pdf(url)
            else:
                pagenumber_url = None
                self.load_pdf(url)
        except Exception as e:
            print(f"Failed to load PDF: {e}")

    # Enable or disable scrollbar based on the number of pages
    def update_scroll_region(self):
        """Ensures that the scroll region updates properly when thumbnails are added."""
        self.inner_thumbnail_frame.update_idletasks()  # Ensure layout updates first
        self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
 
        # Enable or disable scrollbar based on the number of pages
        if len(self.pdf_document) > 4:
            self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
            self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
        else:
            self.thumbnail_scrollbar.pack_forget()  # Hide scrollbar
            self.thumbnail_canvas.configure(yscrollcommand="")  # Disable scrolling


    # load pdf from the server and local 
    def load_pdf(self, file_path=None):

        """Load a PDF file from the specified path."""
        if not file_path:
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        
        if not file_path:
            print("No file selected")
            return

        print(f"Loading PDF from: {file_path}")

        self.sticky_notes.clear()  # Remove all stored sticky note data
        self.canvas.delete("sticky_note")

        self.zoom_factor = 1.0
        self.stickynotezoomy = 1.0
        self.page_rotation = 0
        self.time_redact_used = 0
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.annotations = [] # Clear annotations
        self.is_drawing_hollow_rect = False  # For hollow rectangle tool
        self.is_drawing_filled_rect = False
        self.is_drawing_hollow_circle = False  # Initialize the attribute
        self.is_drawing_filled_circle = False  # Initialize for filled circle too
        self.current_rectangle = None
        self.rectangle_id = None
        self.lock_screen = "no"
        self.annotation_is_available = False
        self.redact_is_available = False
        self.redactions = []
        self.redo_redactions = []

        try:
            parsed = urlparse(file_path)
            if parsed.scheme in ('http', 'https'):
                print("Downloading PDF from URL...")
                response = requests.get(file_path)
                response.raise_for_status()
                pdf_data = response.content
                self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
            else:
                print("Opening local PDF...")
                self.pdf_document = fitz.open(file_path)
            
            if len(self.pdf_document) == 0:
                raise ValueError("The PDF has no pages.")
            
            global fileurl
            if len(self.redactions) > 0:
                for i in range(len(self.redactions)):
                    self.remove_black_boxes()

            fileurl = file_path
            self.pdf_path = file_path
            if self.pagenumber_url is not None:
                self.current_page = int(self.pagenumber_url) - 1
                self.pagenumber_url = None
            else:
                self.current_page = 0       

            self.page_drawings = {}
            self.is_inverted = False
            self.text_annotations.clear()
            self.text_annotations_bg.clear()
            first_page = self.pdf_document[self.current_page]
            self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
            print(f"Page Width: {self.page_width}, Page Height: {self.page_height}")

            global is_small_page
            if self.page_width < 1000:
                is_small_page = "yes"
            elif self.page_width > 1000 and self.page_width <3000:
                is_small_page = "maybe"
            else:
                is_small_page = "no"

            self.render_thumbnails()
            self.render_page(self.current_page)
            # self.root.after(150, self.best_fit)
            self.root.after(500, lambda: self.update_thumbnail_selection(self.current_page))
        except Exception as e:
            print(f"Failed to load PDF: {e}")  # Debug print
            self.pdf_document = None
            self.current_page = None

        self.update_page_display()
        decoded_url = unquote(file_path)
        print(f"Loaded PDF decoded: {decoded_url}")
        global filename_pdf
        global edit_file_name
        global folderpath
        global annotated_url
        global annotatedredact_url
        global redacted_name
        global beforeexe
        try:
            filename_pdf = decoded_url.split('/')[-1]
        except:
            filename_pdf = decoded_url.split('\\')[-1]
        beforeexe = filename_pdf.rsplit('.pdf', 1)[0]
        if "_with_annotations" in decoded_url:
            annotated_url = decoded_url
            edit_file_name = beforeexe + ".pdf"
            folderpath = decoded_url.split('path=')[1]
            folderpath = folderpath.replace('_with_annotations.pdf', '.pdf')

        elif "_with_annotations_redact" in decoded_url:
            annotatedredact_url = decoded_url
            folderpath = decoded_url.split('path=')[1]
            folderpath = folderpath.replace('_with_annotations_redact.pdf', '.pdf')
        else:
            annotated_url = decoded_url.replace('.pdf', '_with_annotations.pdf')
            edit_file_name = beforeexe+ "_with_annotations.pdf"
            annotatedredact_url = decoded_url.replace('.pdf', '_with_annotations_redact.pdf')
            folderpath = decoded_url.split('path=')[1]
 
        if "_redact" in file_path:
            redacted_name = beforeexe + ".pdf"
            folderpath = decoded_url.split('path=')[1]
            folderpath = folderpath.replace('_redact.pdf', '.pdf')
        else:
            redacted_name = beforeexe + "_redact.pdf"
        
        print("------------------------------------------------------------------------------------------------------------------------------------------")
        print("file_path-------",file_path)
        print("------------------------------------------------------------------------------------------------------------------------------------------")
        print("editedfilename_pdf-------",edit_file_name)
        print("------------------------------------------------------------------------------------------------------------------------------------------")
        print("annotated_url*****************",annotated_url)
        print("------------------------------------------------------------------------------------------------------------------------------------------")
        print("folder_pathfolder_path----",folderpath)
        print("------------------------------------------------------------------------------------------------------------------------------------------")
        print("redacted_name ------------------------",redacted_name)
        print("------------------------------------------------------------------------------------------------------------------------------------------")
##########################################################################################################################################################################################

    # to show the thumnail of the pdf on the left side
    def render_thumbnails(self):
        """Render thumbnails asynchronously for better performance on large PDFs."""
        if not self.pdf_document:
            print("No PDF document loaded for thumbnails.")
            return
        # Clear previous thumbnails
        for widget in self.inner_thumbnail_frame.winfo_children():
            widget.destroy()
        global thumb_color
        thumb_color = []
        self.thumbnail_cache = {}  # Ensure proper caching
        # if the page has more than 50 pages then it will show the thumbnail in grid layout
        if (len(self.pdf_document)) > 50:
            thumbnail_width = 100
            thumbnail_height = 150
            total_pages = len(self.pdf_document)

            def load_thumbnails():
                for page_number in range(total_pages):
                    if page_number in self.thumbnail_cache:
                        continue
                    try:
                        page = self.pdf_document.load_page(page_number)

                        pix = page.get_pixmap(matrix=fitz.Matrix(0.5, 0.5))
                        img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                        img.thumbnail((thumbnail_width, thumbnail_height), Image.LANCZOS)
                        photo = ImageTk.PhotoImage(img)

                        # Store reference to avoid garbage collection
                        self.thumbnail_cache[page_number] = photo
                        self.inner_thumbnail_frame.after(0, lambda p=page_number, ph=photo: add_thumbnail(p, ph))
                    except Exception as e:
                        print(f"Error rendering thumbnail for page {page_number}: {e}")

                # Ensure scrollbar updates once all thumbnails are loaded
                self.inner_thumbnail_frame.after(500, self.update_scroll_region)
                self.inner_thumbnail_frame.after(1000, lambda: self.thumbnail_canvas.yview_moveto(0))  # Force scroll update
            def add_thumbnail(page_number, photo):
                """Add the rendered thumbnail to the UI using a grid layout."""
                row = page_number // 2  # Arrange in 2 columns per row
                col = page_number % 2
                label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
                label.image = photo  # Keep reference
                label.grid(row=row, column=col, padx=10, pady=5, sticky="w")
                # Bind click event for page selection
                label.bind("<Button-1>", self.create_page_selection_handler(page_number))
                self.thumbnails.append(label)
                thumb_color.append(label)         
        else:
            # if it has less than 50 pages then it will show the thumbnail in list layout
            thumbnail_width = 150
            thumbnail_height = 200
            total_pages = len(self.pdf_document)

            def load_thumbnails():
                for page_number in range(total_pages):
                    if page_number in self.thumbnail_cache:
                        continue
                    try:
                        page = self.pdf_document.load_page(page_number)
                        pix = page.get_pixmap(matrix=fitz.Matrix(0.5, 0.5))
                        img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                        img.thumbnail((thumbnail_width, thumbnail_height), Image.LANCZOS)
                        photo = ImageTk.PhotoImage(img)
                        self.thumbnail_cache[page_number] = photo
                        self.inner_thumbnail_frame.after(0, lambda p=page_number, ph=photo: add_thumbnail(p, ph))
                    except Exception as e:
                        print(f"Error rendering thumbnail for page {page_number}: {e}")

                # Ensure scrollbar updates once all thumbnails are loaded
                self.inner_thumbnail_frame.after(500, self.update_scroll_region)
                self.inner_thumbnail_frame.after(1000, lambda: self.thumbnail_canvas.yview_moveto(0))
            def add_thumbnail(page_number, photo):
                """Add the rendered thumbnail to the UI."""
                label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
                label.image = photo  # Store reference
                label.pack(pady=5, padx=45)
                label.bind("<Button-1>", self.create_page_selection_handler(page_number))
                self.thumbnails.append(label)
                thumb_color.append(label)

        threading.Thread(target=load_thumbnails, daemon=True).start()

######################################################################################################################################################################################################################
    # to pass the page number to the selected page
    def create_page_selection_handler(self, page_number):
        """Return a handler function to navigate to the selected page."""
        def handler(event):
            print(f"Thumbnail {page_number} clicked.")  # Debug log
            self.select_page(page_number)
        return handler
    
    # to render the page on the canvas and highlight the selected page
    def update_thumbnail_selection(self,page_number):
        """Update the highlight of the selected thumbnail."""
        # print("Updating thumbnail selection...",self.thumbnails)  # Debug log
        print("page number of thumbnail-------------------------------------------------",page_number)
        for label in thumb_color:
            label.configure(text=f"Page {thumb_color.index(label) + 1}",text_color="black")
            if hasattr(label, "original_image"):
                label.configure(image=label.original_image)
        # Update selected thumbnail
        selected_label = thumb_color[page_number]
        selected_label.configure(text="Selected Page",text_color="red")
        self.inner_thumbnail_frame.update_idletasks()
    # to render the selected page on the canvas
    def select_page(self, page_number):
        """Handle thumbnail click event to switch pages."""
        if 0 <= page_number < len(self.pdf_document):
            self.current_page = page_number
            self.render_page(self.current_page)
            self.update_page_display() # Update page number display
            self.update_thumbnail_selection(page_number) # Highlight selected thumbnail

    # to render the page on the duplicate canvas
    def create_duplicate_window(self, fileurl):
        """Creates a duplicate window to display a PDF independently."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if not fileurl:
            messagebox.showerror("Error", "No PDF is currently loaded to duplicate.")
            return

        duplicate_root = ctk.CTkToplevel(self.root) 
        duplicate_window = DuplicateStickyNotesPDFApp(duplicate_root, fileurl)
        self.duplicate_windows.append(duplicate_root) # Keep track of duplicate windows

        def on_close():
            self.duplicate_windows.remove(duplicate_root)
            duplicate_root.destroy()

        duplicate_root.protocol("WM_DELETE_WINDOW", on_close)
    # close only when all the duplicate window are closed
    def close_main_window(self):
        """Closes the main window only if there are no duplicate windows open."""
        if self.duplicate_windows:
            messagebox.showerror("Warning", "Please close all duplicate windows before exiting the main window.")
        else:
            self.root.destroy()
    def lock_function(self):
        if self.lock_screen == "no":
            self.lock_screen = "yes"
        else:
            self.lock_screen = "no"

    # increase the page size by .2 ever time.
    def zoom_in(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.zoom_factor += 0.2
        self.render_page(self.current_page)
    # decrease the page size by .2 ever time.    
    def zoom_out(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.zoom_factor > 0.4:
            self.zoom_factor -= 0.2
            self.render_page(self.current_page)
    # to render the page in perfect fit in width or height to see all the content
    def best_fit(self):
        """Adjust the zoom level to fit the entire PDF page within the canvas."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()

        page = self.pdf_document.load_page(self.current_page)
        page_width, page_height = page.rect.width, page.rect.height

        width_scale = canvas_width / page_width
        height_scale = canvas_height / page_height
        self.zoom_factor = min(width_scale, height_scale)

        self.render_page(self.current_page)
    # to show the page number entered in the entry box
    def go_to_page(self, event=None):
        try:
            page_number = int(self.page_entry.get()) - 1  # Convert to zero-based index
            if 0 <= page_number < len(self.pdf_document):
                self.current_page = page_number
                self.render_page(self.current_page)
                self.update_thumbnail_selection(self.current_page)
            else:
                messagebox.showerror("Error", "Invalid page number.")
        except ValueError:
            pass

    # to remove all the changes by reloading the url again
    def refresh(self):
        """
        Prompts the user to save the file and reloads the PDF if confirmed.
        If the user declines, nothing happens.
        """
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if "_with_annotations" in self.pdf_path:
            response = messagebox.askyesnocancel("Confirm", "Do you want to save changes before you go back to the old file ?")
            if "with_annotations_redact" in self.pdf_path:
                self.pdf_path = self.pdf_path.replace("_with_annotations_redact", "")
            elif "with_annotations" in self.pdf_path:
                self.pdf_path = self.pdf_path.replace("_with_annotations", "")

            print("self.pdf_path------------------------",self.pdf_path)
            if response:
                self.save_pdf()
                self.load_pdf(self.pdf_path)
            if response is None:
                return
            else:
                self.load_pdf(self.pdf_path)
        else:
            response = messagebox.askyesnocancel("Confirm", "Do you want to save the file before refreshing it?")
            if response is None:
                return
            elif response:
                try:
                    if "with_annotations_redact" in self.pdf_path:
                        self.pdf_path = self.pdf_path.replace("_with_annotations_redact", "")
                    elif "with_annotations" in self.pdf_path:
                        self.pdf_path = self.pdf_path.replace("_with_annotations", "")
                    self.save_pdf()
                    self.load_pdf(self.pdf_path)
                except Exception as e:
                    messagebox.showerror("Error", f"An error occurred during refresh: {e}")
            else:
                # User clicked 'No', just refresh without saving
                self.load_pdf(self.pdf_path)

    # if a file related to the url is saved after change to show when clicked if it 
    # has redacted it shows redacted as pirority even if annoted file is also saved
    def show_annotated_file(self):
        """Toggle the visibility of annotations on the canvas."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        response = messagebox.askyesno(
            "Confirm",
            "Are you sure you want to view if this page has annotations? Any unsaved changes will be lost."
        )
        if not response:
            return
        for url in [annotatedredact_url, annotated_url]:
            if url:
                try:
                    parsed = urlparse(url)
                    if parsed.scheme in ('http', 'https'):
                        try:
                            response = requests.head(url, allow_redirects=True, timeout=5)
                            if response.status_code == 200 and 'application/pdf' in response.headers.get('Content-Type', ''):
                                self.load_pdf(url)
                                return
                        except requests.RequestException:
                            continue
                    elif os.path.isfile(url) and url.lower().endswith('.pdf'):
                        self.load_pdf(url)
                        return
                except Exception:
                    continue

        messagebox.showinfo("Info", "No Annotation were saved to view.")

    # to show the width in perfect width to see all the content as per window width
    def best_width(self):
        """Adjust the zoom level to fit the entire PDF page to the canvas width."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        canvas_width = self.canvas.winfo_width()
        page = self.pdf_document.load_page(self.current_page)
        page_width = page.rect.width

        self.zoom_factor = canvas_width / page_width
        self.render_page(self.current_page)

    # to show the height in perfect height to see all the content as per window height
    def best_height(self):
        """Adjust the zoom level to fit the entire PDF page to the canvas height."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        canvas_height = self.canvas.winfo_height()
        page = self.pdf_document.load_page(self.current_page)
        page_height = page.rect.height

        self.zoom_factor = canvas_height / page_height
        self.render_page(self.current_page)

    # to show all the changes done on the pdf by render the pdf after each change.
    def render_page(self, page_number):
        """Render a PDF page to the canvas with the current zoom factor."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        # Load and render the PDF page
        
        global pageinfo
        pageinfo = page_number
        page = self.pdf_document.load_page(page_number)
        print("page_number - ",page_number)
        matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
        pix = page.get_pixmap(matrix=matrix)
        img = Image.open(io.BytesIO(pix.tobytes("png")))
        # Apply inversion if needed
        if self.is_inverted:
            img = ImageOps.invert(img.convert("RGB"))
        # Convert to a format suitable for display
        img_tk = ImageTk.PhotoImage(img)
        # Clear and redraw the canvas
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
        self.canvas.img_tk = img_tk  # Keep a reference to prevent garbage collection
        # Update scrollable region
        self.page_width, self.page_height = pix.width, pix.height
        self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
        # Redraw sticky notes    
        self.redraw_sticky_notes()
        self.redraw_text_annotations()
        self.redraw_text_with_background()
        self.redraw_polygons()
        self.redraw_annotations()
        self.redraw_freehand_drawings()
        self.canvas.config(scrollregion=self.canvas.bbox("all"))
        print("self.duplicate_windows list -",self.duplicate_windows)

        #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation  # Get current page rotation
    #     for mode, points, polygon_id in self.page_drawings[self.current_page]:
    #         if len(points) % 2 != 0:
    #             continue  # Skip malformed polygons
    #         scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in zip(points[::2], points[1::2])]
    #         page_width = page.rect.width * self.zoom_factor
    #         page_height = page.rect.height * self.zoom_factor
    #         rotated_points = []
    #         for x, y in scaled_points:
    #             if rotation_angle == 90:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = page_height+(180*self.zoom_factor) - y, x
    #                 else:
    #                     rotated_x, rotated_y = page_height+(1000*self.zoom_factor) - y, x
    #             elif rotation_angle == 180:
    #                 rotated_x = page_width - x
    #                 rotated_y = page_height - y
    #             elif rotation_angle == 270:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = y, page_width-(180*self.zoom_factor)  - x
    #                 else:
    #                     rotated_x, rotated_y = y, page_width-(1000*self.zoom_factor)  - x
    #             else:  # 0 degrees
    #                 rotated_x = x
    #                 rotated_y = y
    #             rotated_points.extend([rotated_x, rotated_y])

    def redraw_polygons(self):
        """Redraw all polygons, adjusting for zoom properly."""
        if not self.pdf_document or self.current_page is None:
            return
        
        self.canvas.delete("polygon")
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation  # Get current page rotation
        rotated_points = []
        if self.current_page not in self.page_drawings:
            return

        for mode, points, polygon_id in self.page_drawings[self.current_page]:
            scaled_points = [coord * self.zoom_factor for coord in points]

            polygon_id = self.canvas.create_polygon(
                scaled_points,
                fill="blue" if mode == "filled" else "",
                outline="black" if mode == "filled" else "red",
                tags=("polygon",)
            )


    # def redraw_polygons(self):
    #     if not self.pdf_document or self.current_page is None:
    #         return

    #     self.canvas.delete("polygon")
    #     if self.current_page not in self.page_drawings:
    #         return

    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = self.page_rotation  # Ensure we're using the current rotation

    #     for mode, points, polygon_id in self.page_drawings[self.current_page]:
    #         if len(points) % 2 != 0:
    #             continue

    #         # Convert stored points from original PDF coordinates to current zoom level
    #         scaled_points = [(px * self.zoom_factor, py * self.zoom_factor)
    #                         for px, py in zip(points[::2], points[1::2])]

    #         page_width = page.rect.width * self.zoom_factor
    #         page_height = page.rect.height * self.zoom_factor

    #         rotated_points = []
    #         for x, y in scaled_points:
    #             if rotation_angle == 90:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = page_height+(180*self.zoom_factor) - y, x
    #                 else:
    #                     rotated_x, rotated_y = page_height+(1000*self.zoom_factor) - y, x
    #             elif rotation_angle == 180:
    #                 rotated_x = page_width - x
    #                 rotated_y = page_height - y
    #             elif rotation_angle == 270:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = y, page_width-(180*self.zoom_factor)  - x
    #                 else:
    #                     rotated_x, rotated_y = y, page_width-(1000*self.zoom_factor)  - x
    #             else:  # 0 degrees
    #                 rotated_x = x
    #                 rotated_y = y
    #             rotated_points.extend([rotated_x, rotated_y])

    #         if mode == "filled":
    #             self.canvas.create_polygon(rotated_points, fill="blue", outline="black",
    #                                     tags=("polygon", f"poly_{polygon_id}"))
    #         elif mode == "hollow":
    #             self.canvas.create_polygon(rotated_points, fill="", outline="red",
    #                                     tags=("polygon", f"poly_{polygon_id}"))

    # redrwaing polygon on the canvas after each function
    # def redraw_polygons(self):
    #     """Redraw all polygons on the canvas, ensuring they persist after other functions are used."""
    #     if not self.pdf_document or self.current_page is None:
    #         return  # No PDF loaded or invalid page
    #     self.canvas.delete("polygon")  # Clear previous polygons before redrawing
    #     if self.current_page not in self.page_drawings:
    #         return  # No drawings on this page
    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation  # Get current page rotation
    #     for mode, points, polygon_id in self.page_drawings[self.current_page]:
    #         if len(points) % 2 != 0:
    #             continue  # Skip malformed polygons
    #         scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in zip(points[::2], points[1::2])]
    #         page_width = page.rect.width * self.zoom_factor
    #         page_height = page.rect.height * self.zoom_factor
    #         rotated_points = []
    #         for x, y in scaled_points:
    #             if rotation_angle == 90:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = page_height+(180*self.zoom_factor) - y, x
    #                 else:
    #                     rotated_x, rotated_y = page_height+(1000*self.zoom_factor) - y, x
    #             elif rotation_angle == 180:
    #                 rotated_x = page_width - x
    #                 rotated_y = page_height - y
    #             elif rotation_angle == 270:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = y, page_width-(180*self.zoom_factor)  - x
    #                 else:
    #                     rotated_x, rotated_y = y, page_width-(1000*self.zoom_factor)  - x
    #             else:  # 0 degrees
    #                 rotated_x = x
    #                 rotated_y = y
    #             rotated_points.extend([rotated_x, rotated_y])
    #         if mode == "filled":
    #             self.canvas.create_polygon(rotated_points, fill="blue", outline="black", tags=("polygon", f"poly_{polygon_id}"))
    #         elif mode == "hollow":
    #             self.canvas.create_polygon(rotated_points, fill="", outline="red", tags=("polygon", f"poly_{polygon_id}"))

    # mouse scroll event for vertical scrolling
    def on_mouse_scroll(self, event):
        """Handles vertical scrolling."""
        if self.page_height > self.canvas.winfo_height():  # Scroll only if page is taller
            self.canvas.yview_scroll(-1 * (event.delta // 120), "units")
    # mouse scroll event for horizontal scrolling
    def on_shift_mouse_scroll(self, event):
        """Handles horizontal scrolling when Shift is held."""
        if self.page_width > self.canvas.winfo_width():  # Scroll only if page is wider
            self.canvas.xview_scroll(-1 * (event.delta // 120), "units")

    # def on_thumbnail_scroll(self, event):
    #     """Handle vertical scrolling in the thumbnail panel using the mouse wheel."""
    #     self.thumbnail_canvas.yview_scroll(-1 * (event.delta // 120), "units")

    def enable_sticky_note_mode(self):
        """Activate sticky note mode."""
        self.sticky_note_mode = True
        self.highlight_mode = False

        # Unbind previous actions and bind the sticky note click action
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.canvas.bind("<Button-1>", self.on_canvas_click)

    def redraw_sticky_notes(self):
        """Redraw sticky notes after rendering the page and adjust for rotation."""
        self.canvas.delete("sticky_note")
        if not self.pdf_document:
            return
        
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation  # Get current page rotation

        for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor

                # Get page dimensions at the current zoom level
                page_width = page.rect.width * self.zoom_factor
                page_height = page.rect.height * self.zoom_factor

                # Adjust coordinates based on rotation
                if rotation_angle == 90:
                    if is_small_page == "yes":
                        rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
                    else:
                        rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
                elif rotation_angle == 180:
                    rotated_x = page_width - x_position
                    rotated_y = page_height - y_position
                elif rotation_angle == 270:
                    if is_small_page == "yes":
                        rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
                    else:
                        rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position           
                else:  # 0 degrees
                    rotated_x = x_position
                    rotated_y = y_position
                self.canvas.create_image(
                    rotated_x, rotated_y,
                    image=self.icons['thumb_pin'],
                    anchor="center",
                    tags="sticky_note"
                )
        self.annotation_is_available = True
  
    def on_canvas_click(self, event):
        """Add a sticky note at the clicked position on the canvas."""
        if not self.pdf_document or not self.sticky_note_mode:
            return

        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)

        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return

        note_text = self.ask_for_note_text(x, y,"Add Sticky Note")
        if not note_text:
            return

        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor

        self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
        # changes_data = ("sticky_note", self.current_page, x_scaled, y_scaled, note_text)
        # changes_data = str(changes_data)
        # sql_check = """
        #     SELECT COUNT(*) FROM pdf_editor_details 
        #     WHERE folder_path = %s AND filename = %s AND changes_data = %s
        # """
        # mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
        # result = mycursor.fetchone()
        # if result[0] == 0:
        #     sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
        #     val = (beforeexe,folderpath,changes_data,0)
        #     mycursor.execute(sql, val)
        #     mydb.commit()
        self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
        print("Sticky note added at:", x_scaled, y_scaled)
        print("Sticky notes:----",self.change_history)
        # Safely retrieve the icon for sticky notes
        self.annotation_is_available = True
        sticky_icon = self.icons.get("thumb_pin")
        if sticky_icon:
            self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
        else:
            print("Warning: 'sticky_note' icon not found.")  # Refresh to apply the changes

    def ask_for_note_text(self, x, y,title):
        """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
        dialog = ctk.CTkToplevel(self.root)
        dialog.title(title)
        dialog.geometry("400x250")
        dialog.resizable(False, False)

        label = ctk.CTkLabel(
            dialog, text="Enter your note:", font=ctk.CTkFont(size=14, weight="bold")
        )
        label.pack(pady=(15, 10))

        text_box = ctk.CTkTextbox(dialog, wrap="word", height=100, width=360)
        text_box.pack(padx=15, pady=5, fill="x")
        text_box.focus_set()

        note_text_var = ctk.StringVar()

        # Button functionality
        def on_ok_click():
            note_text = text_box.get("1.0", "end").strip()
            if note_text:
                note_text_var.set(note_text)
                dialog.destroy()
            else:
                messagebox.showerror("Empty Note", "You must enter some text to save the sticky note.")

        # Create buttons
        buttons_frame = ctk.CTkFrame(dialog)
        buttons_frame.pack(side="bottom", pady=15)

        ok_button = ctk.CTkButton(
            buttons_frame, text="Apply", command=on_ok_click, fg_color="#00498f", text_color="white"
        )
        ok_button.pack(side="left", padx=10)

        cancel_button = ctk.CTkButton(
            buttons_frame, text="Cancel", command=dialog.destroy, fg_color="#6c757d", text_color="white"
        )
        cancel_button.pack(side="left", padx=10)

        dialog.grab_set()
        dialog.wait_window()

        self.sticky_note_mode = False
        self.add_text_mode = False
        self.add_text_bg_mode = False
        return note_text_var.get() or None


    # def undo_change(self):
    #     """Undo the last change and delete it from the database."""

    #     # Fetch the last action
    #     sql = """SELECT changes_data FROM pdf_editor_details
    #             WHERE filename = %s ORDER BY time_stamp DESC LIMIT 1"""
    #     mycursor.execute(sql, (beforeexe,))  # Ensure it's a tuple
    #     last_action = mycursor.fetchone()

    #     if not last_action:
    #         return

    #     last_action = eval(last_action[0])  # Convert string back to tuple
    #     action_type = last_action[0]

    #     if action_type == "highlight":
    #         _, page, annot_id = last_action
    #         page_obj = self.pdf_document[page]
    #         annot = page_obj.first_annot
    #         while annot:
    #             if annot.info.get('id') == annot_id:
    #                 page_obj.delete_annot(annot)
    #                 self.render_page(self.current_page)
    #                 break
    #             annot = annot.next
        
    #     elif action_type == "freehand":
    #         _, page, line_id, _ = last_action
    #         # Remove from the canvas
    #         self.canvas.delete(line_id)
    #         # Remove from history
    #         self.change_history = [entry for entry in self.change_history if entry[2] != line_id]
    #         # Redraw remaining freehand drawings to refresh the canvas
    #         self.redraw_freehand_drawings()
    #         self.render_page(self.current_page)

    #     elif action_type in ("add_text", "add_text_bg"):
    #         _, page, x_scaled, y_scaled, text = last_action
    #         annotation_dict = self.text_annotations if action_type == "add_text" else self.text_annotations_bg
    #         if (page, x_scaled, y_scaled) in annotation_dict:
    #             del annotation_dict[(page, x_scaled, y_scaled)]
    #             page_obj = self.pdf_document[page]
    #             annot = page_obj.first_annot
    #             while annot:
    #                 if annot.info and annot.info.get("contents") == text:
    #                     page_obj.delete_annot(annot)
    #                     break
    #                 annot = annot.next
    #             self.render_page(self.current_page)

    #     elif action_type == "sticky_note":
    #         _, page, x_scaled, y_scaled, _ = last_action
    #         if (page, x_scaled, y_scaled) in self.sticky_notes:
    #             del self.sticky_notes[(page, x_scaled, y_scaled)]
    #             self.render_page(self.current_page)

    #     elif action_type in ("line", "arrow"):
    #         """Undo the last line or arrow annotation."""
    #         _, page, x1, y1, x2, y2, annot_id = last_action
    #         self.canvas.delete(annot_id)  # Delete from the canvas
    #         self.annotations = [annot for annot in self.annotations if annot[6] != annot_id]
    #         self.redraw_annotations()
    #     else:
    #         print(f"Unknown action type: {action_type}")
        
    #     # Delete the undone action from the database
    #     sql_delete = """DELETE FROM pdf_editor_details 
    #                     WHERE filename = %s AND changes_data = %s 
    #                     ORDER BY time_stamp DESC LIMIT 1"""
    #     mycursor.execute(sql_delete, (beforeexe, str(last_action)))  # Ensure tuple format
    #     mydb.commit()

    #     print(f"Action '{action_type}' undone and removed from the database.")

    def undo_change(self):
        print("Undoing the last change...",self.change_history)
        if not self.change_history:
            return
        data_check_poly = self.change_history[-1]
        if data_check_poly[0] == "polygon":
            print("ssfbbfnfnngnggnc ho ho ho")
            if self.polygon_active != "yes":
                messagebox.showinfo("Info", "Please activate the polygon tool to undo the polygon.")
                return

        last_action = self.change_history.pop()
        action_type = last_action[0]
        
        if action_type == "highlight":
            _, page, annot_id = last_action
            page_obj = self.pdf_document[page]
            annot = page_obj.first_annot
            while annot:
                if annot.info.get('id') == annot_id:
                    page_obj.delete_annot(annot)
                    self.render_page(self.current_page)
                    break
                annot = annot.next
        
        elif action_type == "freehand":
            _, page, line_id, _ = last_action
            # Remove from the canvas
            self.canvas.delete(line_id)
            # Remove from history
            self.change_history = [entry for entry in self.change_history if entry[2] != line_id]
            # Redraw remaining freehand drawings to refresh the canvas
            self.redraw_freehand_drawings()
            self.render_page(self.current_page)

        elif action_type in ("add_text", "add_text_bg"):
            _, page, x_scaled, y_scaled, text = last_action
            annotation_dict = self.text_annotations if action_type == "add_text" else self.text_annotations_bg
            if (page, x_scaled, y_scaled) in annotation_dict:
                del annotation_dict[(page, x_scaled, y_scaled)]
                page_obj = self.pdf_document[page]
                annot = page_obj.first_annot
                while annot:
                    if annot.info and annot.info.get("contents") == text:
                        page_obj.delete_annot(annot)
                        break
                    annot = annot.next
                self.render_page(self.current_page)

        # elif action_type == "polygon":
        #     _, page, prev_state, polygon_id = last_action
        #     if self.polygon_active != "yes":
        #         messagebox.showinfo("Info", "Please activate the polygon tool to undo the polygon.")
        #         return
        #     if page in self.page_drawings:
        #         for i, (mode, points, pid) in enumerate(self.page_drawings[page]):
        #             if pid == polygon_id:
        #                 if prev_state is None:
        #                     # Undo polygon creation (remove it)
        #                     self.canvas.delete(polygon_id)
        #                     del self.page_drawings[page][i]
        #                 else:
        #                     # Restore previous state (undo move/reshape)
        #                     self.page_drawings[page][i] = (mode, prev_state, polygon_id)
        #                     self.canvas.coords(polygon_id, prev_state)
        #                 break

        elif action_type == "sticky_note":
            _, page, x_scaled, y_scaled, _ = last_action
            if (page, x_scaled, y_scaled) in self.sticky_notes:
                del self.sticky_notes[(page, x_scaled, y_scaled)]
                self.render_page(self.current_page)

        elif action_type in ("line", "arrow"):
            """Undo the last line or arrow annotation."""
            _, page, x1, y1, x2, y2, annot_id = last_action
            self.canvas.delete(annot_id)  # Delete from the canvas
            self.annotations = [annot for annot in self.annotations if annot[6] != annot_id]
            self.redraw_annotations()

        elif action_type == "polygon":
            action_type, page_num, previous_state, item_id = last_action
            # Remove the polygon from page_drawings completely
            self.page_drawings[page_num] = [d for d in self.page_drawings[page_num] if d[2] != item_id]
            self.canvas.delete(item_id)  # Remove from the canvas
            # Ensure it doesn't get re-embedded
            if page_num in self.embedded_polygons:
                self.embedded_polygons[page_num] = [d for d in self.embedded_polygons[page_num] if d[2] != item_id]
            self.redraw_polygons()
        else:
            print(f"Unknown action type: {action_type}")



    def enable_highlight_mode(self):
        """ Activate highlight mode """
        self.deactivate_tools()
        self.highlight_mode = True
        self.is_drawing_hollow_rect = False
        self.is_drawing_filled_rect = False
        self.canvas.bind("<Button-1>", self.start_highlight_rectangle)
        self.canvas.bind("<B1-Motion>", self.draw_highlight_rectangle)
        self.canvas.bind("<ButtonRelease-1>", self.finalize_highlight)

    def start_highlight_rectangle(self, event):
        """Start a rectangle selection for highlighting"""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        
        # Delete any existing highlight preview
        if self.rectangle_id:
            self.canvas.delete(self.rectangle_id)
        
        # Draw the initial rectangle immediately
        self.rectangle_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
            outline="yellow", width=2)

    def draw_highlight_rectangle(self, event):
        """Draw the rectangle dynamically as the mouse is dragged."""
        if self.rectangle_id is None:
            return  # Prevents calling coords on None
        
        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
        # Update rectangle coordinates safely
        self.canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)


    def finalize_highlight(self, event):
        """Finalize the highlight and save it to the PDF."""
        if self.start_x is None or self.start_y is None:
            return
        end_x = self.canvas.canvasx(event.x) / self.zoom_factor
        end_y = self.canvas.canvasy(event.y) / self.zoom_factor
        start_x = self.start_x / self.zoom_factor
        start_y = self.start_y / self.zoom_factor
        rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
        page = self.pdf_document[self.current_page]
        rotation = page.rotation
        page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor
        if rotation == 90:
            rect = fitz.Rect(
                rect.y0,
                page_width - rect.x1,
                rect.y1,
                page_width - rect.x0)
        elif rotation == 180:
            rect = fitz.Rect(
                page_width - rect.x1,
                page_height - rect.y1,
                page_width - rect.x0,
                page_height - rect.y0)
        elif rotation == 270:
            rect = fitz.Rect(
                page_height - rect.y1,
                rect.x0,
                page_height - rect.y0,
                rect.x1)
        try:
            highlight = page.add_highlight_annot(rect)
            highlight.update()
            highlight.set_border(width=0, dashes=(0, 0))
            annot_id = highlight.info.get('id')
            # changes_data = ("highlight", self.current_page, annot_id)
            # changes_data = str(changes_data)
            # if annot_id:
            #     sql_check = """
            #         SELECT COUNT(*) FROM pdf_editor_details 
            #         WHERE folder_path = %s AND filename = %s AND changes_data = %s
            #     """
            #     mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
            #     result = mycursor.fetchone()
            #     if result[0] == 0:
            #         print(f"Added highlight with ID: {annot_id}")
            #         print("beforeexe----",beforeexe)
            #         sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
            #         val = (beforeexe,folderpath,changes_data,0)
            #         mycursor.execute(sql, val)
            #         mydb.commit()
            if annot_id:
                self.change_history.append(("highlight", self.current_page, annot_id))
                print("highlight added",self.change_history)
                self.annotation_is_available = True
        except Exception as e:
            messagebox.showerror("Error", f"Failed to add highlight: {e}")
            return    
        self.render_page(self.current_page)
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    def on_mouse_hover(self, event):
        """Change cursor when hovering over a polygon or sticky note."""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        tooltip_shown = False
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        # Check for polygons and freehand drawings
        for drawing in self.page_drawings.get(self.current_page, []):
            if isinstance(drawing, tuple):
                if len(drawing) == 3:  # Polygon (id, points, color)
                    _, points, _ = drawing
                    if self.is_point_inside_polygon(x, y, points):
                        self.canvas.config(cursor="hand2")
                        return

        # Check for sticky notes
        for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                page_width = page.rect.width * self.zoom_factor
                page_height = page.rect.height * self.zoom_factor

                if rotation_angle == 90:
                    rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
                elif rotation_angle == 180:
                    rotated_x = page_width - x_position
                    rotated_y = page_height - y_position
                elif rotation_angle == 270:
                    rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
                else:  # 0 degrees
                    rotated_x = x_position
                    rotated_y = y_position

                # Check if mouse is near the adjusted sticky note position
                if abs(x - rotated_x) < 20 and abs(y - rotated_y) < 20:  # Adjust hover sensitivity
                    if not tooltip_shown:
                        self.show_tooltip(event.x_root, event.y_root, text)
                        tooltip_shown = True
                    break

        if not tooltip_shown:
            if self.active_tooltip:
                self.active_tooltip.destroy()
                self.active_tooltip = None
            self.canvas.config(cursor="")


    def show_tooltip(self, x, y, text):
        """Display the sticky note text as a tooltip."""
        if getattr(self, "active_tooltip", None):
            self.active_tooltip.destroy()
        wraptext = textwrap.fill(text, width=50)  # Ensuring the line ends at 50 characters
        today = date.today().strftime("%m-%d-%Y")
        wrapped_text = f"{today}\n\n{wraptext}"
        tooltip = ctk.CTkToplevel(self.root)
        tooltip.overrideredirect(True)
        tooltip.geometry(f"+{int(x) + 10}+{int(y) + 10}")  # Ensure integer coordinates
        label = ctk.CTkLabel(
            tooltip, text=wrapped_text, bg_color="light yellow", text_color="black", padx=10, pady=5
        )
        label.pack()
        if getattr(self, "active_tooltip", None):
            self.active_tooltip.destroy()
        self.active_tooltip = tooltip

    def toggle_sticky_note_mode(self):
        """Toggle sticky note mode"""
        if self.sticky_note_mode:
            self.sticky_note_mode = False
            self.canvas.unbind("<Button-1>")
        else:
            self.enable_sticky_note_mode()

# -----------------------------------------------------------------------------------------------------------

    def save_pdf(self, file_path=None):
        """Save the PDF with embedded sticky notes and upload directly to the server."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF document to save.")
            return
        if self.annotation_is_available == False:
            if self.redact_is_available == False:
                messagebox.showinfo("Info", "No Changes made to the document to save.")
                return
        redact_buffer = []
        try:        
            if len(self.redactions) > 0:
                redact_file_name = edit_file_name.replace(".pdf", "_redact.pdf")
                redacted_pdf = fitz.open()

                for page_num in range(len(self.pdf_document)):
                    page = self.pdf_document[page_num]
                    redacted_pdf.insert_pdf(self.pdf_document, from_page=page_num, to_page=page_num)
                
                today = date.today().strftime("%m-%d-%Y")
                max_line_length = 50
                
                for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
                    page = redacted_pdf[page_num]
                    marker_size = 12
                    text_size = 13
                    marker_color = (1, 0, 0)  # Red
                    text_offset = 15
                    padding = 10

                    # Draw marker
                    page.draw_circle(
                        center=(x_scaled, y_scaled),
                        radius=marker_size / 2,
                        color=marker_color,
                        fill=marker_color
                    )

                    # Wrap sticky note text
                    lines = self.wrap_text(f"{today}\n\n{text}", max_line_length)
                    max_text_width = max(len(line) for line in lines) * text_size * 0.6
                    max_text_height = len(lines) * text_size * 1.5
                    background_width = max_text_width + padding * 2
                    background_height = max_text_height + padding * 2

                    # Draw sticky note background
                    page.draw_rect(
                        rect=(
                            x_scaled - padding,
                            y_scaled + text_offset - padding,
                            x_scaled + background_width,
                            y_scaled + text_offset + background_height
                        ),
                        color=(1, 1, 0),  # Yellow
                        overlay=True,
                        fill_opacity=0.9,
                        fill=(1, 1, 0)
                    )

                    # Insert wrapped text
                    for i, line in enumerate(lines):
                        page.insert_text(
                            point=(x_scaled, y_scaled + text_offset + (i * text_size * 1.5)),
                            text=line,
                            fontsize=text_size,
                            color=(0, 0, 0)
                        )
                if "redact" not in edit_file_name:
                    redact_file_name = edit_file_name.replace(".pdf", "_redact.pdf")
                else:
                    redact_file_name = edit_file_name
                for page in redacted_pdf:
                    page.apply_redactions()  # Apply redactions
                self.deactivate_redact_tools()
                redact_buffer = io.BytesIO()
                redacted_pdf.save(redact_buffer, garbage=4, deflate=True, deflate_images=True, clean=True)
                redact_buffer.seek(0)
                files = {
                    'folder_path': (None, folderpath),
                    'redact': (redact_file_name, redact_buffer, 'application/pdf')
                }
                print("Redacted file saved and ready for upload")
                response = requests.post(self.server_url, files=files)

            if len(self.redactions) == 0:              
                temp_pdf = fitz.open()
                for page_num in range(len(self.pdf_document)):
                    page = self.pdf_document[page_num]
                    temp_pdf.insert_pdf(self.pdf_document, from_page=page_num, to_page=page_num)
                
                today = date.today().strftime("%m-%d-%Y")
                max_line_length = 50
                
                for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
                    page = temp_pdf[page_num]
                    marker_size = 12
                    text_size = 13
                    marker_color = (1, 0, 0)  # Red
                    text_offset = 15
                    padding = 10

                    # Draw marker
                    page.draw_circle(
                        center=(x_scaled, y_scaled),
                        radius=marker_size / 2,
                        color=marker_color,
                        fill=marker_color
                    )

                    # Wrap sticky note text
                    lines = self.wrap_text(f"{today}\n\n{text}", max_line_length)
                    max_text_width = max(len(line) for line in lines) * text_size * 0.6
                    max_text_height = len(lines) * text_size * 1.5
                    background_width = max_text_width + padding * 2
                    background_height = max_text_height + padding * 2

                    # Draw sticky note background
                    page.draw_rect(
                        rect=(
                            x_scaled - padding,
                            y_scaled + text_offset - padding,
                            x_scaled + background_width,
                            y_scaled + text_offset + background_height
                        ),
                        color=(1, 1, 0),  # Yellow
                        overlay=True,
                        fill_opacity=0.9,
                        fill=(1, 1, 0)
                    )

                    # Insert wrapped text
                    for i, line in enumerate(lines):
                        page.insert_text(
                            point=(x_scaled, y_scaled + text_offset + (i * text_size * 1.5)),
                            text=line,
                            fontsize=text_size,
                            color=(0, 0, 0)
                        )  
                pdf_buffer = io.BytesIO()
                temp_pdf.save(pdf_buffer, garbage=4, deflate=True, deflate_images=True, clean=True)
                pdf_buffer.seek(0)
                # Only upload the non-redacted version
                files = {
                    'file': (edit_file_name, pdf_buffer, 'application/pdf'),
                    'folder_path': (None, folderpath)
                }
                response = requests.post(self.server_url, files=files)
            if response.status_code in [200, 201]:
                messagebox.showinfo("Success", "File successfully uploaded to server.")
            else:
                messagebox.showerror("Error", f"Upload failed. Status: {response.status_code}, {response.text}")

        except Exception as e:
            messagebox.showerror("Error", f"An error occurred while saving the PDF: {e}")

        finally:
            temp_pdf.close()
            pdf_buffer.close()



    def wrap_text(self, text, max_line_length):
        """Wrap the text into lines with a maximum number of characters per line."""
        words = text.split(" ")
        lines = []
        current_line = ""
        for word in words:
            if len(current_line) + len(word) + 1 <= max_line_length:
                current_line += (word + " ")
            else:
                lines.append(current_line.strip())
                current_line = word + " "
        if current_line:
            lines.append(current_line.strip())
        return lines
    
    def update_page_display(self):
        if self.pdf_document:
            total_pages = len(self.pdf_document)
            self.page_entry.delete(0, ctk.END)
            self.page_entry.insert(0, str(self.current_page + 1))  # One-based index
            self.page_total_label.configure(text=f"/ {total_pages}")
    
    def prev_page(self, event=None):
        """Go to the previous page in the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.current_page > 0:
            self.current_page -= 1
            self.render_page(self.current_page)
            self.update_thumbnail_selection(self.current_page)
            self.update_page_display()

    def next_page(self, event=None):
        """Go to the next page in the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.current_page < len(self.pdf_document) - 1:
            self.current_page += 1
            self.render_page(self.current_page)
            self.update_thumbnail_selection(self.current_page)
            self.update_page_display()


    def rotate_90clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 90) % 360)
        self.render_page(self.current_page)

    def rotate_180clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 180) % 360)
        self.render_page(self.current_page)

    def rotate_270clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 270) % 360)
        self.render_page(self.current_page)

    def toggle_invert_colors(self):
        """Toggle color inversion for the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.is_inverted = not self.is_inverted
        self.render_page(self.current_page)
        self.redraw_sticky_notes()


    def zoom_in_area(self, event):
        """Zoom into a specific area of the canvas based on mouse click."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        # Get the canvas click position adjusted for scrolling
        canvas_x = self.canvas.canvasx(event.x) / self.zoom_factor
        canvas_y = self.canvas.canvasy(event.y) / self.zoom_factor

        # Define the zoom area dimensions
        zoom_area_size = 150
        left = max(0, canvas_x - zoom_area_size // 2)
        top = max(0, canvas_y - zoom_area_size // 2)
        right = min(self.page_width, canvas_x + zoom_area_size // 1)
        bottom = min(self.page_height, canvas_y + zoom_area_size // 2)

        # Calculate the zoom factors for the selected area
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        zoom_width_factor = canvas_width / (right - left)
        zoom_height_factor = canvas_height / (bottom - top)

        # Update the zoom factor to fit the selected area
        self.zoom_factor = min(zoom_width_factor, zoom_height_factor)

        # Render the selected zoomed-in area
        page = self.pdf_document.load_page(self.current_page)
        matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)

        # Translate the viewport to the selected area
        translation_matrix = fitz.Matrix(1, 0, 0, 1, -left, -top)
        combined_matrix = matrix * translation_matrix
        pix = page.get_pixmap(matrix=combined_matrix, clip=(left, top, right, bottom))

        # Convert the pixmap to an image
        img = Image.open(io.BytesIO(pix.tobytes("png")))
        if self.is_inverted:
            img = ImageOps.invert(img.convert("RGB"))
        img_tk = ImageTk.PhotoImage(img)

        # Update the canvas with the new zoomed-in area
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
        self.canvas.img_tk = img_tk

        # Update canvas scroll region
        self.page_width, self.page_height = pix.width, pix.height
        self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
        # Disable zoom-in area mode after use
        self.toggle_zoom_in_area_mode()

    def toggle_zoom_in_area_mode(self):
        """Toggle the mode to allow zooming into a specific area."""
        if hasattr(self, "zoom_in_area_enabled") and self.zoom_in_area_enabled:
            self.canvas.unbind("<Button-1>")
            self.zoom_in_area_enabled = False
        else:
            self.canvas.bind("<Button-1>", self.zoom_in_area)
            self.zoom_in_area_enabled = True

    def toggle_drawing(self):
        """Toggle the freehand drawing mode without embedding strokes into the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.is_drawing = not self.is_drawing  # Toggle drawing mode
        if self.is_drawing:
            self.canvas.bind("<Button-1>", self.start_freehand_drawing)
            self.canvas.bind("<B1-Motion>", self.draw_freehand_line)
            self.canvas.bind("<ButtonRelease-1>", self.finish_freehand_drawing)
        else:
            self.canvas.unbind("<Button-1>")
            self.canvas.unbind("<B1-Motion>")
            self.canvas.unbind("<ButtonRelease-1>")

    def start_freehand_drawing(self, event):
        """Start recording a freehand drawing stroke with unscaled coordinates."""
        self.freehand_stroke = [(event.x / self.zoom_factor, event.y / self.zoom_factor)]
        self.current_line = self.canvas.create_line(
            self.freehand_stroke[0][0] * self.zoom_factor,
            self.freehand_stroke[0][1] * self.zoom_factor,
            self.freehand_stroke[0][0] * self.zoom_factor,
            self.freehand_stroke[0][1] * self.zoom_factor,
            fill="black", width=2
        )

    def draw_freehand_line(self, event):
        """Draw a freehand stroke in real-time with unscaled coordinates."""
        if not hasattr(self, "freehand_stroke"):
            return

        x, y = event.x / self.zoom_factor, event.y / self.zoom_factor
        page_width = self.page_width / self.zoom_factor
        page_height = self.page_height / self.zoom_factor

        # Ensure the stroke stays within the page bounds
        x = max(0, min(x, page_width))
        y = max(0, min(y, page_height))

        self.freehand_stroke.append((x, y))
        scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in self.freehand_stroke]
        self.canvas.coords(self.current_line, *sum(scaled_points, ()))

    def finish_freehand_drawing(self, event):
        """Save the drawn freehand stroke for undo functionality without embedding into the PDF."""
        if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
            return
        self.freehand_drawings.append((self.current_page, self.current_line, self.freehand_stroke))
        self.change_history.append(("freehand", self.current_page, self.current_line, self.freehand_stroke))

        self.annotation_is_available = True
        del self.freehand_stroke
        del self.current_line
        self.toggle_drawing()
        self.render_page(self.current_page)  # Re-render to ensure it's drawn correctly
        self.redraw_freehand_drawings()


    # def finish_freehand_drawing(self, event):
    #     """Save the drawn freehand stroke for undo functionality without embedding into the PDF."""
    #     if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
    #         return
        
    #     # Save the stroke in change history
    #     # changes_data = (("freehand", self.current_page, self.current_line, self.freehand_stroke))
    #     # changes_data = str(changes_data)
    #     # sql_check = """
    #     #     SELECT COUNT(*) FROM pdf_editor_details 
    #     #     WHERE folder_path = %s AND filename = %s AND changes_data = %s
    #     # """
    #     # mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
    #     # result = mycursor.fetchone()
    #     # if result[0] == 0:
    #     #     sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
    #     #     val = (beforeexe,folderpath,changes_data,0)
    #     #     mycursor.execute(sql, val)
    #     #     mydb.commit()
    #     self.freehand_drawings.append((self.current_page, self.current_line, self.freehand_stroke))
    #     print("(self.current_page, self.current_line, self.freehand_stroke)-",(self.current_page, self.current_line, self.freehand_stroke))
    #     self.change_history.append(("freehand", self.current_page, self.current_line, self.freehand_stroke))
    #     self.annotation_is_available = True
    #     del self.freehand_stroke
    #     del self.current_line
    #     self.toggle_drawing()
    #     self.render_page(self.current_page)
    #     self.redraw_freehand_drawings()

    def redraw_freehand_drawings(self):
        """Redraw all freehand drawings, applying zoom and rotation transformations."""
        self.canvas.delete("freehand")  # Clear previous drawings

        for i, entry in enumerate(self.change_history):
            if entry[0] == "freehand":
                _, page, line_id, points = entry
                if page != self.current_page:
                    continue
                
                transformed_points = [self.apply_transformations(x, y) for x, y in points]
                scaled_points = [(x * self.zoom_factor, y * self.zoom_factor) for x, y in transformed_points]

                new_line_id = self.canvas.create_line(
                    *sum(scaled_points, ()),
                    fill="black", width=2, tags="freehand"
                )
                self.change_history[i] = ("freehand", page, new_line_id, points)
    def apply_transformations(self, x, y):
        """Apply rotation first, then zoom transformations to a given point."""
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        page_width = self.page_width / self.zoom_factor  # Unscaled width
        page_height = self.page_height / self.zoom_factor  # Unscaled height

        # Apply rotation without zooming
        if rotation_angle == 90:
            if is_small_page == "yes":
                x, y = page_height+(250) - y, x
            elif is_small_page == "maybe":
                x, y = page_height+(750) - y, x
            else:
                x, y = page_height+(1000) - y, x
        elif rotation_angle == 180:
            x, y = page_width - x, page_height - y
        elif rotation_angle == 270:
            if is_small_page == "yes":
                x, y = y, page_width-(250) - x
            elif is_small_page == "maybe":
                x, y = y, page_width-(750) - x
            else:
                x, y = y, page_width-(1000) - x
        return x, y


    def toggle_filled_polygon_mode(self):
        """Toggle filled polygon drawing mode."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        if self.polygon_mode == "filled":
            # Deactivate the mode
            self.filled_polygon_button.configure(text="")
            self.polygon_mode = None
            self.start_point = None
            self.polygon_created = False  # Reset creation flag
            self.polygon_active = "no"
            self.canvas.unbind("<Button-1>")
            # self.embed_polygons_in_pdf()
            self.redraw_polygons()
        else:
            # Deactivate hollow mode if active
            if self.polygon_mode == "hollow":
                self.hollow_polygon_button.configure(text="")

            # Activate filled mode
            self.filled_polygon_button.configure(text="#")
            self.polygon_active = "yes"
            self.polygon_mode = "filled"
            self.start_point = None
            self.polygon_created = False  # Reset creation flag
            self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)


    def toggle_hollow_polygon_mode(self):
        """Toggle hollow polygon drawing mode."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        if self.polygon_mode == "hollow":
            # Deactivate the mode
            self.hollow_polygon_button.configure(text="")
            self.polygon_mode = None
            self.start_point = None
            self.polygon_active = "no"
            self.polygon_created = False  # Reset creation flag
            self.canvas.unbind("<Button-1>")
            self.redraw_polygons()
            # self.embed_polygons_in_pdf()
        else:
            # Deactivate filled mode if active
            if self.polygon_mode == "filled":
                self.filled_polygon_button.configure(text="")

            # Activate hollow mode
            self.hollow_polygon_button.configure(text="#")
            self.polygon_active = "yes"
            self.polygon_mode = "hollow"
            self.start_point = None
            self.polygon_created = False  # Reset creation flag
            self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)


    def is_point_inside_polygon(self, x, y, points):
        num_points = len(points) // 2
        polygon = [(points[i * 2], points[i * 2 + 1]) for i in range(num_points)]
        inside = False

        for i in range(num_points):
            x1, y1 = polygon[i]
            x2, y2 = polygon[(i + 1) % num_points]

            if ((y1 > y) != (y2 > y)) and (x < (x2 - x1) * (y - y1) / (y2 - y1) + x1):
                inside = not inside

        return inside

    def generate_polygon_points(self, x, y, radius, sides):
        """Generate the points of a regular polygon with given sides and radius."""
        points = []
        for i in range(sides):
            angle = 2 * math.pi * i / sides
            px = x + radius * math.cos(angle)
            py = y + radius * math.sin(angle)
            points.append(px)
            points.append(py)
        return points

    # def on_canvas_polygon_click(self, event):
    #     """Handle canvas clicks for creating or modifying polygons."""
    #     if not self.polygon_mode:
    #         return
    #     x, y = self.canvas.canvasx(event.x) / self.zoom_factor, self.canvas.canvasy(event.y) / self.zoom_factor
    #     # x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

    #     if self.current_page not in self.page_drawings:
    #         self.page_drawings[self.current_page] = []

    #     # Check if clicking inside an existing polygon
    #     for idx, drawing in enumerate(self.page_drawings[self.current_page]):
    #         if len(drawing) != 3:
    #             print(f"Skipping invalid entry at index {idx}: {drawing}")
    #             continue
    #         mode, points, polygon_id = drawing

    #         if self.is_point_inside_polygon(x, y, points):
    #             self.canvas.config(cursor="hand2")  # Change cursor when hovering over polygon

    #             # Dynamic selection radius based on zoom level
    #             zoom_adjusted_radius = max(10, 15 * self.zoom_factor)

    #             # Check if dragging a vertex
    #             for i in range(0, len(points), 2):
    #                 vx, vy = points[i], points[i + 1]
    #                 if abs(vx - x) < zoom_adjusted_radius and abs(vy - y) < zoom_adjusted_radius:
    #                     self.dragging_polygon = (idx, i // 2)
    #                     self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
    #                     self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
    #                     self.canvas.config(cursor="fleur")  # Change cursor to grabbing hand when dragging
    #                     return

    #             # Dragging entire polygon
    #             self.dragging_polygon = (idx, None)
    #             self.start_drag_x, self.start_drag_y = x, y
    #             self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
    #             self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
    #             self.canvas.config(cursor="fleur")  # Change cursor to grabbing hand when dragging
    #             return

    #     # Start a new polygon if no existing polygon was selected
    #     if self.start_point is None:
    #         self.start_point = (x, y)
    #         points = self.generate_polygon_points(x / self.zoom_factor, y / self.zoom_factor, self.polygon_size / self.zoom_factor, 5)
    #         # points = self.generate_polygon_points(x, y, self.polygon_size, 5)
    #         polygon_id = self.canvas.create_polygon(
    #             points,
    #             fill="blue" if self.polygon_mode == "filled" else "",
    #             outline="black" if self.polygon_mode == "filled" else "red",
    #             tags=("polygon",)
    #         )
    #         self.page_drawings[self.current_page].append((self.polygon_mode, points, polygon_id))
    #         self.change_history.append(("polygon", self.current_page, None, polygon_id))
    #     else:
    #         self.start_point = None
    #     self.redraw_polygons()

    def on_canvas_polygon_click(self, event):
        """Handle canvas clicks for creating or modifying polygons."""
        if not self.polygon_mode:
            return
        
        # Convert the click position to PDF space
        x = self.canvas.canvasx(event.x) / self.zoom_factor
        y = self.canvas.canvasy(event.y) / self.zoom_factor

        if self.current_page not in self.page_drawings:
            self.page_drawings[self.current_page] = []

        for idx, drawing in enumerate(self.page_drawings[self.current_page]):
            if len(drawing) != 3:
                continue

            mode, points, polygon_id = drawing

            if self.is_point_inside_polygon(x, y, points):
                self.canvas.config(cursor="hand2")

                # Convert the zoom factor correctly for dragging
                zoom_adjusted_radius = max(10, 15 / self.zoom_factor)
                for i in range(0, len(points), 2):
                    vx, vy = points[i], points[i + 1]
                    if abs(vx - x) < zoom_adjusted_radius and abs(vy - y) < zoom_adjusted_radius:
                        self.dragging_polygon = (idx, i // 2)
                        self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
                        self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                        self.canvas.config(cursor="fleur")
                        return

                self.dragging_polygon = (idx, None)
                self.start_drag_x, self.start_drag_y = x, y
                self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
                self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                self.canvas.config(cursor="fleur")
                return

        # If a new polygon needs to be created
        if self.start_point is None:
            self.start_point = (x, y)

            points = self.generate_polygon_points(
                x, y, 
                self.polygon_size / self.zoom_factor, 
                5
            )

            # Scale points back for display on the canvas
            scaled_points = [coord * self.zoom_factor for coord in points]

            polygon_id = self.canvas.create_polygon(
                scaled_points,
                fill="blue" if self.polygon_mode == "filled" else "",
                outline="black" if self.polygon_mode == "filled" else "red",
                tags=("polygon",)
            )

            self.page_drawings[self.current_page].append((self.polygon_mode, points, polygon_id))
            self.change_history.append(("polygon", self.current_page, None, polygon_id))
        else:
            self.start_point = None

        self.redraw_polygons()



    # def embed_polygons_in_pdf(self):
    #     """Embed polygons directly as vector graphics in the PDF with proper scaling."""
    #     if not self.pdf_document:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
    #     page = self.pdf_document[self.current_page]
    #     zoom_matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
    #     self.annotation_is_available = True
    #     for drawing in self.page_drawings[self.current_page]:
    #         if len(drawing) != 3:
    #             print(f"Skipping invalid entry: {drawing}")
    #             continue
    #         mode, points, _ = drawing
    #         scaled_points = [(points[i] / self.zoom_factor, points[i + 1] / self.zoom_factor)
    #                         for i in range(0, len(points), 2)]
    #         path = page.new_shape()
    #         for i in range(len(scaled_points)):
    #             p1 = scaled_points[i]
    #             p2 = scaled_points[(i + 1) % len(scaled_points)]
    #             path.draw_line(p1, p2)
    #         if mode == "filled":
    #             path.finish(fill=(0, 0, 1), color=None)
    #         elif mode == "hollow":
    #             path.finish(color=(1, 0, 0), fill=None)
    #         path.commit()

    def embed_polygons_in_pdf(self):
        """Embed only existing polygons in the PDF with proper scaling."""
        if not self.pdf_document or self.current_page not in self.page_drawings:
            return  # No valid PDF or no drawings on the current page

        page = self.pdf_document[self.current_page]
        
        # Remove old polygon annotations before embedding new ones
        for annot in page.annots():
            if annot.info.get("title") == "polygon_annotation":
                annot.delete()

        zoom_matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
        self.annotation_is_available = True

        # Ensure only non-removed polygons get embedded
        remaining_polygons = []
        
        for drawing in self.page_drawings[self.current_page]:  
            if len(drawing) != 3:
                print(f"Skipping invalid entry: {drawing}")
                continue

            mode, points, polygon_id = drawing

            # Check if this polygon has been removed via undo
            if self.current_page in self.embedded_polygons:
                if any(p[2] == polygon_id for p in self.embedded_polygons[self.current_page]):
                    continue  # Skip embedding removed polygons

            scaled_points = [(points[i] / self.zoom_factor, points[i + 1] / self.zoom_factor)
                            for i in range(0, len(points), 2)]

            path = page.new_shape()
            for i in range(len(scaled_points)):
                p1 = scaled_points[i]
                p2 = scaled_points[(i + 1) % len(scaled_points)]
                path.draw_line(p1, p2)

            if mode == "filled":
                path.finish(fill=(0, 0, 1), color=None)
            elif mode == "hollow":
                path.finish(color=(1, 0, 0), fill=None)

            path.commit()

            remaining_polygons.append(drawing)  # Only keep actually embedded polygons

        self.embedded_polygons[self.current_page] = remaining_polygons  # Update embedded list




    # def on_polygon_drag_entire(self, event):
    #     """Handle dragging to move the entire polygon."""
    #     if not hasattr(self, 'dragging_polygon'):
    #         return
    #     idx, _ = self.dragging_polygon
    #     mode, points, polygon_id = self.page_drawings[self.current_page][idx]

    #     x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
    #     dx, dy = x - self.start_drag_x, y - self.start_drag_y

    #     if not hasattr(self, 'polygon_original_state'):
    #         self.polygon_original_state = points[:]
    #         self.change_history.append(("polygon", self.current_page, self.polygon_original_state, polygon_id))

    #     # Update points and redraw polygon
    #     for i in range(0, len(points), 2):
    #         points[i] += dx
    #         points[i + 1] += dy
    #     self.canvas.coords(polygon_id, points)

    #     # Update start drag position
    #     self.start_drag_x, self.start_drag_y = x, y

    # def on_polygon_drag_entire(self, event):
    #     if not hasattr(self, 'dragging_polygon'):
    #         return
    #     idx, _ = self.dragging_polygon
    #     mode, points, polygon_id = self.page_drawings[self.current_page][idx]

    #     x, y = self.canvas.canvasx(event.x) / self.zoom_factor, self.canvas.canvasy(event.y) / self.zoom_factor
    #     dx, dy = x - self.start_drag_x, y - self.start_drag_y

    #     if not hasattr(self, 'polygon_original_state'):
    #         self.polygon_original_state = points[:]
    #         self.change_history.append(("polygon", self.current_page, self.polygon_original_state, polygon_id))

    #     for i in range(0, len(points), 2):
    #         points[i] += dx
    #         points[i + 1] += dy

    #     scaled_points = [(p * self.zoom_factor) for p in points]
    #     self.canvas.coords(polygon_id, scaled_points)
    #     self.start_drag_x, self.start_drag_y = x, y


    # def on_polygon_drag_vertex(self, event):
    #     """Handle dragging a single vertex of the polygon smoothly."""
    #     if not hasattr(self, 'dragging_polygon'):
    #         return

    #     idx, vertex_idx = self.dragging_polygon
    #     mode, points, polygon_id = self.page_drawings[self.current_page][idx]

    #     x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

    #     if not hasattr(self, 'polygon_original_state'):
    #         self.polygon_original_state = points[:]
    #         self.change_history.append(("polygon", self.current_page, self.polygon_original_state, polygon_id))

    #     # Introduce a snapping threshold for controlled reshaping
    #     snap_threshold = 5  # Pixels
    #     original_x, original_y = points[vertex_idx * 2], points[vertex_idx * 2 + 1]

    #     # Only apply movement if the displacement exceeds the threshold
    #     if abs(x - original_x) > snap_threshold or abs(y - original_y) > snap_threshold:
    #         points[vertex_idx * 2] = x
    #         points[vertex_idx * 2 + 1] = y
    #         self.canvas.coords(polygon_id, points)

    def on_polygon_drag_vertex(self, event):
        if not hasattr(self, 'dragging_polygon'):
            return

        idx, vertex_idx = self.dragging_polygon
        if vertex_idx is None:
            return

        mode, points, polygon_id = self.page_drawings[self.current_page][idx]
        x = self.canvas.canvasx(event.x) / self.zoom_factor
        y = self.canvas.canvasy(event.y) / self.zoom_factor

        x = max(0, min(x, self.page_width / self.zoom_factor))
        y = max(0, min(y, self.page_height / self.zoom_factor))

        points[vertex_idx * 2] = x
        points[vertex_idx * 2 + 1] = y

        scaled_points = [p * self.zoom_factor for p in points]
        self.canvas.coords(polygon_id, *scaled_points)


    def on_polygon_drag_entire(self, event):
        if not hasattr(self, 'dragging_polygon'):
            return
        idx, _ = self.dragging_polygon
        mode, points, polygon_id = self.page_drawings[self.current_page][idx]
        x, y = self.canvas.canvasx(event.x) / self.zoom_factor, self.canvas.canvasy(event.y) / self.zoom_factor
        dx, dy = x - self.start_drag_x, y - self.start_drag_y

        # Constrain entire polygon to remain inside the page boundary
        min_x = min(points[::2]) + dx
        min_y = min(points[1::2]) + dy
        max_x = max(points[::2]) + dx
        max_y = max(points[1::2]) + dy

        if min_x < 0 or max_x > self.page_width / self.zoom_factor or min_y < 0 or max_y > self.page_height / self.zoom_factor:
            return  # Prevent movement outside the page

        for i in range(0, len(points), 2):
            points[i] += dx
            points[i + 1] += dy

        scaled_points = [(p * self.zoom_factor) for p in points]
        self.canvas.coords(polygon_id, scaled_points)

        self.start_drag_x, self.start_drag_y = x, y


    def on_polygon_drag_release(self, event):
        """Release the polygon after dragging."""
        if hasattr(self, 'dragging_polygon'):
            del self.dragging_polygon
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.redraw_polygons()


    def attach_image_to_pdf(self):
        """Attach an image to the currently loaded PDF with interactive placement and resizing."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        image_path = filedialog.askopenfilename(
            title="Select an Image",
            filetypes=[("Image Files", "*.png;*.jpg;*.jpeg"), ("All Files", "*.*")]
        )
        if not image_path:
            return  # User canceled the dialog
 
        try:
            img = Image.open(image_path)
            img.thumbnail((200, 200), Image.LANCZOS)  # Initial size
            self.tk_image = ImageTk.PhotoImage(img)  # Convert to Tkinter-compatible format
            self.current_image = self.canvas.create_image(100, 100, image=self.tk_image, anchor="nw")
            self.image_data = {
                "image_path": image_path,
                "image_obj": img,
                "x": 100, "y": 100,
                "width": img.width, "height": img.height,
            }
            self.canvas.tag_bind(self.current_image, "<ButtonPress-1>", self.start_move)
            self.canvas.tag_bind(self.current_image, "<B1-Motion>", self.do_move)
            self.canvas.tag_bind(self.current_image, "<ButtonRelease-1>", self.finalize_move)
            self.canvas.bind_all("<MouseWheel>", self.resize_image)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load image: {e}")
 
    def start_move(self, event):
        """Start dragging the image."""
        self.image_data["start_x"] = event.x
        self.image_data["start_y"] = event.y
 
    def do_move(self, event):
        """Move the image as the mouse drags."""
        dx = event.x - self.image_data["start_x"]
        dy = event.y - self.image_data["start_y"]
        self.canvas.move(self.current_image, dx, dy)
        self.image_data["x"] += dx
        self.image_data["y"] += dy
        self.image_data["start_x"] = event.x
        self.image_data["start_y"] = event.y
 


    def finalize_move(self, event):
        """Finalize the image position, adjust for zoom/rotation, and embed it correctly in the PDF while maintaining quality."""
        x, y = self.image_data["x"], self.image_data["y"]
        width, height = self.image_data["width"], self.image_data["height"]

        user_response = messagebox.askyesnocancel(
            "Confirm Position",
            "Are you satisfied with the current position and size of the image?"
        )

        if user_response is None:  # User clicked 'Cancel'
            self.canvas.delete(self.current_image)  # Remove the image from canvas
            self.current_image = None
            self.image_data = None
            return  # Stop function execution

        if not user_response:  # User clicked 'No', allow them to move/reshape again
            return  # Do nothing, letting them continue adjusting the image

        # If user clicked 'Yes', proceed with embedding the image
        self.annotation_is_available = True
        try:
            page = self.pdf_document[self.current_page]
            rotation_angle = page.rotation
            x_pdf = x / self.zoom_factor
            y_pdf = y / self.zoom_factor
            width_pdf = width / self.zoom_factor
            height_pdf = height / self.zoom_factor
            page_rect = page.rect

            if rotation_angle == 90:
                x_pdf, y_pdf = y_pdf, page_rect.width - x_pdf - width_pdf
            elif rotation_angle == 180:
                x_pdf, y_pdf = page_rect.width - x_pdf - width_pdf, page_rect.height - y_pdf - height_pdf
            elif rotation_angle == 270:
                x_pdf, y_pdf = page_rect.height - y_pdf - height_pdf, x_pdf

            img_path = self.image_data["image_path"]
            rect = fitz.Rect(x_pdf, y_pdf, x_pdf + width_pdf, y_pdf + height_pdf)
            page.insert_image(rect, filename=img_path)

            self.change_history.append(("image", self.current_page, (x_pdf, y_pdf), (width_pdf, height_pdf), img_path))
            self.render_page(self.current_page)
            self.canvas.unbind_all("<MouseWheel>")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to update PDF: {e}")


    def resize_image(self, event):
        """Resize the image using the mouse scroll."""
        scale_factor = 1.1 if event.delta > 0 else 0.9
        new_width = int(self.image_data["width"] * scale_factor)
        new_height = int(self.image_data["height"] * scale_factor)
        if new_width < 50 or new_height < 50:
            return  # Prevent the image from becoming too small
        self.image_data["width"] = new_width
        self.image_data["height"] = new_height
        img_resized = self.image_data["image_obj"].resize((new_width, new_height), Image.LANCZOS)
        self.tk_image = ImageTk.PhotoImage(img_resized)
        self.canvas.itemconfig(self.current_image, image=self.tk_image)

    def add_text_to_pdf(self):
        """Enable text-adding mode on the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.canvas.bind("<Button-1>", self.on_add_text_click)
        self.add_text_mode = True

    def on_add_text_click(self, event):
        """Handle adding text overlay at the clicked position."""
        if not self.pdf_document or not self.add_text_mode:
            return

        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return

        text = self.ask_for_note_text(x, y, "Add Text")
        if not text:
            return

        wrapped_text = "\n".join(textwrap.wrap(text, width=30))
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor

        # Store text annotation instead of inserting into PDF
        self.text_annotations[(self.current_page, x_scaled, y_scaled)] = wrapped_text
        
        # Store change history for undo
        # changes_data = ("add_text", self.current_page, x_scaled, y_scaled, text)
        # changes_data = str(changes_data)
        # sql_check = """
        #     SELECT COUNT(*) FROM pdf_editor_details 
        #     WHERE folder_path = %s AND filename = %s AND changes_data = %s
        # """
        # mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
        # result = mycursor.fetchone()
        # if result[0] == 0:
        #     sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
        #     val = (beforeexe,folderpath,changes_data,0)
        #     mycursor.execute(sql, val)
        #     mydb.commit()
        self.change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))

        self.render_page(self.current_page)  # Refresh page to show the new text
        self.add_text_mode = False
        self.canvas.unbind("<Button-1>")
        self.annotation_is_available = True

    def redraw_text_annotations(self):
        """Redraw text annotations after rendering the page and adjust for zoom and rotation."""
        self.canvas.delete("text_annotation")  # Clear previous annotations

        if not self.pdf_document:
            return

        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation  # Get current page rotation

        for (page_num, x_scaled, y_scaled), text in self.text_annotations.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor

                # Get page dimensions at the current zoom level
                page_width = page.rect.width * self.zoom_factor
                page_height = page.rect.height * self.zoom_factor
                # Adjust coordinates based on rotation
                if rotation_angle == 90:  # Rotate text **clockwise**
                    if is_small_page == "yes":
                        rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
                    else:
                        rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
                    angle = -90  # Fix: Rotate text correctly to the right
                elif rotation_angle == 180:  # Rotate text upside down
                    rotated_x = page_width - x_position
                    rotated_y = page_height - y_position
                    angle = 180
                elif rotation_angle == 270:  # Rotate text **counterclockwise**
                    if is_small_page == "yes":
                        rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
                    elif is_small_page == "maybe":
                       rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position 
                    else:
                        rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
                    angle = -270  # Fix: Rotate text correctly to the left
                else:  # 0 degrees (default)
                    rotated_x = x_position
                    rotated_y = y_position
                    angle = 0

                text_id = self.canvas.create_text(
                    rotated_x, rotated_y,
                    text=text,
                    font=("Arial", 16),
                    fill="black",
                    tags="text_annotation",
                    anchor="nw"
                )

                # Apply corrected rotation to the text
                self.canvas.itemconfig(text_id, angle=angle)

        self.annotation_is_available = True

    def add_text_with_background(self):
        """Enable text-adding mode for text with a background."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.canvas.bind("<Button-1>", self.on_add_text_with_bg_click)
        self.add_text_bg_mode = True

    def on_add_text_with_bg_click(self, event):
        """Handle adding text with a background at the clicked position."""
        if not self.pdf_document or not self.add_text_bg_mode:
            return

        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)

        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return

        text = self.ask_for_note_text(x, y, "Add Text with Background")
        if not text:
            return

        wrapped_text = "\n".join(textwrap.wrap(text, width=30))
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor

        fontsize = 16
        text_lines = wrapped_text.split("\n")
        max_width = max(len(line) for line in text_lines) * fontsize * 0.6
        text_height = fontsize * 1.2 * len(text_lines)

        # Store the text annotation with background instead of embedding in PDF
        self.text_annotations_bg[(self.current_page, x_scaled, y_scaled)] = wrapped_text

        #Store change history for undo
        # changes_data = ("add_text_bg", self.current_page, x_scaled, y_scaled, text)
        # changes_data = str(changes_data)
        # sql_check = """
        #     SELECT COUNT(*) FROM pdf_editor_details 
        #     WHERE folder_path = %s AND filename = %s AND changes_data = %s
        # """
        # mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
        # result = mycursor.fetchone()
        # if result[0] == 0:
        #     sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
        #     val = (beforeexe,folderpath,changes_data,0)
        #     mycursor.execute(sql, val)
        #     mydb.commit()
        self.change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, text))

        self.render_page(self.current_page)  # Refresh page to show new annotation
        self.add_text_bg_mode = False
        self.canvas.unbind("<Button-1>")
        self.annotation_is_available = True

    def redraw_text_with_background(self):
        """Redraw text annotations with background after rendering the page and adjust for zoom and rotation."""
        self.canvas.delete("text_annotation_bg")  # Clear previous background text

        if not self.pdf_document:
            return

        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation  # Get current page rotation

        for (page_num, x_scaled, y_scaled), text in self.text_annotations_bg.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor

                # Get page dimensions at the current zoom level
                page_width = page.rect.width * self.zoom_factor
                page_height = page.rect.height * self.zoom_factor

                fontsize = 16
                wrapped_text = "\n".join(textwrap.wrap(text, width=30))
                text_lines = wrapped_text.split("\n")
                max_width = max(len(line) for line in text_lines) * fontsize * 0.6
                text_height = fontsize * 1.2 * len(text_lines)
                # Adjust coordinates based on rotation
                if rotation_angle == 90:  # Rotate text **clockwise**
                    if is_small_page == "yes":
                        rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
                    else:
                        rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
                    rect_x1 = rotated_x - text_height - 15
                    rect_y1 = rotated_y
                    rect_x2 = rotated_x
                    rect_y2 = rotated_y + max_width + 10
                    angle = -90  # Fix: Rotate text correctly to the right
                elif rotation_angle == 180:  # Rotate text upside down
                    rotated_x = page_width - x_position
                    rotated_y = page_height - y_position
                    rect_x1 = rotated_x - max_width - 10
                    rect_y1 = rotated_y - text_height - 15
                    rect_x2 = rotated_x
                    rect_y2 = rotated_y
                    angle = 180
                elif rotation_angle == 270:  # Rotate text **counterclockwise**
                    if is_small_page == "yes":
                        rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
                    else:
                        rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
                    rect_x1 = rotated_x
                    rect_y1 = rotated_y - max_width - 10
                    rect_x2 = rotated_x + text_height + 15
                    rect_y2 = rotated_y
                    angle = -270  # Fix: Rotate text correctly to the left
                else:  # 0 degrees (default)
                    rotated_x = x_position
                    rotated_y = y_position
                    rect_x1 = rotated_x
                    rect_y1 = rotated_y
                    rect_x2 = rotated_x + max_width + 10
                    rect_y2 = rotated_y + text_height + 15
                    angle = 0

                rect_id = self.canvas.create_rectangle(
                    rect_x1, rect_y1, rect_x2, rect_y2,
                    fill="cyan",
                    outline="cyan",
                    tags="text_annotation_bg"
                )
          
                text_id = self.canvas.create_text(
                    rotated_x, rotated_y,
                    text=text,
                    font=("Arial", 16),
                    fill="black",
                    tags="text_annotation",
                    anchor="nw"
                )

                self.canvas.itemconfig(text_id, angle=angle)

        self.annotation_is_available = True


    # def activate_line_tool(self):
    #     """Activate the straight line drawing tool."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
    #     self.deactivate_tools()
    #     self.is_drawing_line = True
    #     self.canvas.bind("<Button-1>", self.start_line)
    #     self.canvas.bind("<B1-Motion>", self.draw_line_preview)
    #     self.canvas.bind("<ButtonRelease-1>", self.finish_line)

    # def activate_arrow_tool(self):
    #     """Activate the arrow drawing tool."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
    #     self.deactivate_tools()
    #     self.is_drawing_arrow = True
    #     self.canvas.bind("<Button-1>", self.start_line)
    #     self.canvas.bind("<B1-Motion>", self.draw_line_preview)
    #     self.canvas.bind("<ButtonRelease-1>", self.finish_arrow)

    # def deactivate_tools(self):
    #     """Deactivate all tools."""
    #     self.is_drawing_line = False
    #     self.is_drawing_arrow = False
    #     self.canvas.unbind("<Button-1>")
    #     self.canvas.unbind("<B1-Motion>")
    #     self.canvas.unbind("<ButtonRelease-1>")

    # def start_line(self, event):
    #     """Start drawing a line or arrow."""
    #     self.start_x = self.canvas.canvasx(event.x)
    #     self.start_y = self.canvas.canvasy(event.y)
    #     self.current_line = None

    # def draw_line_preview(self, event):
    #     """Show a preview of the line or arrow while dragging."""
    #     if self.current_line:
    #         self.canvas.delete(self.current_line)

    #     end_x = self.canvas.canvasx(event.x)
    #     end_y = self.canvas.canvasy(event.y)

    #     rotation_angle = self.pdf_document[self.current_page].rotation  # Get current page rotation
    #     start_x, start_y, end_x, end_y = self.apply_rotation_to_line(
    #         self.start_x, self.start_y, end_x, end_y, rotation_angle
    #     )

    #     self.current_line = self.canvas.create_line(
    #         start_x, start_y, end_x, end_y,
    #         fill="red", width=3, tags="annotation"
    #     )

    # def finish_line(self, event):
    #     """Finish drawing the line and store it for redrawing."""
    #     end_x = self.canvas.canvasx(event.x)
    #     end_y = self.canvas.canvasy(event.y)

    #     # Draw line and store its ID
    #     line_id = self.canvas.create_line(
    #         self.start_x, self.start_y, end_x, end_y,
    #         fill="red", width=3, tags="annotation"
    #     )

    #     # Store the original coordinates before rotation
    #     changes_data = ("line", self.current_page, self.start_x, self.start_y, end_x, end_y, line_id)
    #     changes_data = str(changes_data)
    #     sql_check = """
    #         SELECT COUNT(*) FROM pdf_editor_details 
    #         WHERE folder_path = %s AND filename = %s AND changes_data = %s
    #     """
    #     mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
    #     result = mycursor.fetchone()
    #     if result[0] == 0:
    #         sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
    #         val = (beforeexe,folderpath,changes_data,0)
    #         mycursor.execute(sql, val)
    #         mydb.commit()
    #     self.annotations.append(("line", self.current_page, self.start_x, self.start_y, end_x, end_y, line_id))

    #     self.deactivate_tools()
    #     self.annotation_is_available = True
    #     self.redraw_annotations()  # Ensure it updates immediately

    # def finish_arrow(self, event):
    #     """Finish drawing the arrow and store it for redrawing."""
    #     end_x = self.canvas.canvasx(event.x)
    #     end_y = self.canvas.canvasy(event.y)

    #     # Draw arrow and store its ID
    #     arrow_id = self.canvas.create_line(
    #         self.start_x, self.start_y, end_x, end_y,
    #         fill="red", width=3, arrow=ctk.LAST, arrowshape=(16, 20, 6), tags="annotation"
    #     )

    #     # Store the original coordinates before rotation
    #     changes_data = ("arrow", self.current_page, self.start_x, self.start_y, end_x, end_y, arrow_id)
    #     changes_data = str(changes_data)
    #     sql_check = """
    #         SELECT COUNT(*) FROM pdf_editor_details 
    #         WHERE folder_path = %s AND filename = %s AND changes_data = %s
    #     """
    #     mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
    #     result = mycursor.fetchone()
    #     if result[0] == 0:
    #         sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
    #         val = (beforeexe,folderpath,changes_data,0)
    #         mycursor.execute(sql, val)
    #         mydb.commit()
    #     self.annotations.append(("arrow", self.current_page, self.start_x, self.start_y, end_x, end_y, arrow_id))

    #     self.deactivate_tools()
    #     self.annotation_is_available = True
    #     self.redraw_annotations()  # Ensure it updates immediately

    # def redraw_annotations(self):
    #     """Redraw all stored annotations after canvas updates."""
    #     self.canvas.delete("annotation")  # Clear previous annotations

    #     rotation_angle = self.pdf_document[self.current_page].rotation
    #     for annotation in self.annotations:
    #         if len(annotation) == 6:  # Ensure correct unpacking
    #             annot_type, page, x1, y1, x2, y2 = annotation
    #         else:  
    #             continue  # Skip invalid entries

    #         if page == self.current_page:  # Only draw for the active page
    #             x1, y1, x2, y2 = self.apply_rotation_to_line(x1, y1, x2, y2, rotation_angle)

    #             if annot_type == "line":
    #                 self.canvas.create_line(
    #                     x1, y1, x2, y2, fill="red", width=3, tags="annotation"
    #                 )
    #             elif annot_type == "arrow":
    #                 self.canvas.create_line(
    #                     x1, y1, x2, y2, fill="red", width=3, arrow=ctk.LAST, arrowshape=(16, 20, 6), tags="annotation"
    #                 )

    # def apply_rotation_to_line(self, x1, y1, x2, y2, rotation_angle):
    #     """Apply page rotation to the line coordinates dynamically."""
    #     page = self.pdf_document[self.current_page]
    #     page_width = page.rect.width * self.zoom_factor
    #     page_height = page.rect.height * self.zoom_factor

    #     if rotation_angle == 90:
    #         return page_height - y1, x1, page_height - y2, x2
    #     elif rotation_angle == 180:
    #         return page_width - x1, page_height - y1, page_width - x2, page_height - y2
    #     elif rotation_angle == 270:
    #         return y1, page_width - x1, y2, page_width - x2
    #     else:
    #         return x1, y1, x2, y2  # No rotation applied
            
    # def redraw_annotations(self):
    #     """Redraw all stored annotations after canvas updates."""
    #     self.canvas.delete("annotation")  # Clear old drawings
    #     for annotation in self.annotations:
    #         annot_type, page, x1, y1, x2, y2, _ = annotation
    #         if page == self.current_page:  # Redraw only for current page
    #             if annot_type == "line":
    #                 line = self.canvas.create_line(
    #                     x1, y1, x2, y2,
    #                     fill="red", width=3, tags="annotation"
    #                 )
    #                 annotation = ("line", page, x1, y1, x2, y2, line)
    #             elif annot_type == "arrow":
    #                 arrow = self.canvas.create_line(
    #                     x1, y1, x2, y2,
    #                     fill="red", width=3, arrow=ctk.LAST, arrowshape=(16, 20, 6), tags="annotation"
    #                 )
    #                 annotation = ("arrow", page, x1, y1, x2, y2, arrow)

    def activate_line_tool(self):
        """Activate the straight line drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.is_drawing_line = True
        self.canvas.bind("<Button-1>", self.start_drawingline_arrow)
        self.canvas.bind("<B1-Motion>", self.draw_line_previewline_arrow)
        self.canvas.bind("<ButtonRelease-1>", self.finish_line)

    def activate_arrow_tool(self):
        """Activate the arrow drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.is_drawing_arrow = True
        self.canvas.bind("<Button-1>", self.start_drawingline_arrow)
        self.canvas.bind("<B1-Motion>", self.draw_line_previewline_arrow)
        self.canvas.bind("<ButtonRelease-1>", self.finish_arrow)

    def deactivate_tools(self):
        """Deactivate all tools."""
        self.is_drawing_line = False
        self.is_drawing_arrow = False
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    def start_drawingline_arrow(self, event):
        """Start drawing a line or arrow."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.current_line = None

    def draw_line_previewline_arrow(self, event):
        """Show a preview of the line or arrow while dragging."""
        if self.current_line:
            self.canvas.delete(self.current_line)

        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)

        self.current_line = self.canvas.create_line(
            self.start_x, self.start_y, end_x, end_y,
            fill="red", width=3, tags="annotation"
        )

    def finish_line(self, event):
        """Finish drawing the line and store it for redrawing."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        self.store_annotation("line", end_x, end_y)

    def finish_arrow(self, event):
        """Finish drawing the arrow and store it for redrawing."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        self.store_annotation("arrow", end_x, end_y)

    def store_annotation(self, annot_type, end_x, end_y):
        """Store annotation relative to the PDF page."""
        page = self.pdf_document[self.current_page]
        page_width = page.rect.width
        page_height = page.rect.height

        # Convert canvas coordinates to PDF-relative coordinates
        rel_x1 = self.start_x / (page_width * self.zoom_factor)
        rel_y1 = self.start_y / (page_height * self.zoom_factor)
        rel_x2 = end_x / (page_width * self.zoom_factor)
        rel_y2 = end_y / (page_height * self.zoom_factor)

        annot_id = self.canvas.create_line(
            self.start_x, self.start_y, end_x, end_y,
            fill="red", width=3,
            arrow=ctk.LAST if annot_type == "arrow" else None,
            arrowshape=(16, 20, 6) if annot_type == "arrow" else None,
            tags="annotation"
        )

        changes_data = (annot_type, self.current_page, rel_x1, rel_y1, rel_x2, rel_y2, annot_id)
        # self.save_annotation_to_db(changes_data)
        self.change_history.append(changes_data)
        self.annotations.append(changes_data)
        self.deactivate_tools()
        self.annotation_is_available = True
        self.redraw_annotations()


    # def save_annotation_to_db(self, changes_data):
    #     """Save annotation to the database."""
    #     changes_da = str(changes_data)
    #     sql_check = """
    #         SELECT COUNT(*) FROM pdf_editor_details 
    #         WHERE folder_path = %s AND filename = %s AND changes_data = %s
    #     """
    #     mycursor.execute(sql_check, (folderpath, beforeexe, changes_da))
    #     result = mycursor.fetchone()
    #     if result[0] == 0:
    #         sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
    #         val = (beforeexe, folderpath, changes_da, 0)
    #         mycursor.execute(sql, val)
    #         mydb.commit()

    def redraw_annotations(self):
        """Redraw all stored annotations after zoom/rotation."""
        self.canvas.delete("annotation")
        page = self.pdf_document[self.current_page]
        page_width = page.rect.width * self.zoom_factor
        page_height = page.rect.height * self.zoom_factor
        rotation_angle = page.rotation  # Get the actual page rotation

        for annotation in self.annotations:
            if len(annotation) == 7:
                annot_type, page_num, rel_x1, rel_y1, rel_x2, rel_y2, _ = annotation
                if page_num == self.current_page:
                    # Convert relative coords back to canvas
                    x1 = rel_x1 * page_width
                    y1 = rel_y1 * page_height
                    x2 = rel_x2 * page_width
                    y2 = rel_y2 * page_height

                    # Apply rotation
                    x1, y1, x2, y2 = self.apply_rotation_to_line(x1, y1, x2, y2, rotation_angle)
                    if is_small_page == "yes":
                        x1, y1, x2, y2 = x1*self.zoom_factor, y1, x2*self.zoom_factor, y2
                    else:
                        x1, y1, x2, y2 = x1, y1, x2, y2
                    self.canvas.create_line(
                        x1, y1, x2, y2, fill="red", width=3,
                        arrow=ctk.LAST if annot_type == "arrow" else None,
                        arrowshape=(16, 20, 6) if annot_type == "arrow" else None,
                        tags="annotation"
                    )
    
    def apply_rotation_to_line(self, x1, y1, x2, y2, rotation_angle):
        """Correctly rotate a line annotation based on the PDF page rotation."""
        page = self.pdf_document[self.current_page]
        page_width = self.page_width  # Use the stored page width
        page_height = self.page_height  # Use the stored page height

        if rotation_angle == 90:
            if is_small_page == "yes":
                new_x1, new_y1 = page_height+(165*self.zoom_factor) - y1,  x1-20
                new_x2, new_y2 = page_height+(165*self.zoom_factor) - y2,  x2-20
            else:
                new_x1, new_y1 = page_height+(910*self.zoom_factor) - y1,  x1-10
                new_x2, new_y2 = page_height+(910*self.zoom_factor) - y2,  x2-10
        elif rotation_angle == 180:
            new_x1, new_y1 = page_width - x1, page_height - y1
            new_x2, new_y2 = page_width - x2, page_height - y2
        elif rotation_angle == 270:
            if is_small_page == "yes":
                new_x1, new_y1 = y1+10, page_width-(170*self.zoom_factor) - x1
                new_x2, new_y2 = y2+10, page_width-(170*self.zoom_factor) - x2
            else:
                new_x1, new_y1 = y1+15, page_width-(810*self.zoom_factor) - x1
                new_x2, new_y2 = y2+15, page_width-(810*self.zoom_factor) - x2
        else:
            new_x1, new_y1, new_x2, new_y2 = x1, y1, x2, y2

        return new_x1, new_y1, new_x2, new_y2
    


    # def apply_rotation_to_line(self, x1, y1, x2, y2, rotation_angle):
    #     """Correctly rotate a line annotation based on the PDF page rotation."""
    #     page = self.pdf_document[self.current_page]
    #     page_width = page.rect.width * self.zoom_factor
    #     page_height = page.rect.height * self.zoom_factor

    #     if rotation_angle == 90:
    #         new_x1, new_y1 = self.page_height - y1, x1
    #         new_x2, new_y2 = self.page_height - y2, x2
    #     elif rotation_angle == 180:
    #         new_x1, new_y1 = page_width - x1, page_height - y1
    #         new_x2, new_y2 = page_width - x2, page_height - y2
    #     elif rotation_angle == 270:
    #         new_x1, new_y1 = y1, self.page_width - x1
    #         new_x2, new_y2 = y2, self.page_width - x2
    #     else: 
    #         new_x1, new_y1, new_x2, new_y2 = x1, y1, x2, y2

    #     return new_x1, new_y1, new_x2, new_y2


    # def apply_rotation_to_line(self, x1, y1, x2, y2, rotation_angle):
    #     """Apply rotation adjustments to the annotation coordinates."""
    #     page = self.pdf_document[self.current_page]
    #     page_width = page.rect.width * self.zoom_factor
    #     page_height = page.rect.height * self.zoom_factor

    #     if rotation_angle == 90:
    #         return page_height - y1, x1, page_height - y2, x2
    #     elif rotation_angle == 180:
    #         return page_width - x1, page_height - y1, page_width - x2, page_height - y2
    #     elif rotation_angle == 270:
    #         return y1, page_width - x1, y2, page_width - x2
    #     else:
    #         return x1, y1, x2, y2


    def activate_hollow_rectangle_tool(self):
        """Activate the hollow rectangle drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.is_drawing_hollow_rect = True
        self.is_drawing_filled_rect = False  # Ensure only one mode is active
        self.highlight_mode = False
        self.canvas.bind("<Button-1>", self.start_rectangle_drawing)
        self.canvas.bind("<B1-Motion>", self.draw_rectangle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_hollow_rectangle)

    def activate_filled_rectangle_tool(self):
        """Activate the filled rectangle drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.is_drawing_filled_rect = True
        self.is_drawing_hollow_rect = False
        self.highlight_mode = False
        self.canvas.bind("<Button-1>", self.start_rectangle_drawing)
        self.canvas.bind("<B1-Motion>", self.draw_rectangle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_filled_rectangle)

    def start_rectangle_drawing(self, event):
        """Start drawing a rectangle (for hollow/filled tools)."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        
        # Ensure previous rectangle is removed
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        
        # Create an initial small rectangle immediately
        outline_color = "red"
        fill_color = "" if self.is_drawing_hollow_rect else "red"
        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
            outline=outline_color, fill=fill_color, width=2, tags="annotation")

    def draw_rectangle_preview(self, event):
        """Show a preview of the rectangle while dragging."""
        if not hasattr(self, "is_drawing_hollow_rect"):
            self.is_drawing_hollow_rect = False
        if not hasattr(self, "is_drawing_filled_rect"):
            self.is_drawing_filled_rect = False

        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)

        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)

        outline_color = "red"
        fill_color = "" if self.is_drawing_hollow_rect else "red"

        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, end_x, end_y,
            outline=outline_color, fill=fill_color, width=2, tags="annotation"
        )


    def finish_hollow_rectangle(self, event):
        """Finish drawing the hollow rectangle and embed it in the PDF."""
        self.embed_rectangle_in_pdf(event, fill=False)

    def finish_filled_rectangle(self, event):
        """Finish drawing the filled rectangle and embed it in the PDF."""
        self.embed_rectangle_in_pdf(event, fill=True)

    def embed_rectangle_in_pdf(self, event, fill):
        """Embed the drawn rectangle into the PDF."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        page = self.pdf_document[self.current_page]
        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        x1 /= self.zoom_factor
        y1 /= self.zoom_factor
        x2 /= self.zoom_factor
        y2 /= self.zoom_factor

        rect = fitz.Rect(x1, y1, x2, y2)
        if fill:
            rect_id = self.canvas.create_rectangle(
                rect,
                fill="blue",
                outline="blue",
                tags="text_annotation_bg"
            )
            # page.draw_rect(rect, color=(1, 0, 0), fill=(1, 0, 0))
        else:
            rect_id = self.canvas.create_rectangle(
                rect,
                outline="blue",
                tags="text_annotation_bg"
            )
            # page.draw_rect(rect, color=(1, 0, 0), width=2)
        
        self.render_page(self.current_page)
        self.deactivate_tools()
        self.annotation_is_available = True



    def activate_hollow_circle_tool(self):
        """Activate the hollow circle drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.is_drawing_hollow_circle = True
        self.canvas.bind("<Button-1>", self.start_circle)
        self.canvas.bind("<B1-Motion>", self.draw_circle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_hollow_circle)

    def activate_filled_circle_tool(self):
        """Activate the filled circle drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.is_drawing_filled_circle = True
        self.canvas.bind("<Button-1>", self.start_circle)
        self.canvas.bind("<B1-Motion>", self.draw_circle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_filled_circle)

    def start_circle(self, event):
        """Start drawing a circle."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.current_circle = None

    def draw_circle_preview(self, event):
        """Show a preview of the horizontal oval while dragging."""
        if not hasattr(self, "is_drawing_hollow_circle"):  # Ensure attribute exists
            self.is_drawing_hollow_circle = False
        if not hasattr(self, "is_drawing_filled_circle"):
            self.is_drawing_filled_circle = False

        if self.current_circle:
            self.canvas.delete(self.current_circle)
        
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)

        x_radius = abs(end_x - self.start_x)  # Horizontal radius
        y_radius = abs(end_y - self.start_y) / 2  # Vertical radius, keeping it smaller

        outline_color = "blue"
        fill_color = "" if self.is_drawing_hollow_circle else "blue"
        
        self.current_circle = self.canvas.create_oval(
            self.start_x - x_radius, self.start_y - y_radius, 
            self.start_x + x_radius, self.start_y + y_radius,
            outline=outline_color, fill=fill_color, width=2, tags="annotation"
        )

    def finish_hollow_circle(self, event):
        """Finish drawing the hollow circle and embed it in the PDF."""
        self.embed_circle_in_pdf(event, fill=False)

    def finish_filled_circle(self, event):
        """Finish drawing the filled circle and embed it in the PDF."""
        self.embed_circle_in_pdf(event, fill=True)

    def embed_circle_in_pdf(self, event, fill):
        """Embed the drawn oval into the PDF."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        
        x_radius = abs(end_x - self.start_x) / self.zoom_factor
        y_radius = abs(end_y - self.start_y) / (2 * self.zoom_factor)

        x_center, y_center = self.start_x / self.zoom_factor, self.start_y / self.zoom_factor

        page = self.pdf_document[self.current_page]
        oval_rect = fitz.Rect(
            x_center - x_radius, y_center - y_radius, 
            x_center + x_radius, y_center + y_radius
        )
        
        if fill:
            page.draw_oval(oval_rect, color=(0, 0, 1), fill=(0, 0, 1))  # Blue filled oval
        else:
            page.draw_oval(oval_rect, color=(0, 0, 1), width=2)  # Blue outline oval

        self.render_page(self.current_page)
        self.deactivate_tools()
        self.annotation_is_available = True


    def activate_selection_mode(self):
        """Activate the zoom area tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.is_zooming_area = True
        self.canvas.bind("<Button-1>", self.start_zoom_area)
        self.canvas.bind("<B1-Motion>", self.draw_zoom_rectangle)
        self.canvas.bind("<ButtonRelease-1>", self.finish_zoom_area)
        
    def start_zoom_area(self, event):
        """Start drawing the zoom selection rectangle."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.zoom_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x, self.start_y, outline="blue", width=2
        )
        
    def draw_zoom_rectangle(self, event):
        """Update the rectangle as the user drags the mouse."""
        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
        self.canvas.coords(self.zoom_rectangle, self.start_x, self.start_y, current_x, current_y)


####################################### fast and better ##############################################
    def finish_zoom_area(self, event):
        """Zoom into the selected area and keep it centered accurately."""
        if not self.zoom_rectangle:
            return

        # Get selection area in canvas coordinates
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)

        # Convert to PDF coordinates
        x1_pdf, y1_pdf = x1 / self.zoom_factor, y1 / self.zoom_factor
        x2_pdf, y2_pdf = x2 / self.zoom_factor, y2 / self.zoom_factor

        selected_width = x2_pdf - x1_pdf
        selected_height = y2_pdf - y1_pdf

        if selected_width <= 0 or selected_height <= 0:
            return  # Prevent invalid selections

        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()

        # Calculate new zoom factor with bounds
        zoom_x = canvas_width / selected_width
        zoom_y = canvas_height / selected_height
        new_zoom_factor = min(zoom_x, zoom_y)

        # Clamp zoom factor for stability
        new_zoom_factor = max(0.1, min(new_zoom_factor, 10))

        # Calculate new center of selected region in PDF coordinates
        center_x_pdf = (x1_pdf + x2_pdf) / 2
        center_y_pdf = (y1_pdf + y2_pdf) / 2

        # Update zoom factor BEFORE rendering
        self.zoom_factor = new_zoom_factor

        # Render the page with the new zoom
        self.render_page(self.current_page)

        # Calculate the correct scroll offset **after rendering** (fixes position issues)
        canvas_scale = self.zoom_factor / new_zoom_factor  # Adjust scale factor
        scroll_x = ((center_x_pdf * new_zoom_factor) - (canvas_width / 2)) / self.page_width
        scroll_y = ((center_y_pdf * new_zoom_factor) - (canvas_height / 2)) / self.page_height

        # Ensure scroll values are within valid range
        scroll_x = max(0, min(scroll_x, 1))
        scroll_y = max(0, min(scroll_y, 1))

        # Move scrollbars to the correct location
        self.canvas.xview_moveto(scroll_x)
        self.canvas.yview_moveto(scroll_y)

        # Remove the zoom rectangle
        self.canvas.delete(self.zoom_rectangle)
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.is_zooming_area = False

##############################################################################################################


    def toggle_redaction_mode(self):
        """Toggle redaction mode properly without requiring double clicks."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.time_redact_used == 0:
            messagebox.showinfo("Info", "Use redact only after adding all Annotations and changes if not the redact and annotations will be created on the same file.")
            response = messagebox.askyesnocancel("Confirm", "Do you want to save changes before using the redact?")        
            self.time_redact_used +=1
            if response:
                self.save_pdf()
                if self.redaction_mode:
                    self.deactivate_redact_tools()
                else:
                    self.activate_redaction_mode()
            elif response is None:
                return
            else:
                if self.redaction_mode:
                    self.deactivate_redact_tools()
                else:
                    self.activate_redaction_mode()
        else:
            if self.redaction_mode:
                self.deactivate_redact_tools()
            else:
                self.activate_redaction_mode()

    def activate_redaction_mode(self):
        """Ensure activation properly binds events and doesn't toggle incorrectly."""
        self.redaction_mode = True
        self.current_redaction = None  # Prevents lingering boxes
        self.canvas.bind("<Button-1>", self.start_redaction)
        self.canvas.bind("<B1-Motion>", self.draw_redaction_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_redaction)

    def start_redaction(self, event):
        """Start adding a redaction on click."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.current_redaction = None

    def draw_redaction_preview(self, event):
        """Show a redaction preview while dragging."""
        if self.current_redaction:
            self.canvas.delete(self.current_redaction)
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        self.current_redaction = self.canvas.create_rectangle(
            self.start_x, self.start_y, end_x, end_y,
            outline="black", fill="", width=2, tags="redaction_preview")

    def finish_redaction(self, event):
        """Finalize redaction on mouse release using proper PDF redaction annotation."""
        if not self.redaction_mode:
            return

        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        x1, y1 = min(self.start_x, end_x) / self.zoom_factor, min(self.start_y, end_y) / self.zoom_factor
        x2, y2 = max(self.start_x, end_x) / self.zoom_factor, max(self.start_y, end_y) / self.zoom_factor

        rect = fitz.Rect(x1, y1, x2, y2)
        page = self.pdf_document[self.current_page]

        # Add redaction annotation
        page.add_redact_annot(rect, fill=(0, 0, 0))
        print("rect----",rect)
        print("type of rect---",type(rect))
        # type of rect--- <class 'pymupdf.Rect'>
        # changes_data = (self.current_page, rect)
        # changes_data = str(changes_data)
        # sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
        # val = (beforeexe,folderpath,changes_data,1)
        # mycursor.execute(sql, val)
        # mydb.commit()
        self.redactions.append((self.current_page, rect))
        self.redo_redactions.append((self.current_page,self.zoom_factor, rect))
        print("self.redactions--*****",self.redactions)
        print("self.redo_redactions----------*****",self.redo_redactions)
        # Remove preview outline
        if self.current_redaction:
            self.canvas.delete(self.current_redaction)
            self.current_redaction = None  
        self.render_page(self.current_page)
        self.deactivate_redact_tools()  # Ensure deactivation
        self.redaction_mode = False
        self.redact_is_available = True

    def reappear_redact(self):
        """Finalize redaction on mouse release using proper PDF redaction annotation."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if len(self.redo_redactions)==0:
            return
        print("self.redo_redactions----------*****",self.redo_redactions)
        for page_number,zoom_factor,rect in self.redo_redactions:
            if page_number == self.current_page:
                if self.zoom_factor > zoom_factor:
                    zoom_factor = self.zoom_factor - zoom_factor
                elif self.zoom_factor < zoom_factor:
                    zoom_factor = zoom_factor - self.zoom_factor
                elif self.zoom_factor == zoom_factor:
                    zoom_factor = self.zoom_factor
                print("zoom_factor******----",zoom_factor)
                x1 = rect.x0 * zoom_factor
                y1 = rect.y0 * zoom_factor
                x2 = rect.x1 * zoom_factor
                y2 = rect.y1 * zoom_factor
                rect = fitz.Rect(x1, y1, x2, y2)
                page = self.pdf_document[page_number]
                page.add_redact_annot(rect, fill=(0, 0, 0))
                self.redactions.append((self.current_page, rect))
                self.current_redaction = None  
        self.render_page(self.current_page)

    def remove_black_boxes(self):
        """Remove the most recent redaction annotation before applying them."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if len(self.redactions)==0:
            return
        page = self.pdf_document[self.current_page]
        for i in range(len(self.redactions) - 1, -1, -1):
            page_number, rect = self.redactions[i]
            if page_number == self.current_page:
                annot = page.first_annot
                while annot:
                    next_annot = annot.next  # Get next annotation before deleting
                    if self.rects_are_close(annot.rect, rect):
                        page.delete_annot(annot)
                        self.redactions.pop(i)
                        self.render_page(self.current_page)
                        return  # Stop after removing one
                    annot = next_annot

    def rects_are_close(self, rect1, rect2, tol=0.1):
        """Check if two rectangles are approximately equal within a small tolerance."""
        return (
            abs(rect1.x0 - rect2.x0) <= tol and
            abs(rect1.y0 - rect2.y0) <= tol and
            abs(rect1.x1 - rect2.x1) <= tol and
            abs(rect1.y1 - rect2.y1) <= tol
        )
    def deactivate_redact_tools(self):
        """Deactivate the redaction tool and ensure all events are unbound."""
        self.redaction_mode = False
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.current_redaction = None  # Clear any leftover boxes


    def verify_protocol_registration(self):
        """Check and display the protocol registration status"""
        handler = ProtocolHandler()
        is_registered = handler.verify_registration()
        if is_registered:
            status_msg = (
                "Protocol handler is properly registered.\n\n"
                f"Protocol: {handler.protocol}\n"
                f"OS: {handler.os_type}\n"
                f"App Path: {handler.app_path}\n\n"
                "The application will open automatically when clicking PDF links.")
            messagebox.showinfo("Protocol Registration", status_msg)
        else:
            status_msg = (
                "Protocol handler is not registered or registration is incomplete.\n\n"
                f"Protocol: {handler.protocol}\n"
                f"OS: {handler.os_type}\n"
                f"App Path: {handler.app_path}\n\n"
                "Would you like to attempt registration now?")
            result = messagebox.askquestion(
                "Protocol Registration", 
                status_msg,
                icon='warning')
            if result == 'yes':
                try:
                    success, message = handler.register()
                    if success:
                        messagebox.showinfo(
                            "Registration Success", 
                            f"{message}\n\n"
                            f"Protocol: {handler.protocol}\n"
                            f"OS: {handler.os_type}\n"
                            f"App Path: {handler.app_path}")
                    else:
                        messagebox.showerror(
                            "Registration Failed", 
                            f"{message}\n\n"
                            "Please check the console for more details.")
                except Exception as e:
                    messagebox.showerror(
                        "Registration Error", 
                        f"Failed to register protocol handler:\n{str(e)}")

if __name__ == "__main__":
    # Register protocol handler during first run or installation
    try:
        handler = ProtocolHandler()
        success, message = handler.register()
        if success:
            print(message)
        else:
            print(f"Warning: {message}")
    except Exception as e:
        print(f"Failed to register protocol handler: {e}")

    root = ctk.CTk()
    app = StickyNotesPDFApp(root)
    root.mainloop()


























    # def activate_line_tool(self):
    #     """Activate the straight line drawing tool."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
    #     self.deactivate_tools()
    #     self.is_drawing_line = True
    #     self.canvas.bind("<Button-1>", self.start_line)
    #     self.canvas.bind("<B1-Motion>", self.draw_line_preview)
    #     self.canvas.bind("<ButtonRelease-1>", self.finish_line)

    # def activate_arrow_tool(self):
    #     """Activate the arrow drawing tool."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
    #     self.deactivate_tools()
    #     self.is_drawing_arrow = True
    #     self.canvas.bind("<Button-1>", self.start_line)
    #     self.canvas.bind("<B1-Motion>", self.draw_line_preview)
    #     self.canvas.bind("<ButtonRelease-1>", self.finish_arrow)

    # def deactivate_tools(self):
    #     """Deactivate all tools."""
    #     self.is_drawing_line = False
    #     self.is_drawing_arrow = False
    #     self.canvas.unbind("<Button-1>")
    #     self.canvas.unbind("<B1-Motion>")
    #     self.canvas.unbind("<ButtonRelease-1>")

    # def start_line(self, event):
    #     """Start drawing a line or arrow."""
    #     self.start_x = self.canvas.canvasx(event.x)
    #     self.start_y = self.canvas.canvasy(event.y)
    #     self.current_line = None

    # # def draw_line_preview(self, event):
    # #     """Show a preview of the line or arrow while dragging."""
    # #     if self.current_line:
    # #         self.canvas.delete(self.current_line)
    # #     end_x = self.canvas.canvasx(event.x)
    # #     end_y = self.canvas.canvasy(event.y)
    # #     self.current_line = self.canvas.create_line(
    # #         self.start_x, self.start_y, end_x, end_y,
    # #         fill="red", width=3, tags="annotation"
    # #     )

    # # def finish_line(self, event):
    # #     """Finish drawing the line and embed it into the PDF."""
    # #     end_x = self.canvas.canvasx(event.x)
    # #     end_y = self.canvas.canvasy(event.y)
        
    # #     # Draw line on the canvas
    # #     self.canvas.create_line(
    # #         self.start_x, self.start_y, end_x, end_y,
    # #         fill="red", width=3, tags="annotation"
    # #     )

    # #     # Embed the line into the PDF
    # #     self.embed_line_or_arrow(self.start_x, self.start_y, end_x, end_y, is_arrow=False)
    # #     self.deactivate_tools()
    # #     self.annotation_is_available = True

    # # def finish_arrow(self, event):
    # #     """Finish drawing the arrow and embed it into the PDF."""
    # #     end_x = self.canvas.canvasx(event.x)
    # #     end_y = self.canvas.canvasy(event.y)
        
    # #     # Draw arrow on the canvas with a larger arrowhead
    # #     self.canvas.create_line(
    # #         self.start_x, self.start_y, end_x, end_y,
    # #         fill="red", width=3, arrow=ctk.LAST, arrowshape=(16, 20, 6), tags="annotation"
    # #     )

    # #     # Embed the arrow into the PDF
    # #     self.embed_line_or_arrow(self.start_x, self.start_y, end_x, end_y, is_arrow=True)
    # #     self.deactivate_tools()
    # #     self.annotation_is_available = True

    # # def embed_line_or_arrow(self, start_x, start_y, end_x, end_y, is_arrow):
    # #     """Embed a line or arrow directly into the PDF."""
    # #     if not self.pdf_document or self.current_page is None:
    # #         messagebox.showerror("Error", "No PDF loaded.")
    # #         return
        
    # #     page = self.pdf_document[self.current_page]
    # #     # Convert canvas coordinates to PDF coordinates
    # #     x1, y1 = start_x / self.zoom_factor, start_y / self.zoom_factor
    # #     x2, y2 = end_x / self.zoom_factor, end_y / self.zoom_factor

    # #     # Draw the main line
    # #     page.draw_line(p1=(x1, y1), p2=(x2, y2), width=2, color=(1, 0, 0))  # Red color (RGB normalized)

    # #     # If it's an arrow, add arrowhead
    # #     if is_arrow:
    # #         arrow_length = 12
    # #         angle = math.atan2(y2 - y1, x2 - x1)
    # #         # Calculate the points for the arrowhead
    # #         arrow_x1 = x2 - arrow_length * math.cos(angle + math.pi / 6)
    # #         arrow_y1 = y2 - arrow_length * math.sin(angle + math.pi / 6)
    # #         arrow_x2 = x2 - arrow_length * math.cos(angle - math.pi / 6)
    # #         arrow_y2 = y2 - arrow_length * math.sin(angle - math.pi / 6)

    # #         # Draw the arrowhead lines
    # #         page.draw_line(p1=(x2, y2), p2=(arrow_x1, arrow_y1), width=2, color=(1, 0, 0))
    # #         page.draw_line(p1=(x2, y2), p2=(arrow_x2, arrow_y2), width=2, color=(1, 0, 0))

    # #     # Append this change to the history

    # #     changes_data = ("line_or_arrow", self.current_page, x1, y1, x2, y2, is_arrow)
    # #     changes_data = str(changes_data)
    # #     sql_check = """
    # #         SELECT COUNT(*) FROM pdf_editor_details 
    # #         WHERE folder_path = %s AND filename = %s AND changes_data = %s AND redact = 0
    # #     """
    # #     mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
    # #     result = mycursor.fetchone()
    # #     if result[0] == 0:
    # #         sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
    # #         val = (beforeexe,folderpath,changes_data,0)
    # #         mycursor.execute(sql, val)
    # #         mydb.commit()

    # #     self.change_history.append(("line_or_arrow", self.current_page, x1, y1, x2, y2, is_arrow))
    # #     self.annotation_is_available = True