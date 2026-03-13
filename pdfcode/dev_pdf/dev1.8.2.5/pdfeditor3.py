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
import re
import io
import math
import ast
import json
from datetime import date, datetime
import cairosvg
import uuid
import ctypes
import fitz
import time
import textwrap
from shapely.geometry import Point, Polygon
from PIL import Image, ImageTk, ImageOps, ImageSequence, ImageDraw
import requests
import tkinter as tk
from urllib.parse import urlparse, unquote, parse_qs
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

load_dotenv(env_path)


# host = os.getenv("MYSQL_HOST")
# user = os.getenv("MYSQL_USER")
# password = os.getenv("MYSQL_PASSWORD")
# database = os.getenv("MYSQL_DATABASE")
# # Establish db connection
# mydb = mysql.connector.connect(
#     host="127.0.0.1",
#     user="root",
#     password="root",
#     database="redact_viewer"
# )

# mycursor = mydb.cursor()

class StickyNotesPDFApp:
    SOCKET_PORT = 65432 # default socket port for handling the url
    def __init__(self, root):
        self.root = root
        self.is_freeze = "false"
        self.view_redact = "false"
        self.is_locked = "false"
        pdf_url = None
        self.locked_by = "no_body"
        self.page_total = "nope"
        self.new_file_loaded = "yes"
        self.self_locked ="null"
        server_url = "http://localhost:3001" 
        if len(sys.argv) > 1:
            start_time = time.time()
            pdf_url = ProtocolHandler().handle_protocol_url(sys.argv[1])
            if pdf_url:
                self.page_total = "urlpage"
                server_url = pdf_url.split(".com")[0]
                part1, part2 = self.split_url(pdf_url)
                params = parse_qs(part2.lstrip("?"))
                self.is_freeze = params.get("is_freeze", [""])[0]
                self.lasttime_freeze = params.get("is_freeze", [""])[0]
                self.view_redact = params.get("view_redact", [""])[0]
                self.locked_by = params.get("locked_by", [""])[0]
                self.user_id = params.get("user_id", [""])[0]
                self.is_locked = params.get("is_locked", [""])[0]
                if self.is_locked == "true":
                    if self.locked_by == self.user_id:
                        self.self_locked = "me"

            # Set minimum size for the window to prevent excessive shrinking
        self.file_name_is = "attachment_file.pdf"
        # icon for the window title
        self.root.iconbitmap(self.set_window_icon(os.path.join('assets', 'Atic.png')))
        self.zoom_factor = 1.0
        self.freeeze_count = 0
        self.dragged_rectangle_id = None
        self.redact_visible = True
        self.rect_drag_start = None
        self.active_highlight = False
        self.page_highlights = {}
        self.highlight_data = {}  # Store highlights per page {page_num: [coords, ...]}
        self.highlight_rectangles = []
        self.sticky_note_ids = {}  # {(page_num, x_scaled, y_scaled): canvas_id}
        self.dragged_sticky_note = None
        self.all_page_rectangles = {}
        self.sticky_note_drag_start = None
        self.draw_lines_first_time = False
        self.page_height_recdact = 0
        self.polygon_annotations = {}  # Store polygons per page {page_num: [(x1, y1, x2, y2, ...), ...]}
        self.page_width_redact = 0
        self.active_stickynote = False
        self.active_hollowrectangle = False
        # self.highlight_rectangles = {}  # key: rectangle_id, value: (page, annot_id)
        self.active_filledrectangle = False
        self.active_hollowellipse = False
        self.active_filledellipse = False
        self.draw_arrows_first_time = False
        self.active_highlight_filledrectangle = False
        self.active_freehandline = False
        self.active_hollowpolgon = False
        self.active_filledpolygon = False
        self.active_deleteannotation = False
        self.activedeleteredact_button = False
        self.active_line = False
        self.active_arrow = False
        self.thumbnails_ready = False
        self.active_redact = False
        self.scaling_size = 0
        self.add_text_mode = False
        self.add_text_bg_mode = False
        self.dragged_line_id = None
        self.line_drag_start = None
        self.line_total_drag_dx = 0
        self.line_total_drag_dy = 0
        self.dragged_text_bg_key = None
        self.dragged_text_bg_id = None  
        self.text_bg_drag_start = None
        self.file_date_time = ""
        self.time_redact_used = 0
        self.rendered_page_count = 0
        self.lock_screen = "no"
        self.stickynotezoomy = 1.0
        self.annotation_is_available = False
        self.redact_is_available = False
        self.page_rotation = 0
        self.dragged_ellipse_id = None
        self.ellipse_drag_start = None
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.is_drawing_line = False
        self.is_drawing_arrow = False
        self.polygon_mode_created = []  # Store created polygons with their mode
        self.is_drawing_hollow_rect = False  # For hollow rectangle tool
        self.is_drawing_filled_rect = False
        self.is_drawing_hollow_circle = False  # Initialize the attribute
        self.is_drawing_filled_circle = False  # Initialize for filled circle too
        self.last_x, self.last_y = None, None
        self.current_line = None
        self.current_rectangle = None
        self.annotation_listed = []
        self.redact_api_rectangles = []  # Store rectangles from API
        self.redact_api_annotations = []  # Store annotations from API
        self.rectangle_id = None
        self.annotations = [] # Will store all annotations
        self.redact_annotations = []  # Will store redaction annotations
        self.lines = []  # Store line annotations
        self.arrows = []  # Store arrow annotations
        self.rectangles = []
        self.redact_rectangles = []  # Store redaction rectangles
        self.polygon_cord = []
        self.add_pagesize = {}
        self.change_history = []
        self.undo_change_history = []
        self.change_redact_history = []
        self.change_api_redact_history = []
        self.sticky_notes = {}
        self.thumbnails = []
        self.thumbnail_labels = []  # Initialize the missing attribute
        self.thumbnail_cache = {}
        # self.thumbnails_rendered = False
        self.freehand_drawings = []
        self.redactions = []  # To store redaction info (coordinates)
        self.redo_redactions = []
        self.text_annotations = {}
        self.text_annotations_bg = {}
        self.page_drawings = {}
        self.icons = {}
        self.polygons = []
        self.duplicate_windows = []
        # Track scroll position and reset attempts
        self.last_scroll_position = 0
        self._scroll_reset_job = None
        self._selection_attempts = 0
        self.rotated_from_api = 0
        self._thumbnails_rendering = False
        self._target_page_after_load = 0
        self.redaction_mode = False
        self.delete_mode = False
        self.pdf_document = None
        self.current_page = None
        self.is_inverted = False
        self.is_drawing = False  # Default state of the drawing mode
        self.last_x, self.last_y = None, None  # Initialize these as well
        self.polygon_mode = None  # 'filled' or 'hollow'
        self.polygon_size = 50
        self.start_point = None
        self.pagenumber_url = None
        # New attributes for handling movable images
        self.image_overlays = [] 
        # create buttons on the window frame
        self.create_widgets()
        self.canvas.bind("<Button-1>", self.on_canvas_click) # Left click to draw
        self.canvas.bind("<Motion>", self.on_mouse_hover) # Hover to show
        self.root.bind("<Left>", self.prev_page)  # Left arrow for previous page
        self.root.bind("<Right>", self.next_page)  # Right arrow for next page
        self.root.bind("<Up>", self.prev_page)  # Left arrow for previous page
        self.root.bind("<Down>", self.next_page)  # Right arrow for next page
        self.active_tooltip = None
        # default page size
        self.page_width = 0
        self.page_height = 0
        self.root.protocol("WM_DELETE_WINDOW", self.close_main_window) # to allow the main window to close
        self.setup_ipc_server()
        # api to save the annotated and redact file
        # recieving the url from the protocol handler
        # server_url = "http://172.20.1.218:3001/api/v1"
        self.server_url = server_url+r".com/api/v1/uploads/file-annotations"
        self.logger_recorder = "https://idms-dev.blockchaincloudapps.com/api/v1/insert-pdf-viewer-audit" 
        # self.logger_recorder = "http://172.20.1.60:5000/api/v1/insert-pdf-viewer-audit"

        print("server url-----------------------------------------------------------------------------------------------",self.server_url)
        if pdf_url:
            self.handle_url(pdf_url)
            if self.is_freeze == "true":
                self.root.title(f"IDMS Viewer v1.8.2.5 - {self.display_name} {self.file_date_time} - View Only Mode 🔒")
            else:
                self.root.title(f"IDMS Viewer v1.8.2.5 - {self.display_name} {self.file_date_time}")
        else:
            self.root.title("IDMS Viewer v1.8.2.5 - No PDF Loaded")
            
    # window icon 
    def set_window_icon(self, relative_icon_path):
        try:
            if getattr(sys, 'frozen', False):
                base_dir = sys._MEIPASS
            else:
                base_dir = os.path.dirname(os.path.abspath(__file__))
            
            icon_path = os.path.join(base_dir, relative_icon_path)

            if os.path.exists(icon_path):
                self.root.iconphoto(True, ImageTk.PhotoImage(file=icon_path))
            else:
                print(f"Icon file not found: {icon_path}")
        except Exception as e:
            print(f"Failed to set window icon. Error: {e}")
    
    def create_widgets(self):
        hdc = ctypes.windll.user32.GetDC(0)
    
        # Get DPI (dots per inch)
        dpi = ctypes.windll.gdi32.GetDeviceCaps(hdc, 88)  # 88 = LOGPIXELSX

        ctypes.windll.user32.ReleaseDC(0, hdc)

        # Calculate scaling percentage
        self.scaling_size = int(dpi / 96 * 100)
        print("scaling size-----", self.scaling_size)
        toolbar_container = ctk.CTkFrame(self.root,bg_color="#DDDCDC")
        toolbar_container.pack(fill=ctk.X, pady=5)
        if self.is_freeze == "false" and self.lock_screen == "no":
            toolbar_canvas = ctk.CTkCanvas(toolbar_container, height=80, highlightthickness=0, bg="#DDDCDC")
        else:
            toolbar_canvas = ctk.CTkCanvas(toolbar_container, height=40, highlightthickness=0,bg = "#DDDCDC")
        toolbar_canvas.pack(side=ctk.TOP, fill=ctk.X, expand=True)
        
        # Create scrollbar but don't pack it initially
        toolbar_scrollbar = ctk.CTkScrollbar(toolbar_container, orientation="horizontal", command=toolbar_canvas.xview)
        toolbar_canvas.configure(xscrollcommand=toolbar_scrollbar.set)
        
        toolbar = ctk.CTkFrame(toolbar_canvas,bg_color="#DDDCDC")
        canvas_window = toolbar_canvas.create_window((0, 0), window=toolbar, anchor="nw")
        
        min_toolbar_width = 23 * 48 + 150  # 150px for navigation frame
        
        def update_scrollbar_visibility():
            """Show/hide scrollbar based on content width vs canvas width"""
            canvas_width = toolbar_canvas.winfo_width()
            content_width = toolbar.winfo_reqwidth()
            
            if content_width > canvas_width:
                # Content is wider than canvas, show scrollbar
                if not toolbar_scrollbar.winfo_viewable():
                    toolbar_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
            else:
                # Content fits in canvas, hide scrollbar
                if toolbar_scrollbar.winfo_viewable():
                    toolbar_scrollbar.pack_forget()
        
        def update_toolbar_scroll_region(event=None):
            toolbar_canvas.configure(scrollregion=(0, 0, max(min_toolbar_width, toolbar.winfo_reqwidth()), toolbar.winfo_reqheight()))
            toolbar_canvas.itemconfig(canvas_window, width=max(min_toolbar_width, toolbar.winfo_reqwidth()))
            # Update scrollbar visibility after updating scroll region
            toolbar_canvas.after_idle(update_scrollbar_visibility)
        
        toolbar.bind("<Configure>", update_toolbar_scroll_region)
        
        def configure_canvas_width(event):
            if event.width < min_toolbar_width:
                toolbar_canvas.itemconfig(canvas_window, width=min_toolbar_width)
                toolbar_canvas.configure(scrollregion=(0, 0, min_toolbar_width, toolbar.winfo_reqheight()))
            else:
                toolbar_canvas.itemconfig(canvas_window, width=event.width)
            # Update scrollbar visibility when canvas width changes
            toolbar_canvas.after_idle(update_scrollbar_visibility)
        
        toolbar_canvas.bind("<Configure>", configure_canvas_width)
        # toolbar_canvas.bind("<Configure>", lambda e: update_button_rows())

        toolbar.configure(width=min_toolbar_width)
        def create_button(parent, text="", image=None, command=None, tooltip_text="", fg_color=None, hover_color=None):
            button = ctk.CTkButton(
                parent,
                text=text,
                image=image,
                command=command,
                # fg_color="#00498f",
                text_color="white",
                # hover_color="#023261",
                fg_color=fg_color if fg_color else "#00498f",
                hover_color=hover_color if hover_color else "#023261",
                font=("Arial", 12),
                width=50 if self.is_freeze == "false" and self.scaling_size != 100 else 60  # Adjust width based on freeze mode
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
            "delete": load_image("assets/delete.svg"),
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
            "show": load_image("assets/show.svg"),
            "hide": load_image("assets/hide.svg"),
        }

        if self.is_freeze == "false":
            if self.is_locked == "true":
                if self.self_locked == "me":
                    if self.view_redact == "true":
                        button_configs = [
                            {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Page","instance_var":"Lock_button"},
                            {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area","instance_var":"selectzoom_button"},
                            {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Document"},
                            {"image": self.icons['new_window'], "command": lambda: self.create_duplicate_window(fileurl), "tooltip": "New Window", "instance_var":"new_window_button"},
                            {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                            {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                            {"image": self.icons['highlight'], "command": self.activate_Highlight_rectangle_tool, "tooltip": "Highlight","instance_var":"filled_highlight_rectangle_button"},
                            {"image": self.icons['sticky_note'], "command": self.toggle_sticky_note_mode, "tooltip": "Sticky Note", "instance_var":"sticky_note_button"},
                            {"image": self.icons['undo'], "command": self.undo_change, "tooltip": "Undo"},
                            {"image": self.icons['delete'], "command": self.enable_delete_annotation_mode, "tooltip": "Delete Annotation", "instance_var":"delete_button"},
                            {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                            {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                            {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                            {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                            {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                            {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                            {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors", "instance_var":"invert_button"},
                            {"image": self.icons['text'], "command": self.add_text_to_pdf, "tooltip": "Add Text", "instance_var": "text_button"},
                            {"image": self.icons['filled_text'], "command": self.add_text_with_background, "tooltip": "Add Text Stamp", "instance_var": "text_bg_button"},
                            {"image": self.icons['free_line'], "command": self.toggle_drawing, "tooltip": "Free Hand Line", "instance_var": "draw_button"},
                            {"image": self.icons['filled_polygon'], "command": self.toggle_filled_polygon_mode, "tooltip": "Draw Filled Polygon", "instance_var": "filled_polygon_button"},
                            {"image": self.icons['hollow_polygon'], "command": self.toggle_hollow_polygon_mode, "tooltip": "Draw Hollow Polygon", "instance_var": "hollow_polygon_button"},
                            {"image": self.icons.get('image'), "command": lambda: self.attach_image_to_pdf(), "tooltip": "Attach Image", "instance_var": "image_button"},
                            {"image": self.icons['straightline'], "command": self.activate_line_tool, "tooltip": "Draw Straight Line", "instance_var": "line_button"},
                            {"image": self.icons['arrow'], "command": self.activate_arrow_tool, "tooltip": "Draw Arrow", "instance_var": "arrow_button"},
                            {"image": self.icons['hollow_rectangle'], "command": self.activate_hollow_rectangle_tool, "tooltip": "Draw Hollow Rectangle", "instance_var": "hollow_rectangle_button"},
                            {"image": self.icons['filled_rectangle'], "command": self.activate_filled_rectangle_tool, "tooltip": "Draw Filled Rectangle", "instance_var": "filled_rectangle_button"},
                            {"image": self.icons['hollow_ellipse'], "command": self.activate_hollow_ellipse, "tooltip": "Draw Hollow Ellipse", "instance_var": "hollow_ellipse_button"},
                            {"image": self.icons['filled_ellipse'], "command": self.activate_filled_ellipse, "tooltip": "Draw Filled Ellipse", "instance_var": "filled_ellipse_button"},
                            {"image": self.icons['redact'], "command": self.activate_black_rectangle_tool, "tooltip": "Add Redaction", "instance_var": "redact_button"},
                            {"image": self.icons['removeredact'], "command": self.enable_undo_blackrect, "tooltip": "Delete Redaction","instance_var":"deleteredact_button"},
                            {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
                        ]
                    else:
                        button_configs = [
                            {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Page","instance_var":"Lock_button"},
                            {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area","instance_var":"selectzoom_button"},
                            {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Document"},
                            {"image": self.icons['new_window'], "command": lambda: self.create_duplicate_window(fileurl), "tooltip": "New Window", "instance_var":"new_window_button"},
                            {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                            {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                            {"image": self.icons['highlight'], "command": self.activate_Highlight_rectangle_tool, "tooltip": "Highlight","instance_var":"filled_highlight_rectangle_button"},
                            {"image": self.icons['sticky_note'], "command": self.toggle_sticky_note_mode, "tooltip": "Sticky Note", "instance_var":"sticky_note_button"},
                            {"image": self.icons['undo'], "command": self.undo_change, "tooltip": "Undo"},
                            {"image": self.icons['delete'], "command": self.enable_delete_annotation_mode, "tooltip": "Delete Annotation", "instance_var":"delete_button"},
                            {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                            {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                            {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                            {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                            {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                            {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                            {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors", "instance_var":"invert_button"},
                            {"image": self.icons['text'], "command": self.add_text_to_pdf, "tooltip": "Add Text", "instance_var": "text_button"},
                            {"image": self.icons['filled_text'], "command": self.add_text_with_background, "tooltip": "Add Text Stamp", "instance_var": "text_bg_button"},
                            {"image": self.icons['free_line'], "command": self.toggle_drawing, "tooltip": "Free Hand Line", "instance_var": "draw_button"},
                            {"image": self.icons['filled_polygon'], "command": self.toggle_filled_polygon_mode, "tooltip": "Draw Filled Polygon", "instance_var": "filled_polygon_button"},
                            {"image": self.icons['hollow_polygon'], "command": self.toggle_hollow_polygon_mode, "tooltip": "Draw Hollow Polygon", "instance_var": "hollow_polygon_button"},
                            {"image": self.icons.get('image'), "command": lambda: self.attach_image_to_pdf(), "tooltip": "Attach Image", "instance_var": "image_button"},
                            {"image": self.icons['straightline'], "command": self.activate_line_tool, "tooltip": "Draw Straight Line", "instance_var": "line_button"},
                            {"image": self.icons['arrow'], "command": self.activate_arrow_tool, "tooltip": "Draw Arrow", "instance_var": "arrow_button"},
                            {"image": self.icons['hollow_rectangle'], "command": self.activate_hollow_rectangle_tool, "tooltip": "Draw Hollow Rectangle", "instance_var": "hollow_rectangle_button"},
                            {"image": self.icons['filled_rectangle'], "command": self.activate_filled_rectangle_tool, "tooltip": "Draw Filled Rectangle", "instance_var": "filled_rectangle_button"},
                            {"image": self.icons['hollow_ellipse'], "command": self.activate_hollow_ellipse, "tooltip": "Draw Hollow Ellipse", "instance_var": "hollow_ellipse_button"},
                            {"image": self.icons['filled_ellipse'], "command": self.activate_filled_ellipse, "tooltip": "Draw Filled Ellipse", "instance_var": "filled_ellipse_button"},
                            {"image": self.icons['redact'], "command": self.activate_black_rectangle_tool, "tooltip": "Add Redaction", "instance_var": "redact_button"},
                            {"image": self.icons['removeredact'], "command": self.enable_undo_blackrect, "tooltip": "Delete Redaction","instance_var":"deleteredact_button"},
                            {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
                            {"image": self.icons['show'], "command": self.toggle_redact_display, "tooltip": "Show / hide Redact","instance_var":"redacttoggle_button"},
                        ]
                else:
                    button_configs = [
                            {"image": self.icons['lock'], "command": self.dummy_function, "tooltip": "Page is Locked","instance_var":"dummy_button","fg_color": "#d17a24","hover_color": "#b56e26"},
                            {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                            {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                            {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                            {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                            {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                            {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                            {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                            {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                            {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors", "instance_var":"invert_button"},
                        ]
            else:
                if self.view_redact == "true":
                    button_configs = [
                        {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Page","instance_var":"Lock_button"},
                        {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area","instance_var":"selectzoom_button"},
                        {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Document"},
                        {"image": self.icons['new_window'], "command": lambda: self.create_duplicate_window(fileurl), "tooltip": "New Window", "instance_var":"new_window_button"},
                        {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                        {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                        {"image": self.icons['highlight'], "command": self.activate_Highlight_rectangle_tool, "tooltip": "Highlight","instance_var":"filled_highlight_rectangle_button"},
                        {"image": self.icons['sticky_note'], "command": self.toggle_sticky_note_mode, "tooltip": "Sticky Note", "instance_var":"sticky_note_button"},
                        {"image": self.icons['undo'], "command": self.undo_change, "tooltip": "Undo"},
                        {"image": self.icons['delete'], "command": self.enable_delete_annotation_mode, "tooltip": "Delete Annotation", "instance_var":"delete_button"},
                        {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                        {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                        {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                        {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                        {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                        {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                        {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors", "instance_var":"invert_button"},
                        {"image": self.icons['text'], "command": self.add_text_to_pdf, "tooltip": "Add Text", "instance_var": "text_button"},
                        {"image": self.icons['filled_text'], "command": self.add_text_with_background, "tooltip": "Add Text Stamp", "instance_var": "text_bg_button"},
                        {"image": self.icons['free_line'], "command": self.toggle_drawing, "tooltip": "Free Hand Line", "instance_var": "draw_button"},
                        {"image": self.icons['filled_polygon'], "command": self.toggle_filled_polygon_mode, "tooltip": "Draw Filled Polygon", "instance_var": "filled_polygon_button"},
                        {"image": self.icons['hollow_polygon'], "command": self.toggle_hollow_polygon_mode, "tooltip": "Draw Hollow Polygon", "instance_var": "hollow_polygon_button"},
                        {"image": self.icons.get('image'), "command": lambda: self.attach_image_to_pdf(), "tooltip": "Attach Image", "instance_var": "image_button"},
                        {"image": self.icons['straightline'], "command": self.activate_line_tool, "tooltip": "Draw Straight Line", "instance_var": "line_button"},
                        {"image": self.icons['arrow'], "command": self.activate_arrow_tool, "tooltip": "Draw Arrow", "instance_var": "arrow_button"},
                        {"image": self.icons['hollow_rectangle'], "command": self.activate_hollow_rectangle_tool, "tooltip": "Draw Hollow Rectangle", "instance_var": "hollow_rectangle_button"},
                        {"image": self.icons['filled_rectangle'], "command": self.activate_filled_rectangle_tool, "tooltip": "Draw Filled Rectangle", "instance_var": "filled_rectangle_button"},
                        {"image": self.icons['hollow_ellipse'], "command": self.activate_hollow_ellipse, "tooltip": "Draw Hollow Ellipse", "instance_var": "hollow_ellipse_button"},
                        {"image": self.icons['filled_ellipse'], "command": self.activate_filled_ellipse, "tooltip": "Draw Filled Ellipse", "instance_var": "filled_ellipse_button"},
                        {"image": self.icons['redact'], "command": self.activate_black_rectangle_tool, "tooltip": "Add Redaction", "instance_var": "redact_button"},
                        {"image": self.icons['removeredact'], "command": self.enable_undo_blackrect, "tooltip": "Delete Redaction","instance_var":"deleteredact_button"},
                        {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
                    ]
                else:
                    button_configs = [
                        {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Page","instance_var":"Lock_button"},
                        {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area","instance_var":"selectzoom_button"},
                        {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Document"},
                        {"image": self.icons['new_window'], "command": lambda: self.create_duplicate_window(fileurl), "tooltip": "New Window", "instance_var":"new_window_button"},
                        {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                        {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                        {"image": self.icons['highlight'], "command": self.activate_Highlight_rectangle_tool, "tooltip": "Highlight","instance_var":"filled_highlight_rectangle_button"},
                        {"image": self.icons['sticky_note'], "command": self.toggle_sticky_note_mode, "tooltip": "Sticky Note", "instance_var":"sticky_note_button"},
                        {"image": self.icons['undo'], "command": self.undo_change, "tooltip": "Undo"},
                        {"image": self.icons['delete'], "command": self.enable_delete_annotation_mode, "tooltip": "Delete Annotation", "instance_var":"delete_button"},
                        {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                        {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                        {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                        {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                        {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                        {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                        {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors", "instance_var":"invert_button"},
                        {"image": self.icons['text'], "command": self.add_text_to_pdf, "tooltip": "Add Text", "instance_var": "text_button"},
                        {"image": self.icons['filled_text'], "command": self.add_text_with_background, "tooltip": "Add Text Stamp", "instance_var": "text_bg_button"},
                        {"image": self.icons['free_line'], "command": self.toggle_drawing, "tooltip": "Free Hand Line", "instance_var": "draw_button"},
                        {"image": self.icons['filled_polygon'], "command": self.toggle_filled_polygon_mode, "tooltip": "Draw Filled Polygon", "instance_var": "filled_polygon_button"},
                        {"image": self.icons['hollow_polygon'], "command": self.toggle_hollow_polygon_mode, "tooltip": "Draw Hollow Polygon", "instance_var": "hollow_polygon_button"},
                        {"image": self.icons.get('image'), "command": lambda: self.attach_image_to_pdf(), "tooltip": "Attach Image", "instance_var": "image_button"},
                        {"image": self.icons['straightline'], "command": self.activate_line_tool, "tooltip": "Draw Straight Line", "instance_var": "line_button"},
                        {"image": self.icons['arrow'], "command": self.activate_arrow_tool, "tooltip": "Draw Arrow", "instance_var": "arrow_button"},
                        {"image": self.icons['hollow_rectangle'], "command": self.activate_hollow_rectangle_tool, "tooltip": "Draw Hollow Rectangle", "instance_var": "hollow_rectangle_button"},
                        {"image": self.icons['filled_rectangle'], "command": self.activate_filled_rectangle_tool, "tooltip": "Draw Filled Rectangle", "instance_var": "filled_rectangle_button"},
                        {"image": self.icons['hollow_ellipse'], "command": self.activate_hollow_ellipse, "tooltip": "Draw Hollow Ellipse", "instance_var": "hollow_ellipse_button"},
                        {"image": self.icons['filled_ellipse'], "command": self.activate_filled_ellipse, "tooltip": "Draw Filled Ellipse", "instance_var": "filled_ellipse_button"},
                        {"image": self.icons['redact'], "command": self.activate_black_rectangle_tool, "tooltip": "Add Redaction", "instance_var": "redact_button"},
                        {"image": self.icons['removeredact'], "command": self.enable_undo_blackrect, "tooltip": "Delete Redaction","instance_var":"deleteredact_button"},
                        {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
                        {"image": self.icons['show'], "command": self.toggle_redact_display, "tooltip": "Show / hide Redact","instance_var":"redacttoggle_button"},
                    ]
        else:
            button_configs = [
                    {"image": self.icons['lock'], "command": self.dummy_function, "tooltip": "Page is Locked","instance_var":"dummy_button","fg_color": "#d17a24","hover_color": "#b56e26"},
                    {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                    {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                    {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                    {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                    {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                    {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                    {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                    {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                    {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors", "instance_var":"invert_button"},
                ]

        # Create a vertical layout manager frame
        rows_container = ctk.CTkFrame(toolbar,bg_color="#DDDCDC")
        rows_container.pack(side=ctk.TOP, fill=ctk.BOTH)
        current_row = ctk.CTkFrame(rows_container,bg_color="#DDDCDC")
        current_row.pack(side=ctk.TOP, fill=ctk.X, padx=(10, 0))

        if self.is_freeze == "false":
            if self.scaling_size >= 150:
                buttons_in_row = 0
                for config in button_configs:
                    if buttons_in_row >= 24:
                        current_row = ctk.CTkFrame(rows_container,bg_color="#DDDCDC")
                        current_row.pack(side=ctk.TOP, fill=ctk.X, padx=(10, 0))
                        buttons_in_row = 0

                    button = create_button(
                        current_row,
                        image=config["image"],
                        command=config["command"],
                        tooltip_text=config["tooltip"],
                        fg_color=config.get("fg_color"),         # NEW
                        hover_color=config.get("hover_color")
                    )
                    buttons_in_row += 1

                    if "instance_var" in config:
                        setattr(self, config["instance_var"], button)

                # Add nav frame at the end of the last row
                if self.page_total =="urlpage":
                    nav_frame = ctk.CTkFrame(current_row, height=25,bg_color="#DDDCDC")
                    nav_frame.pack(side=ctk.LEFT, pady=0, padx=5)
            elif self.scaling_size >= 125:
                buttons_in_row = 0
                for config in button_configs:
                    if buttons_in_row >= 26:
                        current_row = ctk.CTkFrame(rows_container,bg_color="#DDDCDC")
                        current_row.pack(side=ctk.TOP, fill=ctk.X, padx=(10, 0))
                        buttons_in_row = 0

                    button = create_button(
                        current_row,
                        image=config["image"],
                        command=config["command"],
                        tooltip_text=config["tooltip"],
                        fg_color=config.get("fg_color"),         # NEW
                        hover_color=config.get("hover_color")
                    )
                    buttons_in_row += 1

                    if "instance_var" in config:
                        setattr(self, config["instance_var"], button)

                # Add nav frame at the end of the last row
                if self.page_total =="urlpage":
                    nav_frame = ctk.CTkFrame(current_row, height=25,bg_color="#DDDCDC")
                    nav_frame.pack(side=ctk.LEFT, pady=0, padx=5)
            elif self.scaling_size == 100:
                buttons_in_row = 0
                for config in button_configs:
                    if buttons_in_row >= 28:
                        current_row = ctk.CTkFrame(rows_container,bg_color="#DDDCDC")
                        current_row.pack(side=ctk.TOP, fill=ctk.X, padx=(10, 0))
                        buttons_in_row = 0

                    button = create_button(
                        current_row,
                        image=config["image"],
                        command=config["command"],
                        tooltip_text=config["tooltip"],
                        fg_color=config.get("fg_color"),         # NEW
                        hover_color=config.get("hover_color")
                    )
                    buttons_in_row += 1

                    if "instance_var" in config:
                        setattr(self, config["instance_var"], button)
                if self.page_total =="urlpage":
                    # Add nav frame at the end of the last row
                    nav_frame = ctk.CTkFrame(current_row, height=25,bg_color="#DDDCDC")
                    nav_frame.pack(side=ctk.LEFT, pady=0, padx=5)
        else:
            # Place all buttons and nav in the same single row
            print("*********************************************************************************************")
            for config in button_configs:
                button = create_button(
                    current_row,
                    image=config["image"],
                    command=config["command"],
                    tooltip_text=config["tooltip"],
                    fg_color=config.get("fg_color"),         # NEW
                    hover_color=config.get("hover_color")
                )
                if "instance_var" in config:
                    setattr(self, config["instance_var"], button)
            if self.page_total =="urlpage":
                nav_frame = ctk.CTkFrame(current_row, height=25,bg_color="#DDDCDC")
                nav_frame.pack(side=ctk.LEFT, pady=0, padx=5)

        # navigation buttons
        if self.page_total =="urlpage":
            if self.scaling_size == 100 :
                prev_button = ctk.CTkButton(nav_frame, text="<<<", command=self.prev_page, width=30, fg_color="transparent", text_color="black")
                prev_button.pack(side=ctk.LEFT, padx=(20,0))
                # button for page jump
                self.page_entry = ctk.CTkEntry(nav_frame, width=45, justify="center", height=20)
                self.page_entry.pack(side=ctk.LEFT, padx=0)
                self.page_entry.bind("<Return>", self.go_to_page, add="+")
                # total page count
                self.page_total_label = ctk.CTkLabel(nav_frame, text="/ ?", width=25, fg_color="transparent", text_color="black")
                self.page_total_label.pack(side=ctk.LEFT, padx=0)
                # next button navigation
                next_button = ctk.CTkButton(nav_frame, text=">>>", command=self.next_page, width=30, fg_color="transparent", text_color="black")
                next_button.pack(side=ctk.LEFT, padx=0)
            else:
                prev_button = ctk.CTkButton(nav_frame, text="<<<", command=self.prev_page, width=30, fg_color="transparent", text_color="black")
                prev_button.pack(side=ctk.LEFT, padx=(20,0))
                # button for page jump
                self.page_entry = ctk.CTkEntry(nav_frame, width=45, justify="center", height=20)
                self.page_entry.pack(side=ctk.LEFT, padx=0)
                self.page_entry.bind("<Return>", self.go_to_page, add="+")
                # total page count
                self.page_total_label = ctk.CTkLabel(nav_frame, text="/ ?", width=25, fg_color="transparent", text_color="black")
                self.page_total_label.pack(side=ctk.LEFT, padx=0)
                # next button navigation
                next_button = ctk.CTkButton(nav_frame, text=">>>", command=self.next_page, width=30, fg_color="transparent", text_color="black")
                next_button.pack(side=ctk.LEFT, padx=0)
            

        def on_toolbar_mousewheel(event):
            if event.state & 0x0001:  # Check if Shift key is pressed
                toolbar_canvas.xview_scroll(int(-1*(event.delta/120)), "units")
        
        toolbar_canvas.bind("<MouseWheel>", on_toolbar_mousewheel)
        
        # Initial setup - delay the scrollbar visibility check to ensure widgets are rendered
        self.root.after(100, lambda: [update_toolbar_scroll_region(), update_scrollbar_visibility()])
        # go button but hidden
        if getattr(self, "canvas_frame", None) is None:
            canvas_frame = ctk.CTkFrame(self.root)
            canvas_frame.pack(fill=ctk.BOTH, expand=True)
            # thumbnail frame size
            if self.page_total =="urlpage":
                self.thumbnail_frame = ctk.CTkFrame(canvas_frame, width=175, fg_color="lightgray")
                self.thumbnail_frame.pack(side=ctk.LEFT, fill=ctk.Y)            
                # this one is with the total thumnail frame incliding scrollbar
                self.thumbnail_canvas = ctk.CTkCanvas(self.thumbnail_frame, bg="#073259", width=250)
                # self.thumbnail_scrollbar = ctk.CTkScrollbar(self.thumbnail_frame, orientation="vertical", command=self.thumbnail_canvas.yview)
                self.thumbnail_scrollbar = ctk.CTkScrollbar(self.thumbnail_frame, orientation="vertical", command=self.thumbnail_canvas.yview, width=20)
                self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
                self.thumbnail_canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
                # self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
                self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y, padx=2)
                # self.thumbnail_canvas.bind("<MouseWheel>", self.on_thumbnail_scroll)
                self.inner_thumbnail_frame = ctk.CTkFrame(self.thumbnail_canvas, fg_color="#073259")
                self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
                self.inner_thumbnail_frame.bind("<Configure>", lambda e: self.update_scroll_region() if self.pdf_document else None)
                # total main frame size
            self.canvas = ctk.CTkCanvas(canvas_frame, bg="lightgray", width=1050, height=750) #
            if self.page_total =="urlpage":
                self.h_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="horizontal", command=self.canvas.xview)
                self.v_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="vertical", command=self.canvas.yview)
                self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
                self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
                self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
            self.canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
                # mouse wheel event for pdf render window for scrolling the pdf render  
            if self.page_total =="urlpage":
                self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
                self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
                self.thumbnail_canvas.bind("<Button-1>", self._cancel_scroll_reset)
                self.thumbnail_canvas.bind("<B1-Motion>", self._cancel_scroll_reset)
                self.thumbnail_scrollbar.bind("<Button-1>", self._cancel_scroll_reset)
                self.thumbnail_scrollbar.bind("<B1-Motion>", self._cancel_scroll_reset)
                

    def _cancel_scroll_reset(self, event=None):
        """Cancel the delayed scroll reset if user interacts manually."""
        if hasattr(self, '_scroll_reset_job') and self._scroll_reset_job:
            self.root.after_cancel(self._scroll_reset_job)
            self._scroll_reset_job = None     
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
                handlerurl = ProtocolHandler()
                pdf_url = handlerurl.handle_protocol_url(sys.argv[1])
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

    def split_url(self, url):
        pdf_index = url.lower().find('.pdf')
        if pdf_index == -1:
            return url, ''
        
        part1 = url[:pdf_index + 4]  # Include ".pdf"
        part2 = url[pdf_index + 4:]  # Everything after ".pdf"
        return part1.strip(), part2.strip()

    #to handle url and filter the page number when passed
    def handle_url(self, url):
        try:
            self.root.deiconify()
            self.root.lift()
            self.root.attributes("-topmost", True)
            self.root.focus_force()
            self.root.after(1000, lambda: self.root.attributes("-topmost", False))
            start_time = time.time()
            part1, part2 = self.split_url(url)
            params = parse_qs(part2.lstrip("?"))
            self.current_is_freeze = params.get("is_freeze", [""])[0]
            self.account_name = params.get("account_name", [""])[0]
            self.timer_id = params.get("timer_id", [""])[0]
            self.doc_id = params.get("doc_id", [""])[0]
            self.user_id = params.get("user_id", [""])[0]
            self.display_name = params.get("display_name", [""])[0]
            self.file_date_time = params.get("date_time", [""])[0]
            self.view_redact = params.get("view_redact", [""])[0]
            self.locked_by = params.get("locked_by", [""])[0]
            self.temp_id = params.get("temp_id", [""])[0]
            self.is_locked = params.get("is_locked", [""])[0]
            self.pagenumber_url = int(params.get("page_number", [1])[0])
            self.loaderurl = f"{part1.split('.com/')[0]}.com/api/v1/samba/close-file-loader/"
            self.pdf_file_url = part1
            print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
            print("PDF URL:", self.pdf_file_url)
            print("Account Name:", self.account_name)
            print("Timer ID:", self.timer_id)
            print("Doc ID:", self.doc_id)
            print("Display Name:", self.display_name)
            print("File Date Time:", self.file_date_time)
            print("Is Freeze:", self.is_freeze)
            print("View Redact:", self.view_redact)
            print("Page Number URL:", self.pagenumber_url)
            print("self.temp_id",self.temp_id)
            print("Locked By:", self.locked_by)
            print("User ID:", self.user_id)
            if self.is_locked == "true":
                if self.locked_by == self.user_id:
                    self.self_locked = "me"
            print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
            self.show_loader()
            # Load PDF in background to avoid UI blocking
            threading.Thread(target=self.load_pdf_and_finalize, args=(url, start_time), daemon=True).start()
        except Exception as e:
            print(f"Failed to load PDF in handle_url: {e}")
            self.root.destroy()

    def load_pdf_and_finalize(self, url, start_time):
        try:
            def finalize_after_load():
                end_time = time.time()
                self.rendered_time_cal = f"{end_time - start_time:.2f} sec"
                self.handle_url_execution = f"PDF loaded in: {self.rendered_time_cal}"
                self.action_description = f"{self.display_name} {self.file_date_time} loaded - {self.handle_url_execution}"
                self.action_name = "file loading"
                self.protocol_timer_url = f"{self.pdf_file_url.split('.com/')[0]}.com/api/v1/pdf-timer/{self.timer_id}"
                if self.is_freeze == "true":
                    self.root.after(0, lambda: self.root.title(f"IDMS Viewer v1.8.2.5 - {self.display_name} {self.file_date_time} - View Only Mode 🔒" ))
                else:
                    self.root.after(0, lambda: self.root.title(f"IDMS Viewer v1.8.2.5 - {self.display_name} {self.file_date_time}"))
                threading.Thread(target=self._log_and_notify_backend, daemon=True).start()
                
            self.load_pdf(url, on_complete=finalize_after_load)

        except Exception as e:
            print(f"Error in load_pdf_and_finalize: {e}")
    
    def _log_and_notify_backend(self):
        try:
            payload = {
                "user": self.account_name,
                "viewer_version": "1.8.2",
                "action": self.action_name,
                "description": self.action_description,
            }
            headers = {
                            'Authorization': 'Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJmcmVzaCI6ZmFsc2UsImlhdCI6MTc1NTY2NzY3NywianRpIjoiMWViZThiODAtZTJiZS00MmZkLWIxZWMtNmU2MmI4NWFlOTNkIiwidHlwZSI6ImFjY2VzcyIsInN1YiI6ImRob25pIiwibmJmIjoxNzU1NjY3Njc3LCJjc3JmIjoiZGIxN2UzNzYtOGVlYi00YmI1LTk0MTctZWMyMWJmMjQ1YzgxIiwiZXhwIjoxNzU1NjY4NTc3fQ.oXKx53IBNUtYP575pm53b7WyR8RJXB5jxt1amUdG_wk',
                            'Content-Type': 'application/json'
                        }
            requests.post(self.logger_recorder, headers=headers, json=payload)

            now = datetime.now().isoformat(timespec="milliseconds")
            requests.patch(self.protocol_timer_url, headers=headers, json={"render_time": self.rendered_time_cal})
            requests.post(self.loaderurl, headers=headers, json={"account_id": self.user_id})
            requests.patch(self.protocol_timer_url, headers=headers, json={"loading_close_time": now})
        except Exception as e:
            print(f"Logging/Loader request failed: {e}")


    def loggerIssue_function(self,url,accountname,action_name, actiondescription):                
        payload = json.dumps({
                    "user": accountname,
                    "viewer_version": "1.8.2",
                    "action": action_name,
                    "description": actiondescription
                    })
        headers = {
        'Content-Type': 'application/json'
        }
        response = requests.request("POST", url, headers=headers, data=payload)

    # Enable or disable scrollbar based on the number of pages
    def update_scroll_region(self):
        """Ensures that the scroll region updates properly when thumbnails are added."""
        self.inner_thumbnail_frame.update_idletasks()  # Ensure layout updates first
        
        # Calculate current batch size
        current_batch_start = self.current_thumbnail_batch * self.thumbnail_batch_size
        current_batch_end = min(current_batch_start + self.thumbnail_batch_size, self.total_pages)
        current_batch_size = current_batch_end - current_batch_start
        
        # Get actual bbox
        bbox = self.thumbnail_canvas.bbox("all")
        
        # Handle scrollbar visibility and scroll region based on current batch size
        if current_batch_size > 6:
            # For scrollable batches, use the actual content size or a minimum size
            if bbox:
                # For scrollable content, allow some extra space but not too much
                canvas_height = self.thumbnail_canvas.winfo_height()
                content_height = bbox[3] - bbox[1]
                
                # If content is smaller than canvas, use canvas height to prevent issues
                # If content is larger, use actual content height
                final_height = max(content_height, canvas_height)
                self.thumbnail_canvas.configure(scrollregion=(bbox[0], bbox[1], bbox[2], bbox[1] + final_height))
            else:
                # Fallback calculation for scrollable content
                expected_height = current_batch_size * (self.thumbnail_height + 10)
                self.thumbnail_canvas.configure(scrollregion=(0, 0, 0, expected_height))
            
            self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
            self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
        else:
            # For non-scrollable batches, fit exactly to content
            if bbox:
                # Use exact content size - no extra space
                content_height = bbox[3] - bbox[1]
                self.thumbnail_canvas.configure(scrollregion=(bbox[0], bbox[1], bbox[2], bbox[1] + content_height))
            else:
                # Fallback: use exact calculated height for the thumbnails
                exact_height = current_batch_size * (self.thumbnail_height + 10)
                self.thumbnail_canvas.configure(scrollregion=(0, 0, 0, exact_height))
            
            self.thumbnail_scrollbar.pack_forget()  # Hide scrollbar
            self.thumbnail_canvas.configure(yscrollcommand="")  # Disable scrolling
            # Reset scroll position to top when scrollbar is hidden
            self.thumbnail_canvas.yview_moveto(0)

    # def update_scroll_region(self):
    #     """Ensures that the scroll region updates properly when thumbnails are added."""
    #     self.inner_thumbnail_frame.update_idletasks()  # Ensure layout updates first
    #     self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
        
    #     # Updated condition: show scrollbar only if more than 6 pages
    #     if len(self.pdf_document) > 6:
    #         self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
    #         self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
    #     else:
    #         self.thumbnail_scrollbar.pack_forget()  # Hide scrollbar
    #         self.thumbnail_canvas.configure(yscrollcommand="")  # Disable scrolling
    
    def dummy_function(self):
        """Dummy function to prevent actions when the screen is locked."""
        self.dummybutton.configure(fg_color="#d17a24", hover_color="#b56e26")
        return

    def _load_pdf_internal(self):
        """Internal function that handles PDF loading (called in a thread)."""
        self.root.after(0, lambda: self.canvas.config(cursor="watch"))  # show wait cursor
        try:
            # Instead of using a fixed timer, call best_fit after the page is fully rendered
            # We'll use update_idletasks to ensure UI is updated before calling best_fit
            self.root.after(0, lambda: self.root.update_idletasks())
            self.root.after(100, lambda: self.canvas.update_idletasks())
            # Now call best_fit with a slight delay to ensure canvas size is established
            self.root.after(500, lambda: self.ensure_best_fit())
        except:
            print("Error in best_fit in load pdf") 
        finally:
            self.root.after(0, lambda: self.canvas.config(cursor=""))

    def ensure_best_fit(self):
        """Ensures best_fit is called properly with canvas fully initialized"""
        if self.pdf_document and self.current_page is not None:
            # Check if canvas has actual dimensions
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            
            if canvas_width <= 1 or canvas_height <= 1:
                # Canvas not yet properly sized, try again after a short delay
                print("Canvas not yet sized, retrying best_fit...")
                self.root.after(200, self.ensure_best_fit)
            else:
                # Canvas is ready, apply best_fit
                print(f"Applying best_fit with canvas size: {canvas_width}x{canvas_height}")
                self.best_fit()

    def _timed_render_page(self, page):
        start_time = time.time()
        self.render_page(page)
        end_time = time.time()
        print(f"render_page execution time: {end_time - start_time:.4f} seconds")

    def ensure_thumbnail_selection(self, page_number):
        """Ensures thumbnail selection happens after thumbnails are properly rendered"""
        if not self.pdf_document or not hasattr(self, 'thumbnails'):
            self.root.after(200, lambda: self.ensure_thumbnail_selection(page_number))
            return
            
        if len(self.thumbnails) <= page_number or not hasattr(self, 'thumbnail_canvas') or not self.thumbnail_canvas.winfo_exists():
            # If thumbnails aren't ready yet, retry after a short delay
            self.root.after(200, lambda: self.ensure_thumbnail_selection(page_number))
        else:
            try:
                # Check if thumb_color exists and has enough items
                global thumb_color
                if 'thumb_color' not in globals() or len(thumb_color) <= page_number:
                    self.root.after(200, lambda: self.ensure_thumbnail_selection(page_number))
                    return
                    
                # Track attempts to avoid infinite loops
                if not hasattr(self, '_selection_attempts'):
                    self._selection_attempts = 0
                
                # If too many attempts, ensure we don't get stuck
                if self._selection_attempts > 10:
                    self._selection_attempts = 0
                    return
                    
                self._selection_attempts += 1
                self._timed_thumbnail_selection(page_number)
                self._selection_attempts = 0  # Reset on success
                
            except Exception as e:
                print(f"Error in ensure_thumbnail_selection: {e}")
                # Retry with increased delay if there was an error
                self.root.after(300, lambda: self.ensure_thumbnail_selection(page_number))

    def _timed_thumbnail_selection(self, page):
        start_time = time.time()
        self.update_thumbnail_selection(page)
        end_time = time.time()
        print(f"_timed_thumbnail_selection execution time: {end_time - start_time:.4f} seconds")

    def _timed_render_thumbnails(self):
        start_time = time.time()
        self.render_thumbnails()
        end_time = time.time()
        print(f"render_thumbnails execution time: {end_time - start_time:.4f} seconds")


    # load pdf from the server and local 
    def show_loader(self):
        """Display a blue circling animation as an overlay while PDF loads."""
        canvas_size = 150
        parent_bg = self.root.cget('bg')

        # Prevent duplicate canvases or restarts
        if hasattr(self, "loader_running") and self.loader_running:
            return

        self.loader_canvas = tk.Canvas(
            self.root,
            width=canvas_size,
            height=canvas_size,
            bg="lightgray",
            highlightthickness=0,
            relief='flat',
            borderwidth=0
        )
        self.loader_canvas.place(relx=0.5, rely=0.5, anchor="center")

        self.angle = 0
        self.circle_radius = 50
        self.dot_radius = 8
        center_x = canvas_size // 2
        center_y = canvas_size // 2
        self.loader_running = True

        def animate():
            if not self.loader_running:
                return  # exit loop if loader stopped

            self.loader_canvas.delete("all")

            x = center_x + self.circle_radius * math.cos(math.radians(self.angle))
            y = center_y + self.circle_radius * math.sin(math.radians(self.angle))

            # Outer circle
            self.loader_canvas.create_oval(
                center_x - self.circle_radius, center_y - self.circle_radius,
                center_x + self.circle_radius, center_y + self.circle_radius,
                outline='lightblue', width=2
            )

            # Main dot
            self.loader_canvas.create_oval(
                x - self.dot_radius, y - self.dot_radius,
                x + self.dot_radius, y + self.dot_radius,
                fill='blue', outline='darkblue', width=2
            )

            # Trail dots
            for i in range(1, 4):
                trail_angle = self.angle - i * 15
                trail_x = center_x + self.circle_radius * math.cos(math.radians(trail_angle))
                trail_y = center_y + self.circle_radius * math.sin(math.radians(trail_angle))
                alpha = 1 - (i * 0.3)
                trail_color = f'#{int(135*alpha):02x}{int(206*alpha):02x}{int(235*alpha):02x}'

                self.loader_canvas.create_oval(
                    trail_x - (self.dot_radius - i), trail_y - (self.dot_radius - i),
                    trail_x + (self.dot_radius - i), trail_y + (self.dot_radius - i),
                    fill=trail_color, outline=''
                )

            self.angle = (self.angle + 8) % 360
            self.loader_animation = self.root.after(50, animate)

        animate()


    def hide_loader(self):
        """Stop and remove loader safely."""
        self.loader_running = False
        try:
            if hasattr(self, 'loader_animation'):
                self.root.after_cancel(self.loader_animation)
            if hasattr(self, 'loader_canvas') and self.loader_canvas:
                self.loader_canvas.destroy()
                self.loader_canvas = None
        except Exception as e:
            print(f"Error in hide_loader: {e}")


    def toggle_redact_display(self):
        """Toggle visibility of all redaction rectangles across all pages."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
            
        if not hasattr(self, 'redact_visible'):
            self.redact_visible = False
        
        if not getattr(self, 'thumbnails_ready', False):
            messagebox.showwarning("Wait", "Please wait thumbnail is loading....")
            return
            
        if self.redact_visible:
            # Hide redactions
            self.redacttoggle_button.configure(
                image=self.icons['hide'],
                fg_color="#d17a24", 
                hover_color="#b56e26"
            )
            
            # Remove rectangles from all pages in PDF document
            for page_num in range(len(self.pdf_document)):
                page = self.pdf_document.load_page(page_num)
                
                # Remove annotations from PDF page
                if hasattr(self, 'all_page_rectangles') and page_num in self.all_page_rectangles:
                    for rect_data in self.all_page_rectangles[page_num]:
                        rect_pdf = fitz.Rect(rect_data['x1'], rect_data['y1'], rect_data['x2'], rect_data['y2'])
                        for annot in page.annots():
                            if annot.rect == rect_pdf:
                                annot.delete()
                                break
            
            # Clear canvas rectangles for current page
            self.canvas.delete("annotation")
            self.view_redact = "false"
            # Clear the rectangle data
            if hasattr(self, 'all_page_rectangles'):
                self.all_page_rectangles.clear()
            self.redact_api_rectangles.clear()
            self.redact_api_annotations.clear()
            
            self.annotation_is_available = False
            self.redact_visible = False
            
            # Re-render thumbnails without rectangles
            self.render_thumbnails()
            
        else:
            # Show redactions
            self.redraw_black_rectangles_from_api()
            self.redact_visible = True
            self.redacttoggle_button.configure(
                image=self.icons['show'],
                fg_color="#00498f",
                hover_color="#023261"
            )
            
            # Re-render thumbnails with rectangles
            self.render_thumbnails()
            self.render_page(self.current_page)

    # def toggle_redact_display(self):
    #     """Toggle visibility of all redaction rectangles across all pages."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
        
    #     # Initialize redact_visible to True by default if it doesn't exist
    #     if not hasattr(self, 'redact_visible'):
    #         self.redact_visible = True
        
    #     if not getattr(self, 'thumbnails_ready', False):
    #         messagebox.showwarning("Wait", "Please wait thumbnail is loading....")
    #         return
        
    #     if self.redact_visible:
    #         # Hide redactions
    #         self.redacttoggle_button.configure(
    #             image=self.icons['hide'],
    #             fg_color="#d17a24", 
    #             hover_color="#b56e26")
            
    #         # Remove annotations from PDF pages
    #         for page_num in range(len(self.pdf_document)):
    #             page = self.pdf_document.load_page(page_num)
    #             if hasattr(self, 'all_page_rectangles') and page_num in self.all_page_rectangles:
    #                 for rect_data in self.all_page_rectangles[page_num]:
    #                     rect_pdf = fitz.Rect(rect_data['x1'], rect_data['y1'], rect_data['x2'], rect_data['y2'])
    #                     for annot in page.annots():
    #                         if annot.rect == rect_pdf:
    #                             annot.delete()
    #                             break
            
    #         # Clear canvas annotations
    #         self.canvas.delete("annotation")
            
    #         # Set redact as not visible
    #         self.annotation_is_available = False
    #         self.redact_visible = False
            
    #         # Re-render thumbnails without rectangles
    #         self.render_thumbnails()
            
    #     else:
    #         # Show redactions
    #         self.redact_visible = True
    #         self.redacttoggle_button.configure(
    #             image=self.icons['show'],
    #             fg_color="#00498f",
    #             hover_color="#023261")
            
    #         # If we don't have rectangle data, load it from API
    #         if not hasattr(self, 'all_page_rectangles') or not self.all_page_rectangles:
    #             self.redraw_black_rectangles_from_api()
    #         else:
    #             # Just draw the existing rectangles
    #             self._draw_rectangles_for_current_page()
            
    #         # Re-render thumbnails with rectangles
    #         self.render_thumbnails()

    def _reset_editor_state(self):
        self.sticky_notes.clear()
        self.canvas.delete("sticky_note")
        self.zoom_factor = 1.0
        self.stickynotezoomy = 1.0
        self.redact_visible = False
        self.page_rotation = 0
        self.time_redact_used = 0
        self.sticky_note_mode = False
        self.highlight_rectangles.clear()  # key: rectangle_id, value: (page, annot_id)
        self.highlight_mode = False
        self.annotations.clear()
        self.change_history.clear()
        self.polygon_mode_created.clear()
        self.annotation_listed.clear()
        self.sticky_note_ids = {}  # {(page_num, x_scaled, y_scaled): canvas_id}
        self.dragged_sticky_note = None
        self.sticky_note_drag_start = None
        self.thumbnails.clear()
        self.change_api_redact_history.clear()
        self.lines.clear()
        self.arrows.clear()
        self.dragged_text_bg_key = None
        self.dragged_text_bg_id = None  
        self.text_bg_drag_start = None
        self.rectangles.clear()
        self.redact_rectangles.clear()
        self.redact_annotations.clear()
        self.redact_api_rectangles.clear()
        self.redact_api_annotations.clear()
        self.thumbnail_labels.clear()
        self.thumbnail_cache.clear()
        self.freehand_drawings.clear()
        self.polygon_annotations.clear()
        self.redactions.clear()
        self.line_total_drag_dx = 0
        self.all_page_rectangles = {}
        self.line_total_drag_dy = 0
        self.dragged_rectangle_id = None
        self.thumbnails_ready = False
        self.rect_drag_start = None
        self.dragged_line_id = None
        self.line_drag_start = None
        self.dragged_ellipse_id = None
        self.ellipse_drag_start = None
        self.add_text_mode = False
        self.add_text_bg_mode = False
        self.redo_redactions.clear()
        self.image_overlays.clear()
        self.text_annotations.clear()
        self.page_width_redact = 0
        self.page_height_recdact = 0
        self.text_annotations_bg.clear()
        self.page_drawings.clear()
        self.polygons.clear()
        self.rendered_page_count = 0
        self.is_drawing_hollow_rect = False
        self.draw_lines_first_time = False
        self.draw_arrows_first_time = False
        self.is_drawing_filled_rect = False
        self.is_drawing_hollow_circle = False
        self.is_drawing_filled_circle = False
        self.current_rectangle = None
        self.rectangle_id = None
        self.lock_screen = "no"
        self.annotation_is_available = False
        self.redact_is_available = False
        
    def _process_file_url(self, file_path):
        from urllib.parse import unquote
        decoded_url = unquote(file_path)
        folder_path = re.search(r'documents/(.*?\.pdf)', self.pdf_file_url)
        filename_pdf = folder_path.group(1)
        print("folder_path-------------",folder_path)
        beforeexe = filename_pdf.rsplit('.pdf', 1)[0]
        
        if "_redact.pdf" in decoded_url:
            edit_file_name = redacted_name = beforeexe + ".pdf"
            annotatedredact_url = decoded_url.replace('.pdf', '_with_annotations.pdf')
            annotated_url = decoded_url.replace('_redact.pdf', '_with_annotations.pdf')
        elif "redact_with_annotations.pdf" in decoded_url:
            annotated_url = decoded_url.replace('_redact_with_annotations.pdf', '_with_annotations.pdf')
            annotatedredact_url = decoded_url
            redacted_name = annotatedredact_url
            edit_file_name = beforeexe + ".pdf"
        elif "_with_annotations.pdf" in decoded_url:
            annotated_url = decoded_url
            annotatedredact_url = decoded_url.replace('_with_annotations.pdf','_redact_with_annotations.pdf')
            edit_file_name = beforeexe + ".pdf"
            redacted_name = annotatedredact_url
        else:
            annotated_url = decoded_url.replace('.pdf', '_with_annotations.pdf')
            annotatedredact_url = decoded_url.replace('.pdf', '_redact_with_annotations.pdf')
            redacted_name = decoded_url.replace('.pdf', '_redact.pdf')
            edit_file_name = beforeexe + ".pdf"

        self.decoded_url = decoded_url
        self.filename_pdf = filename_pdf
        self.beforeexe = beforeexe
        self.edit_file_name = edit_file_name
        self.annotated_url = annotated_url
        self.annotatedredact_url = annotatedredact_url
        self.redacted_name = redacted_name
        print("*************************************************************************************************************************************************************************************************************************************************")
        print(f"Decoded URL: {decoded_url}")
        print(" ")
        print(f"Filename PDF: {filename_pdf}")
        print("  ")
        print(f"Before EXE: {beforeexe}")
        print(" ")
        print(f"Edit File Name: {edit_file_name}")
        print(" ")
        print(f"Annotated URL: {annotated_url}")
        print(" ")
        print(f"Annotated Redact URL: {annotatedredact_url}")
        print(" ")
        print(f"Redacted Name: {redacted_name}")
        print("***********************************************************************************************************************************************************************************************************************************************************")

    def freeze_function(self):
        # Destroy all widgets safely
        for widget in self.root.winfo_children():
            widget.destroy()
        self.create_widgets()

    def load_pdf(self, file_path=None, on_complete=None):
        if not file_path:
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        if not file_path:
            print("No file selected")
            return
        print("self.is_freeze -----------------------------------------", self.is_freeze)
        print("self.current_is_freeze -----------------------------------------", self.current_is_freeze)
        print("self.lasttime_freeze -----------------------------------------", self.lasttime_freeze)

        if self.current_is_freeze != self.lasttime_freeze:
            print("freeze function called as the freeze state has changed")
            self.is_freeze = self.current_is_freeze
            self.freeze_function()
            self.lasttime_freeze = self.current_is_freeze

        print("self.is_freeze -----------------------------------------", self.is_freeze)
        print(f"Loading PDF from: {file_path}")
        global fileurl
        fileurl = file_path
        def task():
            try:
                self._reset_editor_state()
                self.load_pdf_url = file_path
                parsed = urlparse(file_path)
                if parsed.scheme in ("http", "https"):
                    try:
                        response = requests.get(file_path)
                        response.raise_for_status()
                        pdf_data = response.content
                    except requests.exceptions.SSLError:
                        response = requests.get(file_path, verify=False)
                        response.raise_for_status()
                        pdf_data = response.content
                    self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
                else:
                    print("Invalid file path or URL.")
                    self.root.after(0, self.hide_loader)
                    return

                if len(self.pdf_document) == 0:
                    raise ValueError("The PDF has no pages.")

                self.current_page = int(self.pagenumber_url) - 1 if self.pagenumber_url is not None else 0
                self.pagenumber_url = None
                self.page_drawings.clear()
                self.file_loaded_first_time = True
                self.is_inverted = False
                self.view_redact = "true"
                first_page = self.pdf_document[self.current_page]
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                print("PDF loaded successfully and rotation is ",first_page.rotation)
                self.very_first_rotation_degree = first_page.rotation
                self.file_opened_for_the_first_time = True
                if first_page.rotation == 90:
                    first_page.set_rotation((first_page.rotation + 270) % 360)
                elif first_page.rotation == 270:
                    first_page.set_rotation((first_page.rotation + 90) % 360)
                print("PDF loaded successfully and rotation is ",first_page.rotation)
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")
                self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
                print(f"Page size: width {self.page_width} x hight {self.page_height}")
                self.page_entry.delete(0, "end")
                # 1275.0 x hight 1650.0
                global is_small_page
                if  self.page_width < 850 and self.page_height < 550:
                    is_small_page = "very small"
                elif self.page_width < 1000:
                    is_small_page = "yes"
                elif self.page_width <= 1500 and self.page_height < 1000:
                    is_small_page = "smaller"
                elif self.page_width <= 1500 and self.page_height < 2000:
                    is_small_page = "small"
                elif 2000 < self.page_width < 3000 and self.page_height > 2800:
                    is_small_page = "longer"
                elif 3000 < self.page_width < 3500 and 2000 < self.page_height < 3000:
                    is_small_page = "wider"
                elif 1000 <= self.page_width < 2500:
                    is_small_page = "slightly"
                elif 2500 <= self.page_width < 3000:
                    is_small_page = "maybe"
                elif 3000 <= self.page_width < 5000:
                    is_small_page = "nope large"
                elif self.page_width >= 10000:
                    is_small_page = "nope very large"
                else:
                    is_small_page = "no"
                self.root.after(0, lambda: self._timed_render_page(self.current_page))
                print("is_small_page----",is_small_page)              
                self.root.after(0, self._timed_render_thumbnails)
                self.root.after(100, lambda: self.ensure_thumbnail_selection(self.current_page))
                self.update_page_display()
                self._process_file_url(file_path)
                if on_complete:
                    self.root.after(0, on_complete)
                    self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
                    print(f"Page size after all processing: width {self.page_width} x hight {self.page_height}")
            except Exception as e:
                print(f"Failed to load PDF: {e}")
                messagebox.showerror("Error", f"Failed to load PDF: 400 Bad URL Request")
                self.pdf_document = None
                self.current_page = None
                self.root.destroy()
            finally:
                self.root.after(0, self.hide_loader)

        threading.Thread(target=task).start()

##########################################################################################################################################################################################

    def render_thumbnails(self):
        if not self.pdf_document:
            print("No PDF document loaded for thumbnails.")
            return
        self.thumbnail_batch_size = 20
        self.current_thumbnail_batch = -1  # None loaded initially
        self.thumbnails = []
        self.thumbnail_cache = {}
        self.thumbnails_ready = False
        global thumb_color
        thumb_color = []
        self.total_pages = len(self.pdf_document)
        self.thumbnail_width = 100
        self.thumbnail_height = 150
        self.thumbnail_canvas.bind("<Configure>", self.check_and_update_thumbnail_batch)
        self._user_scrolling = False
        self._batch_check_job = None
        
        # Ensure current_page is properly initialized for first load
        if not hasattr(self, 'current_page') or self.current_page is None:
            self.current_page = 0  # Initialize to first page (0-indexed)
        
        # Initial scroll setup will be done in load_thumbnail_batch based on batch size
        self.load_thumbnail_batch(0)

    def on_thumbnail_scroll(self, event):
        # Check current batch size, not total document pages
        current_batch_start = self.current_thumbnail_batch * self.thumbnail_batch_size
        current_batch_end = min(current_batch_start + self.thumbnail_batch_size, self.total_pages)
        current_batch_size = current_batch_end - current_batch_start
        
        if current_batch_size <= 6:
            return
        if hasattr(self, '_scroll_reset_job') and self._scroll_reset_job:
            self.root.after_cancel(self._scroll_reset_job)
            self._scroll_reset_job = None
        self.thumbnail_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        if hasattr(self, '_batch_check_job') and self._batch_check_job:
            self.root.after_cancel(self._batch_check_job)
        self._batch_check_job = self.root.after(500, self.check_and_update_thumbnail_batch)

    def check_and_update_thumbnail_batch(self, event=None):
        # Ensure current_page is valid
        if not hasattr(self, 'current_page') or self.current_page is None:
            target_page = 0  # Default to first page
        else:
            target_page = max(0, min(self.current_page, self.total_pages - 1))  # Ensure within valid range
        
        new_batch_index = target_page // self.thumbnail_batch_size
        if new_batch_index != self.current_thumbnail_batch:
            print(f"Switching from batch {self.current_thumbnail_batch} to batch {new_batch_index} (page {target_page})")
            self.load_thumbnail_batch(new_batch_index)

    def load_thumbnail_batch(self, batch_index):
        print(f"Loading batch {batch_index} (pages {batch_index * self.thumbnail_batch_size + 1}-{min((batch_index + 1) * self.thumbnail_batch_size, self.total_pages)})")
        for widget in self.inner_thumbnail_frame.winfo_children():
            widget.destroy()
        self.thumbnails.clear()
        self.thumbnail_cache.clear()
        global thumb_color
        thumb_color.clear()
        self.current_thumbnail_batch = batch_index
        start_page = batch_index * self.thumbnail_batch_size
        end_page = min(start_page + self.thumbnail_batch_size, self.total_pages)
        if start_page >= self.total_pages:
            print(f"Batch {batch_index} is beyond total pages ({self.total_pages})")
            return
        
        # Calculate current batch size
        current_batch_size = end_page - start_page
        
        # Setup scroll behavior based on current batch size
        self._setup_scroll_behavior(current_batch_size)
        
        # Create placeholder labels first to maintain order
        self.thumbnail_placeholders = {}
        for page_number in range(start_page, end_page):
            placeholder_label = ctk.CTkLabel(self.inner_thumbnail_frame, text=f"Loading Page {page_number + 1}...")
            placeholder_label.page_number = page_number
            placeholder_label.pack(pady=5, padx=50)
            self.thumbnail_placeholders[page_number] = placeholder_label
            self.thumbnails.append(placeholder_label)
            thumb_color.append(placeholder_label)
        
        # Update scroll region immediately after creating placeholders
        self.update_scroll_region()
        
        def load_batch_worker():
            # Process pages sequentially to maintain order
            for page_number in range(start_page, end_page):
                try:
                    page = self.pdf_document.load_page(page_number)
                    pix = page.get_pixmap(matrix=fitz.Matrix(0.5, 0.5))
                    img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                    
                    try:
                        if (hasattr(self, 'all_page_rectangles') and 
                            page_number in self.all_page_rectangles and 
                            self.all_page_rectangles[page_number]):
                            img = self._add_rectangles_to_thumbnail(img, page_number, pix.width, pix.height)
                    except:
                        if (hasattr(self, 'redact_visible') and self.redact_visible and 
                            hasattr(self, 'all_page_rectangles') and page_number in self.all_page_rectangles):
                            img = self._add_rectangles_to_thumbnail(img, page_number, pix.width, pix.height)

                    img.thumbnail((self.thumbnail_width, self.thumbnail_height), Image.LANCZOS)
                    photo = ImageTk.PhotoImage(img)
                    self.thumbnail_cache[page_number] = photo

                    # Update the placeholder with the actual thumbnail
                    self.inner_thumbnail_frame.after(0, lambda pn=page_number, ph=photo: self.update_thumbnail_placeholder(pn, ph))
                except Exception as e:
                    print(f"Error rendering thumbnail for page {page_number}: {e}")
                    # Update placeholder to show error
                    self.inner_thumbnail_frame.after(0, lambda pn=page_number: self.update_thumbnail_error(pn))
            
            # Final updates after all thumbnails are processed
            self.inner_thumbnail_frame.after(100, self.update_scroll_region)
            self.inner_thumbnail_frame.after(200, lambda: self.update_thumbnail_selection(self.current_page))
            self.inner_thumbnail_frame.after(300, lambda: setattr(self, 'thumbnails_ready', True))
        
        threading.Thread(target=load_batch_worker, daemon=True).start()

    def _setup_scroll_behavior(self, current_batch_size):
        """Setup scroll behavior based on current batch size."""
        # Remove any existing scroll bindings
        self.thumbnail_canvas.unbind("<Enter>")
        self.thumbnail_canvas.unbind("<Leave>")
        self.thumbnail_canvas.unbind_all("<MouseWheel>")
        
        if current_batch_size > 6:
            def start_scroll(e):
                self._user_scrolling = True
                self.thumbnail_canvas.bind_all("<MouseWheel>", self.on_thumbnail_scroll)
            
            def end_scroll(e):
                self._user_scrolling = False
                self.thumbnail_canvas.unbind_all("<MouseWheel>")
                self.root.after(100, self.check_and_update_thumbnail_batch)
            
            self.thumbnail_canvas.bind("<Enter>", start_scroll)
            self.thumbnail_canvas.bind("<Leave>", end_scroll)
        # If batch size <= 6, don't bind any scroll events

    def update_thumbnail_placeholder(self, page_number, photo):
        """Update a placeholder label with the actual thumbnail image."""
        if page_number in self.thumbnail_placeholders:
            placeholder = self.thumbnail_placeholders[page_number]
            placeholder.configure(image=photo, text=f"Page {page_number + 1}")
            placeholder.image = photo  # Keep reference
            placeholder.bind("<Button-1>", self.create_page_selection_handler(page_number))

    def update_thumbnail_error(self, page_number):
        """Update a placeholder label to show an error."""
        if page_number in self.thumbnail_placeholders:
            placeholder = self.thumbnail_placeholders[page_number]
            placeholder.configure(text=f"Error Page {page_number + 1}")
            placeholder.bind("<Button-1>", self.create_page_selection_handler(page_number))

    def add_thumbnail(self, page_number, photo):
        # This method is now replaced by update_thumbnail_placeholder
        # Keeping it for compatibility if called elsewhere
        label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
        label.image = photo
        label.page_number = page_number
        label.pack(pady=5, padx=50)
        label.bind("<Button-1>", self.create_page_selection_handler(page_number))
        self.thumbnails.append(label)
        thumb_color.append(label)

    def _add_rectangles_to_thumbnail(self, img, page_number, pix_width, pix_height):
        """Add redaction rectangles to thumbnail image."""
        from PIL import ImageDraw
        if page_number not in self.all_page_rectangles:
            return img
        if img.mode != 'RGB':
            img = img.convert('RGB')
        
        draw = ImageDraw.Draw(img)
        page = self.pdf_document.load_page(page_number)
        page_width, page_height = page.rect.width, page.rect.height
        scale_x = pix_width / page_width
        scale_y = pix_height / page_height
        for rect_data in self.all_page_rectangles[page_number]:
            x1 = int(rect_data['x1'] * scale_x)
            y1 = int(rect_data['y1'] * scale_y)
            x2 = int(rect_data['x2'] * scale_x)
            y2 = int(rect_data['y2'] * scale_y)
            if rect_data['filled']:
                draw.rectangle([x1, y1, x2, y2], fill='black', outline='black', width=1)
            else:
                draw.rectangle([x1, y1, x2, y2], outline='black', width=1)
        return img

    def create_page_selection_handler(self, page_number):
        """Return a handler function to navigate to the selected page."""
        def handler(event):
            print(f"Thumbnail {page_number} clicked. Current page before: {self.current_page}")
            self.select_page(page_number)
            print(f"Current page after: {self.current_page}")
        return handler

    def update_thumbnail_selection(self, page_number):
        """Update the highlight of the selected thumbnail and ensure it's visible in the scroll view."""
        print(f"Updating thumbnail selection to page {page_number}")
        
        # Ensure page_number is valid
        if page_number is None or page_number < 0 or page_number >= self.total_pages:
            page_number = 0  # Default to first page if invalid
        
        current_batch_start = self.current_thumbnail_batch * self.thumbnail_batch_size
        current_batch_end = current_batch_start + self.thumbnail_batch_size
        if not (current_batch_start <= page_number < current_batch_end):
            needed_batch = page_number // self.thumbnail_batch_size
            if needed_batch != self.current_thumbnail_batch:
                self.load_thumbnail_batch(needed_batch)
                return
        for label in thumb_color:
            if hasattr(label, 'page_number'):
                label.configure(
                    text=f"Page {label.page_number + 1}",
                    text_color="black",
                    fg_color="transparent",
                    corner_radius=0)
                if hasattr(label, "original_image"):
                    label.configure(image=label.original_image)
        for label in thumb_color:
            if hasattr(label, 'page_number') and label.page_number == page_number:
                label.configure(
                    text="Selected Page", 
                    text_color="red",    
                    fg_color="#c41818", 
                    corner_radius=4, 
                    compound="center")
                self.inner_thumbnail_frame.update_idletasks()
                self.selected_label_info = label
                self.root.after(100, lambda: self.scroll_to_thumbnail(label, page_number))
                break 
    
    def select_page(self, page_number):
        """Handle thumbnail click event to switch pages."""
        if 0 <= page_number < len(self.pdf_document):
            print(f"Selecting page: {page_number} (0-based), Display: {page_number + 1}")  # Debug log
            
            self.current_page = page_number
            
            if hasattr(self, 'page_drawings'):
                if isinstance(self.page_drawings, list):
                    self.current_page_drawings = [d for d in self.page_drawings if isinstance(d, dict) and d.get('page') == page_number]
            
            # Get page dimensions
            first_page = self.pdf_document[self.current_page]
            self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
            print(f"Page size: width {self.page_width} x hight {self.page_height}")
            global is_small_page
            if  self.page_width < 850 and self.page_height < 550:
                is_small_page = "very small"
            elif self.page_width < 1000:
                is_small_page = "yes"
            elif self.page_width <= 1500 and self.page_height < 1000:
                is_small_page = "smaller"
            elif self.page_width <= 1500 and self.page_height < 2000:
                is_small_page = "small"
            elif 2000 < self.page_width < 3000 and self.page_height > 2800:
                is_small_page = "longer"
            elif 3000 < self.page_width < 3500 and 2000 < self.page_height < 3000:
                is_small_page = "wider"
            elif 1000 <= self.page_width < 2500:
                is_small_page = "slightly"
            elif 2500 <= self.page_width < 3000:
                is_small_page = "maybe"
            elif 3000 <= self.page_width < 5000:
                is_small_page = "nope large"
            elif self.page_width >= 10000:
                is_small_page = "nope very large"
            else:
                is_small_page = "no"
            print("is_small_page----",is_small_page)
            # Render the selected page
            self.render_page(self.current_page)
            
            # Update displays - make sure this happens after page is set
            self.update_page_display()
            self.update_thumbnail_selection(page_number)
            self.check_and_update_thumbnail_batch()
        else:
            print(f"Invalid page number: {page_number}. Total pages: {len(self.pdf_document)}")

    # def select_page(self, page_number):
    #     """Handle thumbnail click event to switch pages."""
    #     print(f"select_page called with page_number: {page_number}")
    #     if 0 <= page_number < len(self.pdf_document):
    #         print(f"Valid page number. Setting current_page from {self.current_page} to {page_number}")
    #         self.current_page = page_number
            
    #         if hasattr(self, 'page_drawings'):
    #             if isinstance(self.page_drawings, list):
    #                 self.current_page_drawings = [d for d in self.page_drawings if isinstance(d, dict) and d.get('page') == page_number]
            
    #         first_page = self.pdf_document[self.current_page]
    #         self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
    #         first_page = self.pdf_document[self.current_page]
    #         print(f"Page size: width {self.page_width} x hight {self.page_height}")
    #         global is_small_page
    #         if  self.page_width < 850 and self.page_height < 550:
    #             is_small_page = "very small"
    #         elif self.page_width < 1000:
    #             is_small_page = "yes"
    #         elif self.page_width <= 1500 and self.page_height < 1000:
    #             is_small_page = "smaller"
    #         elif self.page_width <= 1500 and self.page_height < 2000:
    #             is_small_page = "small"
    #         elif 2000 < self.page_width < 3000 and self.page_height > 2800:
    #             is_small_page = "longer"
    #         elif 3000 < self.page_width < 3500 and 2000 < self.page_height < 3000:
    #             is_small_page = "wider"
    #         elif 1000 <= self.page_width < 2500:
    #             is_small_page = "slightly"
    #         elif 2500 <= self.page_width < 3000:
    #             is_small_page = "maybe"
    #         elif 3000 <= self.page_width < 5000:
    #             is_small_page = "nope large"
    #         elif self.page_width >= 10000:
    #             is_small_page = "nope very large"
    #         else:
    #             is_small_page = "no"
    #         print("is_small_page----",is_small_page)
    #         self.render_page(self.current_page)
    #         self.update_page_display()
    #         self.update_thumbnail_selection(page_number)
            
    #         # Check if we need to load a different batch
    #         self.check_and_update_thumbnail_batch()
            
    #         print(f"Page selection completed. Current page is now: {self.current_page}")
    #     else:
    #         print(f"Invalid page number: {page_number}. Total pages: {len(self.pdf_document)}")

    # to render the page on the duplicate canvas
    def create_duplicate_window(self, fileurl):
        """Creates a duplicate window to display a PDF independently."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if not fileurl:
            messagebox.showerror("Error", "No PDF is currently loaded to duplicate.")
            return   
        self.new_window_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        duplicate_root = ctk.CTkToplevel(self.root) 
        duplicate_window = DuplicateStickyNotesPDFApp(duplicate_root, fileurl)
        self.duplicate_windows.append(duplicate_root) # Keep track of duplicate windows

        def on_close():
            self.duplicate_windows.remove(duplicate_root)
            duplicate_root.destroy()
            if len(self.duplicate_windows) == 0:
                self.new_window_button.configure(fg_color="#00498f", hover_color="#023261")

        duplicate_root.protocol("WM_DELETE_WINDOW", on_close)
    # close only when all the duplicate window are closed
    def close_main_window(self):
        """Closes the main window only if there are no duplicate windows open."""
        if self.duplicate_windows:
            messagebox.showerror("Warning", "Please close all duplicate windows before exiting the main window.")
        else:
            self.root.destroy()


    # def lock_function(self):      
    #     self.lock_screen = "yes" if self.lock_screen == "no" else "no"
    #     current_page_number = self.current_page
    #     current_pdf = self.pdf_document
    #     # Destroy all widgets safely
    #     for widget in self.root.winfo_children():
    #         widget.destroy()
    #     # Reset widget references before re-creating
    #     self.canvas = None
    #     self.thumbnail_canvas = None
    #     self.thumbnail_frame = None
    #     self.inner_thumbnail_frame = None
    #     self.thumbnail_labels = []
    #     self.thumbnails = []
    #     self.thumbnail_cache = {}

    #     # Re-create all widgets
    #     self.create_widgets()
    #     if self.lock_screen == "yes":
    #         self.Lock_button.configure(fg_color="#d17a24", hover_color="#b56e26")
    #     else:
    #         self.Lock_button.configure(fg_color="#00498f",hover_color="#023261")

    #     # Restore the PDF and page view
    #     if current_pdf and current_page_number is not None:
    #         self.pdf_document = current_pdf
    #         self.current_page = current_page_number

    #         self.render_page(self.current_page)

    #         # Delay thumbnail rendering slightly to ensure canvas is ready
    #         self.root.after(150, self.render_thumbnails)

    #         self.update_page_display()
    #         self.root.after(1000, lambda: self.update_thumbnail_selection(self.current_page))

    #         self.canvas.config(cursor="arrow")
    #         self.canvas.bind("<Motion>", self.on_mouse_hover)
    #         self.page_entry.delete(0, "end")
    #         self.page_entry.insert(0, str(self.current_page + 1))
    #         self.page_total_label.configure(text=f"/ {len(self.pdf_document)}")

    def lock_function(self):

        url = "https://idms-backend.blockchaincloudapps.com/api/v1/folder/lock-unlock"

        payload = json.dumps({
        "doc_id": self.doc_id,
        "user_id": self.user_id 
        })
        headers = {
        'Content-Type': 'application/json'
        }

        response = requests.request("POST", url, headers=headers, data=payload)
        print("redact_api status", response.text, response.status_code)
        if response.status_code == 200 or response.status_code == 201:
            messagebox.showinfo("Success", "Document lock status changed successfully.")
        


    # increase the page size by .2 ever time.
    def zoom_in(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        self.zoom_factor += 0.2
        self.render_page(self.current_page)
    # decrease the page size by .2 ever time.    
    def zoom_out(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
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
        rotation_angle = page.rotation
        page_width, page_height = page.rect.width, page.rect.height

        width_scale = canvas_width / page_width
        height_scale = canvas_height / page_height
        self.zoom_factor = min(width_scale, height_scale)

        self.render_page(self.current_page)
    # to show the page number entered in the entry box
    def go_to_page(self, event=None):
        """Handle manual page entry navigation"""
        try:
            entered_page = self.page_entry.get().strip()
            if not entered_page:
                return
                
            page_number = int(entered_page) - 1  # Convert to zero-based index
            print(f"Manual navigation: entered '{entered_page}', converted to 0-based: {page_number}")  # Debug log
            
            if 0 <= page_number < len(self.pdf_document):
                self.current_page = page_number
                self.render_page(self.current_page)
                self.update_thumbnail_selection(self.current_page)
                self.check_and_update_thumbnail_batch()
                # Note: Don't call update_page_display() here as it would overwrite user input
            else:
                # Reset to current valid page if invalid input
                self.update_page_display()
                messagebox.showerror("Error", f"Invalid page number. Enter a number between 1 and {len(self.pdf_document)}.")
        except ValueError:
            # Reset to current valid page if invalid input
            self.update_page_display()
            messagebox.showerror("Error", "Enter a valid page number.")
    # def go_to_page(self, event=None):
    #     try:
    #         page_number = int(self.page_entry.get()) - 1  # Convert to zero-based index
    #         print(f"Attempting to go to page: {page_number}")  # Debug log
    #         if 0 <= page_number < len(self.pdf_document):
    #             self.current_page = page_number
    #             self.render_page(self.current_page)
    #             self.update_thumbnail_selection(self.current_page)
    #         else:
    #             messagebox.showerror("Error", "Invalid page number.")
    #     except ValueError:
    #         messagebox.showerror("Error", "Enter a valid page number.")

   
    def scroll_to_thumbnail(self, selected_label, page_number):
        """Scroll the thumbnail view to make the selected thumbnail visible."""
        self.inner_thumbnail_frame.update_idletasks()
        y_position = selected_label.winfo_y()

        canvas_height = self.thumbnail_canvas.winfo_height()
        scroll_region = self.thumbnail_canvas.bbox("all")
        if not scroll_region:
            return
        total_height = scroll_region[3] - scroll_region[1]
        if total_height <= 0:
            return
        fraction = y_position / total_height
        half_thumbnail = 75  # Half of thumbnail height
        half_canvas = canvas_height / 2
        offset = (half_canvas - half_thumbnail) / total_height
        fraction = max(0.0, min(1.0, fraction - offset if y_position > 0 else 0))
        self.thumbnail_canvas.yview_moveto(fraction)
        self.last_scroll_position = fraction

        if hasattr(self, '_scroll_reset_job') and self._scroll_reset_job:
            self.root.after_cancel(self._scroll_reset_job)
            self._scroll_reset_job = None
        self._scroll_reset_job = self.root.after(250, lambda: self._ensure_scroll_position(fraction))

    def _ensure_scroll_position(self, target_position):
        """Ensures the thumbnail scroll position stays at the desired location.
        This prevents the scroll from bouncing back to the top after being set."""
        current_position = self.thumbnail_scrollbar.get()[0]  # Get current scroll position
        if abs(current_position - target_position) > 0.05:  # Allow small variations
            self.thumbnail_canvas.yview_moveto(target_position)
            self._scroll_reset_job = self.root.after(200, lambda: self._ensure_scroll_position(target_position))
        else:
            self._scroll_reset_job = None

    # def scroll_to_thumbnail(self, selected_label, page_number):
    #     """Scroll the thumbnail view to make the selected thumbnail visible."""
    #     self.inner_thumbnail_frame.update_idletasks()
    #     y_position = selected_label.winfo_y()

    #     canvas_height = self.thumbnail_canvas.winfo_height()
    #     scroll_region = self.thumbnail_canvas.bbox("all")
    #     if not scroll_region:
    #         return
    #     total_height = scroll_region[3] - scroll_region[1]
    #     if total_height <= 0:
    #         return
    #     fraction = y_position / total_height
    #     half_thumbnail = 75  # Half of thumbnail height
    #     half_canvas = canvas_height / 2
    #     offset = (half_canvas - half_thumbnail) / total_height
    #     # fraction = max(0.0, min(1.0, fraction - offset))
    #     fraction = max(0.0, min(1.0, fraction - offset if y_position > 0 else 0))
    #     self.thumbnail_canvas.yview_moveto(fraction)
    #     self.last_scroll_position = fraction

    #     if hasattr(self, '_scroll_reset_job') and self._scroll_reset_job:
    #         self.root.after_cancel(self._scroll_reset_job)
    #         self._scroll_reset_job = None
    #     self._scroll_reset_job = self.root.after(250, lambda: self._ensure_scroll_position(fraction))
    
    # def _ensure_scroll_position(self, target_position):
    #     """Ensures the thumbnail scroll position stays at the desired location.
    #     This prevents the scroll from bouncing back to the top after being set."""
    #     current_position = self.thumbnail_scrollbar.get()[0]  # Get current scroll position
        
    #     # If the position has changed significantly, reset it to our target
    #     if abs(current_position - target_position) > 0.05:  # Allow small variations
    #         self.thumbnail_canvas.yview_moveto(target_position)
            
    #         # Schedule another check to make sure it sticks
    #         self._scroll_reset_job = self.root.after(200, lambda: self._ensure_scroll_position(target_position))
    #     else:
    #         self._scroll_reset_job = None



    def refresh(self):
        """
        Refreshes the PDF by prompting the user and then retrieving the latest PDF URL from the API.
        Ensures the new URL is fetched only after user confirms to avoid expiration.
        """
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        # Step 1: Ask the user first
        response = messagebox.askyesnocancel(
            "Confirm",
            "Would you like to save the file before refreshing?\nAny unsaved changes will be permanently lost."
        )

        if response is None:
            return  # Cancel

        # Step 2: Call the API *after* the user's decision
        try:
            api_url = f"https://idms-backend.blockchaincloudapps.com/api/v1/folder/pdf-viewer/{self.doc_id}"
            api_response = requests.get(api_url, timeout=10)
            api_response.raise_for_status()
            json_data = api_response.json()
            annotations_path = json_data.get("data", {}).get("annotations_document_path")

            if not annotations_path or annotations_path == "null":
                annotations_path = json_data.get("data", {}).get("folder_path")

            if not annotations_path:
                raise ValueError("Missing annotations_document_path in response.")

            base_url = self.load_pdf_url.split("documents/")[0] + "documents/"
            query_string = self.load_pdf_url.split("?")[1] if "?" in self.load_pdf_url else ""
            new_url = f"{base_url}{annotations_path}?{query_string}" if query_string else f"{base_url}{annotations_path}"

        except (requests.exceptions.RequestException, ValueError, KeyError) as e:
            messagebox.showerror("API Error", f"Failed to fetch updated PDF data:\n{str(e)}")
            print("API Error during refresh:", e)
            return

        # Step 3: Load the new PDF
        try:
            if response:  # User clicked "Yes" – Save first
                self.save_pdf()
            self.load_pdf(new_url, on_complete=None)
        except Exception as e:
            print(f"Error refreshing PDF: {e}")
            messagebox.showerror("Refresh Error", f"Failed to reload PDF:\n{str(e)}")

    # to show the width in perfect width to see all the content as per window width
    def best_width(self):
        """Adjust the zoom level to fit the entire PDF page to the canvas width."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        canvas_width = self.canvas.winfo_width()
        page = self.pdf_document.load_page(self.current_page)
        rotation_angle = page.rotation
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
        rotation_angle = page.rotation
        page_height = page.rect.height

        self.zoom_factor = canvas_height / page_height
        self.render_page(self.current_page)

    def render_page(self, page_number):
        """Render a PDF page to the canvas with the current zoom factor."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.new_file_loaded == "yes":
            self.root.state('zoomed')
            self.new_file_loaded = "no"
        if self.loader_running:
            self.root.after(0, self.hide_loader)
        global pageinfo
        print("self.undo_change_history------------------",self.undo_change_history)
        pageinfo = page_number
        page = self.pdf_document.load_page(page_number)
        # self.update_page_display()
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
        self.root.after(0, self.hide_loader)
        first_page = self.pdf_document[self.current_page]
        if self.file_opened_for_the_first_time == True:
            print("self.very_first_rotation_degree------------------",self.very_first_rotation_degree)
            if self.very_first_rotation_degree == 90 :
                print("90 degree rotation applied")
                first_page.set_rotation((first_page.rotation + 90) % 360)
            elif self.very_first_rotation_degree == 270:
                print("270 degree rotation applied")
                first_page.set_rotation((first_page.rotation + 270) % 360)
            self.file_opened_for_the_first_time = False

        self.page_width_redact, self.page_height_recdact = first_page.rect.width, first_page.rect.height
        print(f"Rendered Page size: width {self.page_width_redact} x hight {self.page_height_recdact}")
        print("self.redact_visible------------------",self.redact_visible)
        print("self.all_page_rectangles-----",self.all_page_rectangles)
        print("self.redact_api_annotations",self.redact_api_annotations)
        print("self.redact_api_rectangles",self.redact_api_rectangles)
        # Initialize redact_visible to True by default (show rectangles by default)
        if not hasattr(self, 'redact_visible'):
            self.redact_visible = True
        
        # Load redaction data if we don't have it yet (first time loading or view_redact is true)
        if not hasattr(self, 'all_page_rectangles') or self.view_redact == "true":
            print("Loading redacted annotations.")
            self.redraw_black_rectangles_from_api()
            self.redact_visible = True
        # Draw rectangles if redact is visible
        if hasattr(self, 'redact_visible') and self.redact_visible:

            self._draw_rectangles_for_current_page()

        if self.rendered_page_count == 0:
            self.root.after(100, self.ensure_best_fit)
            self.rendered_page_count += 1
        # Redraw sticky notes
        print("self.redact_api_rectangles-----------------------------",self.redact_api_rectangles)    
        self.redraw_sticky_notes()
        self.redraw_text_annotations()
        self.redraw_text_with_background()
        self.redraw_polygons()
        self.redraw_all_annotations()
        self.redraw_image_overlays(page_number)
        self.redraw_freehand_drawings()
        self.canvas.config(scrollregion=self.canvas.bbox("all"))
        print("self.duplicate_windows list -",self.duplicate_windows)



    # def redraw_image_overlays(self, page_number):
    #     """Redraw image overlays for the current page with proper scaling and rotation."""
    #     if not hasattr(self, "image_overlays"):
    #         self.image_overlays = []
    #         return
    #     self.canvas.delete("image_overlay")
    #     self.tk_images = {}  # Reset the tk_images dictionary
    #     rotation_angle = 0
    #     if self.pdf_document:
    #         page = self.pdf_document[page_number]
    #         rotation_angle = page.rotation
        
    #     page_width = self.page_width
    #     page_height = self.page_height
    #     current_page_overlays = [overlay for overlay in self.image_overlays if overlay["page"] == page_number]
    #     for overlay in current_page_overlays:
    #         try:
    #             base_x = overlay["base_x"]
    #             base_y = overlay["base_y"]
    #             base_width = overlay["base_width"]
    #             base_height = overlay["base_height"]
    #             scaled_x = base_x * self.zoom_factor
    #             scaled_y = base_y * self.zoom_factor
    #             scaled_width = base_width * self.zoom_factor
    #             scaled_height = base_height * self.zoom_factor
    #             if rotation_angle == 0:
    #                 rotated_x, rotated_y = scaled_x, scaled_y
    #                 display_width, display_height = scaled_width, scaled_height
    #             else:
    #                 center_x_orig = scaled_x + (scaled_width / 2)
    #                 center_y_orig = scaled_y + (scaled_height / 2)
    #                 rotated_center_x, rotated_center_y = self.rotate_point(
    #                     center_x_orig, center_y_orig, 
    #                     page_width, page_height, 
    #                     rotation_angle)
    #                 if rotation_angle in [90, 270]:
    #                     display_width, display_height = scaled_height, scaled_width
    #                 else:
    #                     display_width, display_height = scaled_width, scaled_height
    #                 rotated_x = rotated_center_x - (display_width / 2)
    #                 rotated_y = rotated_center_y - (display_height / 2)
    #             overlay["x"] = rotated_x
    #             overlay["y"] = rotated_y
    #             overlay["width"] = display_width
    #             overlay["height"] = display_height
    #             img = Image.open(overlay["image_path"])
    #             if rotation_angle != 0:
    #                 pil_rotation = {
    #                     90: 270,  # PIL uses counter-clockwise rotation
    #                     180: 180,
    #                     270: 90
    #                 }.get(rotation_angle, 0)
    #                 img = img.rotate(pil_rotation, expand=True)
    #             img = img.resize((int(display_width), int(display_height)), Image.LANCZOS)
    #             tk_img = ImageTk.PhotoImage(img)
    #             self.tk_images[overlay["id"]] = tk_img
    #             canvas_id = self.canvas.create_image(
    #                 rotated_x, rotated_y,
    #                 image=tk_img,
    #                 anchor="nw",
    #                 tags=("image_overlay", overlay["id"]))
    #             overlay["canvas_id"] = canvas_id
                
    #         except Exception as e:
    #             print(f"Failed to redraw image overlay: {e}")

    # def redraw_image_overlays(self, page_number):
    #     """Redraw image overlays for the current page with proper scaling and rotation."""
    #     if not hasattr(self, "image_overlays"):
    #         self.image_overlays = []
    #         return
    #     self.canvas.delete("image_overlay")
    #     self.tk_images = {}  # Reset the tk_images dictionary
        
    #     rotation_angle = 0
    #     if self.pdf_document:
    #         page = self.pdf_document[page_number]
    #         rotation_angle = page.rotation
        
    #     page_width = self.page_width
    #     page_height = self.page_height
        
    #     current_page_overlays = [overlay for overlay in self.image_overlays if overlay["page"] == page_number]
        
    #     for overlay in current_page_overlays:
    #         try:
    #             # Get base coordinates and dimensions (unscaled)
    #             base_x = overlay["base_x"]
    #             base_y = overlay["base_y"]
    #             base_width = overlay["base_width"]
    #             base_height = overlay["base_height"]
                
    #             # Apply zoom scaling
    #             scaled_x = base_x * self.zoom_factor
    #             scaled_y = base_y * self.zoom_factor
    #             scaled_width = base_width * self.zoom_factor
    #             scaled_height = base_height * self.zoom_factor
                
    #             # Apply rotation transformation
    #             # For proper positioning, we need to rotate coordinates based on rotation angle
    #             if rotation_angle == 0:
    #                 rotated_x, rotated_y = scaled_x, scaled_y
    #                 display_width, display_height = scaled_width, scaled_height
    #             else:
    #                 # For rotations, we need to handle the center point of the image
    #                 # Calculate the position from the center of the original image
    #                 center_x_orig = scaled_x + (scaled_width / 2)
    #                 center_y_orig = scaled_y + (scaled_height / 2)
                    
    #                 # Use rotate_point to get the rotated position
    #                 rotated_center_x, rotated_center_y = self.rotate_point(
    #                     center_x_orig, center_y_orig, 
    #                     page_width, page_height, 
    #                     rotation_angle)
                    
    #                 # Swap dimensions for 90° and 270° rotations
    #                 if rotation_angle in [90, 270]:
    #                     display_width, display_height = scaled_height, scaled_width
    #                 else:
    #                     display_width, display_height = scaled_width, scaled_height
                    
    #                 # Calculate the top-left corner from the center point
    #                 rotated_x = rotated_center_x - (display_width / 2)
    #                 rotated_y = rotated_center_y - (display_height / 2)
                
    #             # Update overlay with new coordinates
    #             overlay["x"] = rotated_x
    #             overlay["y"] = rotated_y
    #             overlay["width"] = display_width
    #             overlay["height"] = display_height
                
    #             # Load and prepare the image
    #             img = Image.open(overlay["image_path"])
                
    #             # Rotate the image if needed
    #             if rotation_angle != 0:
    #                 pil_rotation = {
    #                     90: 270,  # PIL uses counter-clockwise rotation
    #                     180: 180,
    #                     270: 90
    #                 }.get(rotation_angle, 0)
    #                 img = img.rotate(pil_rotation, expand=True)
                
    #             # Resize the image
    #             img = img.resize((int(display_width), int(display_height)), Image.LANCZOS)
                
    #             # Convert to Tkinter PhotoImage
    #             tk_img = ImageTk.PhotoImage(img)
    #             self.tk_images[overlay["id"]] = tk_img
                
    #             # Create the image on canvas
    #             canvas_id = self.canvas.create_image(
    #                 rotated_x, rotated_y,
    #                 image=tk_img,
    #                 anchor="nw",
    #                 tags=("image_overlay", overlay["id"]))
                    
    #             overlay["canvas_id"] = canvas_id
                
    #         except Exception as e:
    #             print(f"Failed to redraw image overlay: {e}")

    def redraw_all_annotations(self):
        """Redraw all annotations on the current page with proper rotation"""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation  # Get current page rotation
        # if self.draw_lines_first_time == False:
        #     self.redraw_lines_90(rotation_angle)
        # else:
        #     self.redraw_lines(rotation_angle)
        
        # if self.draw_arrows_first_time == False:
        #     self.redraw_arrows_90(rotation_angle)
        # else:
        #     self.redraw_arrows(rotation_angle)
        self.redraw_lines_90(rotation_angle)
        self.redraw_arrows_90(rotation_angle)
        self.redraw_blackrectangles_90(rotation_angle)
        self.redraw_rectangles_90(rotation_angle)
        self.redraw_apiblackrectangles_90(rotation_angle) 
        self.redraw_ellipses(rotation_angle)

    def redraw_lines(self, rotation_angle=0):
        self.draw_lines_first_time = False
        self.canvas.delete("line")
        current_rotation = self.pdf_document[self.current_page].rotation
        for annotation in self.lines:
            if annotation['page'] == self.current_page:
                canvas_coords = self.pdf_line_to_canvas_coordinates(
                    annotation['x1'], annotation['y1'], 
                    annotation['x2'], annotation['y2'], 
                    current_rotation
                )
       
                line_id = self.canvas.create_line(
                    canvas_coords[0], canvas_coords[1], canvas_coords[2], canvas_coords[3],
                    fill="red", width=4, tags=("annotation", "line"))
                annotation['id'] = line_id
                for ann in self.annotations:
                    if isinstance(ann, dict) and ann.get("type") == "line" and ann.get("page") == self.current_page and ann.get("id") != line_id:
                        ann['id'] = line_id

                self.canvas.tag_bind(line_id, "<Button-1>", self.on_line_press)
                self.canvas.tag_bind(line_id, "<B1-Motion>", self.on_line_drag)
                self.canvas.tag_bind(line_id, "<ButtonRelease-1>", self.on_line_release)

    def redraw_lines_90(self, rotation_angle=0):
        self.canvas.delete("line")
        page_width, page_height = self.page_width, self.page_height
        for annotation in self.lines:
            if annotation['page'] == self.current_page:
                x1 = annotation['x1'] * self.zoom_factor
                y1 = annotation['y1'] * self.zoom_factor
                x2 = annotation['x2'] * self.zoom_factor
                y2 = annotation['y2'] * self.zoom_factor

                if rotation_angle != 0:
                    x1, y1 = self.rotate_point(x1, y1, page_width, page_height, rotation_angle)
                    x2, y2 = self.rotate_point(x2, y2, page_width, page_height, rotation_angle)
                    print("Redrawing line in refresh:", annotation["x1"], annotation["y1"], "to", annotation["x2"], annotation["y2"])

                line_id = self.canvas.create_line(
                    x1, y1, x2, y2,
                    fill="red", width=4, tags=("annotation", "line"))
                annotation['id'] = line_id
                for ann in self.annotations:
                    if isinstance(ann, dict) and ann.get("type") == "line" and ann.get("page") == self.current_page and ann.get("id") != line_id:
                        ann['id'] = line_id

                self.canvas.tag_bind(line_id, "<Button-1>", self.on_line_press)
                self.canvas.tag_bind(line_id, "<B1-Motion>", self.on_line_drag)
                self.canvas.tag_bind(line_id, "<ButtonRelease-1>", self.on_line_release)

    def redraw_arrows(self, rotation_angle=0):
        """Redraw all arrow annotations for the current page with rotation"""
        self.draw_arrows_first_time = False
        self.canvas.delete("arrow")
        current_rotation = self.pdf_document[self.current_page].rotation    

        for annotation in self.arrows:
            if annotation['page'] == self.current_page:
                # Get canvas coordinates
                x1_c, y1_c, x2_c, y2_c = self.pdf_line_to_canvas_coordinates(
                    annotation['x1'], annotation['y1'], 
                    annotation['x2'], annotation['y2'], 
                    current_rotation
                )

                # Determine if we need to swap so the arrow head is at the logical end
                if (annotation['x1'], annotation['y1']) == (annotation['x2'], annotation['y2']):
                    # Skip zero-length arrows
                    continue

                # The "end" is where the arrow head should go
                end_x, end_y = annotation['x2'], annotation['y2']
                start_x, start_y = annotation['x1'], annotation['y1']

                # If drawing direction reversed (optional: you can define your own logic)
                # For example, ensure that the arrow head is where the user finished drawing
                # So if they drew bottom to top, head is at top (x2,y2)

                arrow_coords = (x1_c, y1_c, x2_c, y2_c)

                arrow_id = self.canvas.create_line(
                    arrow_coords[0], arrow_coords[1], arrow_coords[2], arrow_coords[3],
                    fill="red", width=4, arrow=ctk.LAST,
                    arrowshape=(16, 20, 6), tags=("annotation", "arrow")
                )

                # Update annotation ID and bind
                annotation['id'] = arrow_id
                for ann in self.annotations:
                    if isinstance(ann, dict) and ann.get("type") == "arrow" and ann.get("page") == self.current_page:
                        ann['id'] = arrow_id

                self.canvas.tag_bind(arrow_id, "<Button-1>", self.on_line_press)
                self.canvas.tag_bind(arrow_id, "<B1-Motion>", self.on_line_drag)
                self.canvas.tag_bind(arrow_id, "<ButtonRelease-1>", self.on_line_release)

    def redraw_arrows_90(self, rotation_angle=0):
        """Redraw all arrow annotations for the current page with rotation"""
        self.canvas.delete("arrow")
        page_width, page_height = self.page_width, self.page_height
        
        for annotation in self.arrows:
            if annotation['page'] == self.current_page:
                x1 = annotation['x1'] * self.zoom_factor
                y1 = annotation['y1'] * self.zoom_factor
                x2 = annotation['x2'] * self.zoom_factor
                y2 = annotation['y2'] * self.zoom_factor

                if rotation_angle != 0:
                    x1, y1 = self.rotate_point(x1, y1, page_width, page_height, rotation_angle)
                    x2, y2 = self.rotate_point(x2, y2, page_width, page_height, rotation_angle)
                    print("Redrawing arrow in refresh:", annotation["x1"], annotation["y1"], "to", annotation["x2"], annotation["y2"])
  
                arrow_id = self.canvas.create_line(
                    x1, y1, x2, y2,
                    fill="red", width=4, arrow=ctk.LAST, 
                    arrowshape=(16, 20, 6), tags=("annotation", "arrow"))
                
                # Update the ID and bind drag events
                annotation['id'] = arrow_id
                for ann in self.annotations:
                    if isinstance(ann, dict) and ann.get("type") == "arrow" and ann.get("page") == self.current_page and ann.get("id") != arrow_id:
                        ann['id'] = arrow_id
                self.canvas.tag_bind(arrow_id, "<Button-1>", self.on_line_press)
                self.canvas.tag_bind(arrow_id, "<B1-Motion>", self.on_line_drag)
                self.canvas.tag_bind(arrow_id, "<ButtonRelease-1>", self.on_line_release)
    
    def redraw_apiblackrectangles(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation"""
        self.canvas.delete("red_rectangle")
        current_rotation = self.pdf_document[self.current_page].rotation
        print("Current rotation:", current_rotation)
        print("self.rectangles------------------", self.rectangles)
        for annotation in self.redact_api_rectangles:
            print("annotation ------------------", annotation)
            if annotation['page'] == self.current_page:
                print(f"Original PDF coords: {annotation['x1']}, {annotation['y1']}, {annotation['x2']}, {annotation['y2']}")
                
                # The stored coordinates are always in the original (0° rotation) PDF coordinate system
                # Convert them to current canvas coordinates considering the current rotation
                canvas_coords = self.pdf_to_canvas_coordinates(
                    annotation['x1'], annotation['y1'], 
                    annotation['x2'], annotation['y2'], 
                    current_rotation
                )
                
                print(f"Converted canvas coords: {canvas_coords}")

                outline_color = annotation['color']
                fill_color = "" if not annotation['filled'] else annotation['color']
                
                # Draw as polygon instead of rectangle to handle rotation

                self.canvas.create_rectangle(
                    canvas_coords[0], canvas_coords[1], canvas_coords[2], canvas_coords[3],
                    outline=outline_color, fill=fill_color,
                    width=3,tags=("annotation", "apirectangle")
                )
                
    # def redraw_apiblackrectangles_90(self, rotation_angle=0):
    #     """Redraw all rectangle annotations for the current page with rotation"""
    #     self.canvas.delete("apirectangle")
    #     page_width, page_height = self.page_width, self.page_height
        
    #     for annotation in self.redact_api_rectangles:
    #         print("annotation ------------------",annotation)
    #         if annotation['page'] == self.current_page:
    #             # Apply zoom factor to coordinates
    #             x1 = annotation['x1'] * self.zoom_factor
    #             y1 = annotation['y1'] * self.zoom_factor
    #             x2 = annotation['x2'] * self.zoom_factor
    #             y2 = annotation['y2'] * self.zoom_factor
                
    #             # For rectangles, we need to rotate all four corners
    #             corners = [
    #                 (x1, y1),
    #                 (x2, y1),
    #                 (x2, y2),
    #                 (x1, y2)
    #             ]
                
    #             # Rotate each corner
    #             rotated_corners = []
    #             for x, y in corners:
    #                 rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
    #                 rotated_corners.extend([rx, ry])
                
    #             outline_color = annotation['color']
    #             fill_color = "" if not annotation['filled'] else annotation['color']
                
    #             # Draw as polygon instead of rectangle to handle rotation
    #             self.canvas.create_polygon(
    #                 rotated_corners,
    #                 outline=outline_color, fill=fill_color, 
    #                 width=3, tags=("annotation", "apirectangle"))
                
                
    def redraw_blackrectangles(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation"""
        self.canvas.delete("red_rectangle")
        current_rotation = self.pdf_document[self.current_page].rotation
        print("Current rotation:", current_rotation)
        print("self.rectangles------------------", self.rectangles)
        for annotation in self.redact_rectangles:
            print("annotation ------------------", annotation)
            if annotation['page'] == self.current_page:
                print(f"Original PDF coords: {annotation['x1']}, {annotation['y1']}, {annotation['x2']}, {annotation['y2']}")
                
                # The stored coordinates are always in the original (0° rotation) PDF coordinate system
                # Convert them to current canvas coordinates considering the current rotation
                canvas_coords = self.pdf_to_canvas_coordinates(
                    annotation['x1'], annotation['y1'], 
                    annotation['x2'], annotation['y2'], 
                    current_rotation
                )
                
                print(f"Converted canvas coords: {canvas_coords}")

                outline_color = annotation['color']
                fill_color = "" if not annotation['filled'] else annotation['color']
                
                # Draw as polygon instead of rectangle to handle rotation

                self.canvas.create_rectangle(
                    canvas_coords[0], canvas_coords[1], canvas_coords[2], canvas_coords[3],
                    outline=outline_color, fill=fill_color,
                    width=3, tags=("annotation", "rectangle")
                )

    # def redraw_blackrectangles_90(self, rotation_angle=0):
    #     """Redraw all rectangle annotations for the current page with rotation"""
    #     self.canvas.delete("rectangle")
    #     page_width, page_height = self.page_width, self.page_height
        
    #     for annotation in self.redact_rectangles:
    #         print("annotation ------------------",annotation)
    #         if annotation['page'] == self.current_page:
    #             # Apply zoom factor to coordinates
    #             x1 = annotation['x1'] * self.zoom_factor
    #             y1 = annotation['y1'] * self.zoom_factor
    #             x2 = annotation['x2'] * self.zoom_factor
    #             y2 = annotation['y2'] * self.zoom_factor
                
    #             # For rectangles, we need to rotate all four corners
    #             corners = [
    #                 (x1, y1),
    #                 (x2, y1),
    #                 (x2, y2),
    #                 (x1, y2)
    #             ]
                
    #             # Rotate each corner
    #             rotated_corners = []
    #             for x, y in corners:
    #                 rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
    #                 rotated_corners.extend([rx, ry])
                
    #             outline_color = annotation['color']
    #             fill_color = "" if not annotation['filled'] else annotation['color']
                
    #             # Draw as polygon instead of rectangle to handle rotation
    #             self.canvas.create_polygon(
    #                 rotated_corners,
    #                 outline=outline_color, fill=fill_color, 
    #                 width=3, tags=("annotation", "rectangle"))

    def redraw_blackrectangles_90(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation"""
        self.canvas.delete("rectangle")
        page = self.pdf_document[self.current_page]
        rotation = page.rotation  # Use current page rotation directly
        for annotation in self.redact_rectangles:
            if annotation['page'] != self.current_page:
                continue
            pdf_x1 = annotation['x1']
            pdf_y1 = annotation['y1']
            pdf_x2 = annotation['x2']
            pdf_y2 = annotation['y2']
            # Get canvas coords using the consistent transformation (matches refresh)
            canvas_x1, canvas_y1, canvas_x2, canvas_y2 = self.pdf_to_canvas_coordinates(
                pdf_x1, pdf_y1, pdf_x2, pdf_y2, rotation
            )
            # Conditionally apply your essential 2000 offset for alignment (test signs/directions)
            offset = 750 * self.zoom_factor
            if rotation == 90:
                canvas_x1 += offset
                canvas_x2 += offset
                # Or apply to y if needed: canvas_y1 += offset; canvas_y2 += offset
            elif rotation == 270:
                canvas_y1 -= offset
                canvas_y2 -= offset
                # Or change to + if - causes shift: canvas_y1 += offset; canvas_y2 += offset
            outline_color = annotation['color']
            fill_color = annotation['color'] if annotation['filled'] else ""
            tags = ("annotation", "rectangle")
            kwargs = {
                "outline": outline_color,
                "fill": fill_color,
                "width": 4 if not annotation['filled'] else 3,
                "tags": tags
            }
            # Always use rectangle (no polygon needed for 90° multiples)
            rect_id = self.canvas.create_rectangle(
                canvas_x1, canvas_y1, canvas_x2, canvas_y2, **kwargs
            )
            annotation['id'] = rect_id


    def redraw_apiblackrectangles_90(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation"""
        self.canvas.delete("apirectangle")
        page_width, page_height = self.page_width, self.page_height
        page = self.pdf_document[self.current_page]
        rotation = page.rotation  # Use current page rotation directly
        for annotation in self.redact_api_rectangles:
            print("annotation ------------------",annotation)
            if annotation['page'] != self.current_page:
                continue
            pdf_x1 = annotation['x1']
            pdf_y1 = annotation['y1']
            pdf_x2 = annotation['x2']
            pdf_y2 = annotation['y2']
            # Get canvas coords using the consistent transformation (matches refresh)
            canvas_x1, canvas_y1, canvas_x2, canvas_y2 = self.pdf_to_canvas_coordinates(
                pdf_x1, pdf_y1, pdf_x2, pdf_y2, rotation
            )
            # Conditionally apply your essential 2000 offset for alignment (test signs/directions)
            offset = 750 * self.zoom_factor
            if rotation == 90:
                canvas_x1 += offset
                canvas_x2 += offset
                # Or apply to y if needed: canvas_y1 += offset; canvas_y2 += offset
            elif rotation == 270:
                canvas_y1 -= offset
                canvas_y2 -= offset
                # Or change to + if - causes shift: canvas_y1 += offset; canvas_y2 += offset
            outline_color = annotation['color']
            fill_color = annotation['color'] if annotation['filled'] else ""
            tags = ("annotation", "apirectangle")
            kwargs = {
                "outline": outline_color,
                "fill": fill_color,
                "width": 4 if not annotation['filled'] else 3,
                "tags": tags
            }
            # Always use rectangle (no polygon needed for 90° multiples)
            rect_id = self.canvas.create_rectangle(
                canvas_x1, canvas_y1, canvas_x2, canvas_y2, **kwargs
            )
            annotation['id'] = rect_id
                
    def redraw_rectangles_90(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation."""
        self.canvas.delete("red_rectangle")
        page = self.pdf_document[self.current_page]
        rotation = page.rotation  # Use current page rotation directly
        for annotation in self.rectangles:
            if annotation['page'] != self.current_page:
                continue
            pdf_x1 = annotation['x1']
            pdf_y1 = annotation['y1']
            pdf_x2 = annotation['x2']
            pdf_y2 = annotation['y2']
            # Get canvas coords using the consistent transformation (matches refresh)
            canvas_x1, canvas_y1, canvas_x2, canvas_y2 = self.pdf_to_canvas_coordinates(
                pdf_x1, pdf_y1, pdf_x2, pdf_y2, rotation
            )
            # Conditionally apply your essential 2000 offset for alignment (test signs/directions)
            offset = 750 * self.zoom_factor
            if rotation == 90:
                canvas_x1 += offset
                canvas_x2 += offset
                # Or apply to y if needed: canvas_y1 += offset; canvas_y2 += offset
            elif rotation == 270:
                canvas_y1 -= offset
                canvas_y2 -= offset
                # Or change to + if - causes shift: canvas_y1 += offset; canvas_y2 += offset
            outline_color = annotation['color']
            fill_color = annotation['color'] if annotation['filled'] else ""
            use_stipple = annotation['filled'] and annotation['color'] == "yellow"
            tags = ("annotation", "red_rectangle")
            kwargs = {
                "outline": outline_color,
                "fill": fill_color,
                "width": 4 if not annotation['filled'] else 3,
                "tags": tags
            }
            if use_stipple:
                kwargs["stipple"] = "gray25"
            # Always use rectangle (no polygon needed for 90° multiples)
            rect_id = self.canvas.create_rectangle(
                canvas_x1, canvas_y1, canvas_x2, canvas_y2, **kwargs
            )
            annotation['id'] = rect_id
            self.canvas.tag_bind(rect_id, "<Button-1>", self.on_rectangle_press)
            self.canvas.tag_bind(rect_id, "<B1-Motion>", self.on_rectangle_drag)
            self.canvas.tag_bind(rect_id, "<ButtonRelease-1>", self.on_rectangle_release)
                
    # def redraw_rectangles_90(self, rotation_angle=0):
    #     """Redraw all rectangle annotations for the current page with rotation."""
    #     self.canvas.delete("red_rectangle")
    #     page_width, page_height = self.page_width, self.page_height

    #     for annotation in self.rectangles:
    #         if annotation['page'] != self.current_page:
    #             continue

    #         x1 = annotation['x1'] * self.zoom_factor
    #         y1 = annotation['y1'] * self.zoom_factor
    #         x2 = annotation['x2'] * self.zoom_factor
    #         y2 = annotation['y2'] * self.zoom_factor

    #         outline_color = annotation['color']
    #         fill_color = annotation['color'] if annotation['filled'] else ""
    #         use_stipple = annotation['filled'] and annotation['color'] == "yellow"
    #         tags = ("annotation", "red_rectangle")

    #         kwargs = {
    #             "outline": outline_color,
    #             "fill": fill_color,
    #             "width": 4 if not annotation['filled'] else 3,
    #             "tags": tags
    #         }

    #         if use_stipple:
    #             kwargs["stipple"] = "gray25"

    #         if rotation_angle == 0:
    #             rect_id = self.canvas.create_rectangle(x1, y1, x2, y2, **kwargs)
    #         else:
    #             corners = [(x1, y1), (x2, y1), (x2, y2), (x1, y2)]
    #             rotated = []
    #             for x, y in corners:
    #                 rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
    #                 rotated.extend([rx, ry])
    #             rect_id = self.canvas.create_polygon(rotated, **kwargs)

    #         annotation['id'] = rect_id
    #         self.canvas.tag_bind(rect_id, "<Button-1>", self.on_rectangle_press)
    #         self.canvas.tag_bind(rect_id, "<B1-Motion>", self.on_rectangle_drag)
    #         self.canvas.tag_bind(rect_id, "<ButtonRelease-1>", self.on_rectangle_release)


    def redraw_rectangles(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation"""
        self.canvas.delete("red_rectangle")
        current_rotation = self.pdf_document[self.current_page].rotation
        print("Current rotation:", current_rotation)
        print("self.rectangles------------------", self.rectangles)
        
        for annotation in self.rectangles:
            print("annotation ------------------", annotation)
            if annotation['page'] == self.current_page:
                print(f"Original PDF coords: {annotation['x1']}, {annotation['y1']}, {annotation['x2']}, {annotation['y2']}")
                
                # The stored coordinates are always in the original (0° rotation) PDF coordinate system
                # Convert them to current canvas coordinates considering the current rotation
                canvas_coords = self.pdf_to_canvas_coordinates(
                    annotation['x1'], annotation['y1'], 
                    annotation['x2'], annotation['y2'], 
                    current_rotation
                )
                
                print(f"Converted canvas coords: {canvas_coords}")
                
                outline_color = annotation['color']
                fill_color = "" if not annotation['filled'] else annotation['color']
                use_stipple = annotation['filled'] and annotation['color'] == "yellow"
                
                rect_id = self.canvas.create_rectangle(
                    canvas_coords[0], canvas_coords[1], canvas_coords[2], canvas_coords[3],
                    outline=outline_color, fill=fill_color,
                    stipple="gray25" if use_stipple else "",
                    width=4 if not annotation['filled'] else 3,
                    tags=("annotation", "red_rectangle")
                )
                
                annotation['id'] = rect_id
                self.canvas.tag_bind(rect_id, "<Button-1>", self.on_rectangle_press)
                self.canvas.tag_bind(rect_id, "<B1-Motion>", self.on_rectangle_drag)
                self.canvas.tag_bind(rect_id, "<ButtonRelease-1>", self.on_rectangle_release)


    def redraw_ellipses(self, rotation_angle=0):
        """Redraw all ellipse annotations on the current page with correct rotation"""
        self.canvas.delete("ellipse")
        ellipse_annotations = [ann for ann in self.annotations 
                            if isinstance(ann, tuple) and ann[0] == 'ellipse' 
                            and ann[1] is not None]
        print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
        print("ellipse_annotations", ellipse_annotations)
        print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
        for annotation in ellipse_annotations:
            _, x1, y1, x2, y2, old_ellipse_id, mode, numb = annotation
            if numb == self.current_page:    
                # Apply zoom factor to coordinates
                unscaled_x1, unscaled_y1 = x1, y1
                unscaled_x2, unscaled_y2 = x2, y2
                
                # Scale coordinates
                x1 = unscaled_x1 * self.zoom_factor
                y1 = unscaled_y1 * self.zoom_factor
                x2 = unscaled_x2 * self.zoom_factor
                y2 = unscaled_y2 * self.zoom_factor
                
                # Determine the page dimensions at current zoom level
                page_width = self.page_width / self.zoom_factor
                page_height = self.page_height / self.zoom_factor
                
                corners = [
                    (x1, y1),  # Top-left
                    (x2, y1),  # Top-right
                    (x2, y2),  # Bottom-right
                    (x1, y2)   # Bottom-left
                ]
                rotated_corners = []
                for corner_x, corner_y in corners:
                    rx, ry = self.rotate_point(corner_x, corner_y, 
                                            self.page_width, self.page_height, 
                                            rotation_angle)
                    rotated_corners.append((rx, ry))
                rotated_x_coords = [p[0] for p in rotated_corners]
                rotated_y_coords = [p[1] for p in rotated_corners]
                rotated_x1 = min(rotated_x_coords)
                rotated_y1 = min(rotated_y_coords)
                rotated_x2 = max(rotated_x_coords)
                rotated_y2 = max(rotated_y_coords)
                num_points = 72
                points = []
                cx = (x1 + x2) / 2
                cy = (y1 + y2) / 2
                rx = abs(x2 - x1) / 2
                ry = abs(y2 - y1) / 2
                for i in range(num_points):
                    angle = 2 * math.pi * i / num_points
                    point_x = cx + rx * math.cos(angle)
                    point_y = cy + ry * math.sin(angle)
                    rotated_point_x, rotated_point_y = self.rotate_point(
                        point_x, point_y, 
                        self.page_width, self.page_height, 
                        rotation_angle
                    )
                    points.extend([rotated_point_x, rotated_point_y])
                
                fill = "" if mode == "hollow" else "orange"
                new_ellipse_id = self.canvas.create_polygon(
                    points,
                    outline="orange", width=3, fill=fill,
                    smooth=True, tags=("ellipse", "annotation"))
                self.canvas.tag_bind(new_ellipse_id, "<Button-1>", self.on_ellipse_press)
                self.canvas.tag_bind(new_ellipse_id, "<B1-Motion>", self.on_ellipse_drag)
                self.canvas.tag_bind(new_ellipse_id, "<ButtonRelease-1>", self.on_ellipse_release)
                
                # Update annotations list with new ellipse ID
                for i, ann in enumerate(self.annotations):
                    if isinstance(ann, tuple) and ann[0] == 'ellipse' and ann[5] == old_ellipse_id and ann[7] == self.current_page:
                        self.annotations[i] = (ann[0], ann[1], ann[2], ann[3], ann[4], new_ellipse_id, ann[6], ann[7])
                        break
                
                # Update change_history with new ellipse ID
                for j, hist in enumerate(self.change_history):
                    if hist[0] == "add_annotation" and isinstance(hist[1], tuple):
                        if hist[1][0] == "ellipse" and hist[1][5] == old_ellipse_id and hist[1][7] == self.current_page:
                            updated_annotation = (hist[1][0], hist[1][1], hist[1][2], hist[1][3], hist[1][4], new_ellipse_id, hist[1][6], hist[1][7])
                            self.change_history[j] = ("add_annotation", updated_annotation)
                            break
                    elif hist[0] == "move_annotation":
                        # Update both old and new annotations in move_annotation entries
                        old_ann, new_ann = hist[1], hist[2]
                        if isinstance(new_ann, tuple) and new_ann[0] == "ellipse" and new_ann[5] == old_ellipse_id and new_ann[7] == self.current_page:
                            updated_new_ann = (new_ann[0], new_ann[1], new_ann[2], new_ann[3], new_ann[4], new_ellipse_id, new_ann[6], new_ann[7])
                            # Check if old_ann also needs updating (in case of multiple moves)
                            if isinstance(old_ann, tuple) and old_ann[0] == "ellipse" and old_ann[5] == old_ellipse_id and old_ann[7] == self.current_page:
                                updated_old_ann = (old_ann[0], old_ann[1], old_ann[2], old_ann[3], old_ann[4], new_ellipse_id, old_ann[6], old_ann[7])
                                self.change_history[j] = ("move_annotation", updated_old_ann, updated_new_ann)
                            else:
                                self.change_history[j] = ("move_annotation", old_ann, updated_new_ann)
                            break
                
                # Update undo_change_history with new ellipse ID
                for k, undo_hist in enumerate(self.undo_change_history):
                    if undo_hist[0] == "add_annotation" and isinstance(undo_hist[1], tuple):
                        if undo_hist[1][0] == "ellipse" and undo_hist[1][5] == old_ellipse_id and undo_hist[1][7] == self.current_page:
                            updated_annotation = (undo_hist[1][0], undo_hist[1][1], undo_hist[1][2], undo_hist[1][3], undo_hist[1][4], new_ellipse_id, undo_hist[1][6], undo_hist[1][7])
                            self.undo_change_history[k] = ("add_annotation", updated_annotation)
                            break
                    elif undo_hist[0] == "move_annotation":
                        # Update both old and new annotations in move_annotation entries
                        old_ann, new_ann = undo_hist[1], undo_hist[2]
                        if isinstance(new_ann, tuple) and new_ann[0] == "ellipse" and new_ann[5] == old_ellipse_id and new_ann[7] == self.current_page:
                            updated_new_ann = (new_ann[0], new_ann[1], new_ann[2], new_ann[3], new_ann[4], new_ellipse_id, new_ann[6], new_ann[7])
                            # Check if old_ann also needs updating (in case of multiple moves)
                            if isinstance(old_ann, tuple) and old_ann[0] == "ellipse" and old_ann[5] == old_ellipse_id and old_ann[7] == self.current_page:
                                updated_old_ann = (old_ann[0], old_ann[1], old_ann[2], old_ann[3], old_ann[4], new_ellipse_id, old_ann[6], old_ann[7])
                                self.undo_change_history[k] = ("move_annotation", updated_old_ann, updated_new_ann)
                            else:
                                self.undo_change_history[k] = ("move_annotation", old_ann, updated_new_ann)
                            break

    def rotate_point(self, x, y, page_width, page_height, rotation_angle):
        """Rotate a point (x, y) based on the given rotation angle."""
        if rotation_angle == 90:
            if is_small_page == "yes":
                rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y, x
            elif is_small_page == "very small":
                print("buka buka very small")
                rotated_x, rotated_y = self.page_height+(80*self.zoom_factor) - y, x
            elif is_small_page == "smaller":
                print("buka buka smaller")
                rotated_x, rotated_y = self.page_height+(-550*self.zoom_factor) - y, x
            elif is_small_page == "small":
                print("buka buka small")
                rotated_x, rotated_y = self.page_height+(370*self.zoom_factor) - y, x
            elif is_small_page == "slightly":
                rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y, x
            elif is_small_page == "maybe":
                rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y, x
            elif is_small_page == "longer":
                print("rhdttjfykfkyf buka buka")
                rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y, x
            elif is_small_page == "nope large":
                rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y, x
            elif is_small_page == "nope very large":
                rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y, x
            else:
                rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y, x
        elif rotation_angle == 180:
            rotated_x, rotated_y = page_width - x, page_height - y  
        elif rotation_angle == 270:
            if is_small_page == "yes":
                rotated_x, rotated_y = y, self.page_width-(180*self.zoom_factor) - x
            elif is_small_page == "smaller":
                print("buka buka smaller")
                rotated_x, rotated_y = y, self.page_width-(-550*self.zoom_factor) - x
            elif is_small_page == "small":
                print("buka buka small")
                rotated_x, rotated_y = y, self.page_width-(370*self.zoom_factor) - x
            elif is_small_page == "slightly":
                rotated_x, rotated_y =y, self.page_width-(1050*self.zoom_factor) - x
            elif is_small_page == "longer":
                rotated_x, rotated_y = y, self.page_width-(750*self.zoom_factor) - x
            elif is_small_page == "maybe":
                rotated_x, rotated_y = y, self.page_width-(750*self.zoom_factor) - x 
            elif is_small_page == "nope large":
                rotated_x, rotated_y = y, self.page_width-(1000*self.zoom_factor) - x
            elif is_small_page == "nope very large":
                rotated_x, rotated_y = y, self.page_width-(4300*self.zoom_factor) - x
            else:
                rotated_x, rotated_y = y, self.page_width-(2000*self.zoom_factor) - x 
        else:  # 0 degrees
            rotated_x, rotated_y = x, y  
        return rotated_x, rotated_y

    # def redraw_polygons(self):
    #     """Redraw all polygons, adjusting for zoom and rotation properly."""
    #     if not self.pdf_document or self.current_page is None:
    #         return

    #     self.canvas.delete("polygon")
    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation  # Get current page rotation

    #     if self.current_page not in self.page_drawings:
    #         return

    #     page_width, page_height = self.page_width, self.page_height  # Get current page dimensions

    #     for mode, points, polygon_id in self.page_drawings[self.current_page]:
    #         scaled_points = [coord * self.zoom_factor for coord in points]

    #         rotated_points = []
    #         for i in range(0, len(scaled_points), 2):
    #             x, y = scaled_points[i], scaled_points[i + 1]
    #             new_x, new_y = self.rotate_point(x, y, page_width, page_height, rotation_angle)
    #             rotated_points.extend([new_x, new_y])


    #         polygon_id = self.canvas.create_polygon(
    #             rotated_points,
    #             fill="blue" if mode == "filled" else "",
    #             outline="blue" if mode == "filled" else "red",
    #             width=4,
    #             tags=("polygon",),
    #         )

    def on_mouse_scroll(self, event):
        """Handle mouse wheel scrolling for both page navigation and in-page scrolling."""
        # Get canvas dimensions and page dimensions
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        actual_page_width = self.page_width * self.zoom_factor
        actual_page_height = self.page_height * self.zoom_factor
        num_pages = len(self.pdf_document) if self.pdf_document else 0
        delta = int(-1 * (event.delta / 120))  # Scroll direction adjustment
        
        # Get current scroll position
        y_top, y_bottom = self.canvas.yview()
        top_visible = y_top <= 0.01
        bottom_visible = y_bottom >= 0.99
        
        # Check conditions
        at_first_page = self.current_page == 0
        at_last_page = self.current_page == num_pages - 1
        scrolling_up = delta < 0
        scrolling_down = delta > 0
        page_fits_in_canvas = actual_page_height <= canvas_height
        
        # Case 1: Page fits entirely in canvas - only handle page navigation
        if page_fits_in_canvas:
            # When page fits in canvas, only allow page navigation, not scrolling within page
            if scrolling_down and not at_last_page:
                # Go to next page
                self.current_page += 1
                self.render_page(self.current_page)
                self.update_thumbnail_selection(self.current_page)
                self.update_page_display()
                return
            elif scrolling_up and not at_first_page:
                # Go to previous page
                self.current_page -= 1
                self.render_page(self.current_page)
                self.update_thumbnail_selection(self.current_page)
                self.update_page_display()
                return
            # If we're at first page scrolling up or last page scrolling down,
            # don't do anything (prevents unwanted movement)
            return
        
        # Case 2: Page is larger than canvas - allow both scrolling and page navigation
        else:
            # Store the current scroll position before scrolling
            prev_y_top = y_top
            
            # Normal scrolling within the page
            self.canvas.yview_scroll(delta, "units")
            
            # Check if we need to navigate pages after scrolling
            new_y_top, new_y_bottom = self.canvas.yview()
            
            # If scroll position didn't change, it means we hit a boundary
            reached_boundary = (prev_y_top == new_y_top and scrolling_up) or \
                            (new_y_bottom == y_bottom and scrolling_down)
            
            # Handle page navigation at boundaries
            if new_y_bottom >= 0.99 and scrolling_down and not at_last_page:
                # At bottom of page, go to next page
                self.current_page += 1
                self.render_page(self.current_page)
                self.update_thumbnail_selection(self.current_page)
                self.update_page_display()
                self.canvas.yview_moveto(0.0)  # Position at top of new page
            elif new_y_top <= 0.01 and scrolling_up and not at_first_page:
                # At top of page, go to previous page
                self.current_page -= 1
                self.render_page(self.current_page)
                self.update_thumbnail_selection(self.current_page)
                self.update_page_display()
                self.canvas.yview_moveto(1.0)  # Position at bottom of new page
    
    def on_shift_mouse_scroll(self, event):
        """Handles horizontal scrolling when Shift is held."""
        # Calculate actual page width with zoom factor
        actual_page_width = self.page_width * self.zoom_factor
        canvas_width = self.canvas.winfo_width()
        
        # Only allow horizontal scrolling if the page width exceeds the canvas width
        if actual_page_width > canvas_width:
            self.canvas.xview_scroll(-1 * (event.delta // 120), "units")

    # def enable_sticky_note_mode(self):
    #     """Activate sticky note mode."""
    #     self.sticky_note_mode = True
    #     self.highlight_mode = False
    #     # Unbind previous actions and bind the sticky note click action
    #     self.canvas.unbind("<B1-Motion>")
    #     self.canvas.unbind("<ButtonRelease-1>")
    #     self.canvas.bind("<Button-1>", self.on_canvas_click)
    

    # def redraw_sticky_notes(self):
    #     """Redraw sticky notes after rendering the page and adjust for rotation."""
    #     self.canvas.delete("sticky_note")
    #     if not self.pdf_document:
    #         return
            
    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation  # Get current page rotation

    #     for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
    #         if page_num == self.current_page:
    #             x_position = x_scaled * self.zoom_factor
    #             y_position = y_scaled * self.zoom_factor

    #             # Get page dimensions at the current zoom level
    #             page_width = page.rect.width * self.zoom_factor
    #             page_height = page.rect.height * self.zoom_factor

    #             # Adjust coordinates based on rotation
    #             if rotation_angle == 90:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "very small":
    #                     print("buka buka very small")
    #                     rotated_x, rotated_y = self.page_height+(80*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "smaller":
    #                     print("buka buka smaller")
    #                     rotated_x, rotated_y = self.page_height+(-550*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "small":
    #                     print("buka buka small")
    #                     rotated_x, rotated_y = self.page_height+(370*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "slightly":
    #                     rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "longer":
    #                     rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "maybe":
    #                     rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "nope large":
    #                     rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
    #                 elif is_small_page == "nope very large":
    #                     rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
    #                 else:
    #                     rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position
    #             elif rotation_angle == 180:
    #                 rotated_x = page_width - x_position
    #                 rotated_y = page_height - y_position
    #             elif rotation_angle == 270:
    #                 if is_small_page == "yes":
    #                     rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
    #                 elif is_small_page == "very small":
    #                     print("buka buka very small")
    #                     rotated_x, rotated_y = y_position, self.page_width-(80*self.zoom_factor) - x_position
    #                 elif is_small_page == "smaller":
    #                     print("buka buka smaller")
    #                     rotated_x, rotated_y = y_position, self.page_width-(-550*self.zoom_factor) - x_position
    #                 elif is_small_page == "small":
    #                     print("buka buka small")
    #                     rotated_x, rotated_y = y_position, self.page_width-(370*self.zoom_factor) - x_position
    #                 elif is_small_page == "slightly":
    #                     rotated_x, rotated_y =y_position, self.page_width-(1050*self.zoom_factor) - x_position
    #                 elif is_small_page == "longer":
    #                     rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position
    #                 elif is_small_page == "maybe":
    #                     rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
    #                 elif is_small_page == "nope large":
    #                     rotated_x, rotated_y = y_position, self.page_height-(1000*self.zoom_factor)- x_position
    #                 elif is_small_page == "nope very large":
    #                     rotated_x, rotated_y = y_position, self.page_height-(4300*self.zoom_factor)- x_position
    #                 else:
    #                     rotated_x, rotated_y = y_position, self.page_height-(2000*self.zoom_factor) - x_position
           
    #             else:  # 0 degrees
    #                 rotated_x = x_position
    #                 rotated_y = y_position
                    

    #             canvas_id = self.canvas.create_image(
    #                 rotated_x, rotated_y,
    #                 image=self.icons['thumb_pin'],
    #                 anchor="center",
    #                 tags="sticky_note"
    #             )
    #             self.sticky_note_ids[(page_num, x_scaled, y_scaled)] = canvas_id
    #             self.canvas.tag_bind(canvas_id, "<ButtonPress-1>", self.on_sticky_note_press)
    #             self.canvas.tag_bind(canvas_id, "<B1-Motion>", self.on_sticky_note_drag)
    #             self.canvas.tag_bind(canvas_id, "<ButtonRelease-1>", self.on_sticky_note_release)
    #     self.annotation_is_available = True
    #     self.root.update_idletasks()

    # def on_sticky_note_press(self, event):
    #     if not (event.state & 0x0001):
    #         return
    #     self.sticky_note_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
    #     self.dragged_sticky_note = self.canvas.find_withtag("current")[0]

    # def on_sticky_note_drag(self, event):
    #     if self.dragged_sticky_note is not None and self.sticky_note_drag_start:
    #         x_start, y_start = self.sticky_note_drag_start
    #         x_current = self.canvas.canvasx(event.x)
    #         y_current = self.canvas.canvasy(event.y)
    #         dx = x_current - x_start
    #         dy = y_current - y_start
    #         self.canvas.move(self.dragged_sticky_note, dx, dy)
    #         self.sticky_note_drag_start = (x_current, y_current)

    # def on_sticky_note_release(self, event):
    #     if self.dragged_sticky_note is None:
    #         return
    #     new_bbox = self.canvas.bbox(self.dragged_sticky_note)
    #     if not new_bbox:
    #         return
    #     x_center = (new_bbox[0] + new_bbox[2]) / 2
    #     y_center = (new_bbox[1] + new_bbox[3]) / 2
    #     x_scaled = x_center / self.zoom_factor
    #     y_scaled = y_center / self.zoom_factor

    #     # Find the old key (sticky note position) by matching the dragged canvas ID
    #     old_key = None
    #     for key, cid in self.sticky_note_ids.items():
    #         if cid == self.dragged_sticky_note:
    #             old_key = key
    #             break

    #     if old_key:
    #         text = self.sticky_notes.pop(old_key)
    #         self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = text
    #         self.sticky_note_ids.pop(old_key)
    #         self.sticky_note_ids[(self.current_page, x_scaled, y_scaled)] = self.dragged_sticky_note

    #     self.dragged_sticky_note = None
    #     self.sticky_note_drag_start = None

  
    # def on_canvas_click(self, event):
    #     """Add a sticky note at the clicked position on the canvas."""
    #     if not self.pdf_document or not self.sticky_note_mode:
    #         return

    #     x = self.canvas.canvasx(event.x)
    #     y = self.canvas.canvasy(event.y)

    #     if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
    #         return

    #     self.note_text = self.ask_for_note_text(x, y,"Add Sticky Note")
    #     if not self.note_text:
    #         return

    #     x_scaled = x / self.zoom_factor
    #     y_scaled = y / self.zoom_factor

    #     self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = self.note_text

    #     self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, self.note_text))
    #     self.undo_change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, self.note_text))
    #     print("Sticky note added at:", x_scaled, y_scaled)
    #     print("Sticky notes:----",self.change_history)
    #     # Safely retrieve the icon for sticky notes
    #     self.annotation_is_available = True
    #     sticky_icon = self.icons.get("thumb_pin")
    #     if sticky_icon:
    #         # self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
    #         canvas_id = self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
    #         self.sticky_note_ids[(self.current_page, x_scaled, y_scaled)] = canvas_id
    #         self.canvas.tag_bind(canvas_id, "<ButtonPress-1>", self.on_sticky_note_press)
    #         self.canvas.tag_bind(canvas_id, "<B1-Motion>", self.on_sticky_note_drag)
    #         self.canvas.tag_bind(canvas_id, "<ButtonRelease-1>", self.on_sticky_note_release)
    #     else:
    #         print("Warning: 'sticky_note' icon not found.")  # Refresh to apply the changes
    #     self.sticky_note_button.configure(fg_color="#00498f",hover_color="#023261")
    #     self.annotation_listed.append("sticky_note")

    # def ask_for_note_text(self, x, y, title):
    #     """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
    #     dialog = ctk.CTkToplevel(self.root)
    #     dialog.title(title)
    #     dialog.geometry("400x250")
    #     dialog.resizable(False, False)

    #     label = ctk.CTkLabel(
    #         dialog, text="Enter your note:", font=ctk.CTkFont(size=14, weight="bold")
    #     )
    #     label.pack(pady=(15, 10))

    #     text_box = ctk.CTkTextbox(dialog, wrap="word", height=100, width=360)
    #     text_box.pack(padx=15, pady=5, fill="x")

    #     # Set focus after the dialog is fully loaded
    #     dialog.after(100, text_box.focus_set)

    #     note_text_var = ctk.StringVar()

    #     def on_ok_click():
    #         note_text = text_box.get("1.0", "end").strip()
    #         if note_text:
    #             note_text_var.set(note_text)
    #             dialog.destroy()
    #         else:
    #             messagebox.showerror("Empty Note", "You must enter some text to save the sticky note.")

    #     buttons_frame = ctk.CTkFrame(dialog)
    #     buttons_frame.pack(side="bottom", pady=15)

    #     ok_button = ctk.CTkButton(
    #         buttons_frame, text="Apply", command=on_ok_click, fg_color="#00498f", text_color="white"
    #     )
    #     ok_button.pack(side="left", padx=10)

    #     cancel_button = ctk.CTkButton(
    #         buttons_frame, text="Cancel", command=dialog.destroy, fg_color="#6c757d", text_color="white"
    #     )
    #     cancel_button.pack(side="left", padx=10)

    #     dialog.grab_set()
    #     dialog.wait_window()

    #     self.sticky_note_mode = False
    #     self.add_text_mode = False
    #     self.add_text_bg_mode = False
    #     return note_text_var.get() or None


    def enable_sticky_note_mode(self):
        """Activate sticky note mode."""
        self.sticky_note_mode = True
        self.highlight_mode = False
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.canvas.bind("<Button-1>", self.on_canvas_click)

    def redraw_sticky_notes(self):
        """Redraw sticky notes after rendering the page with proper rotation handling."""
        self.canvas.delete("sticky_note")
        if not self.pdf_document:
            return
            
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        page_width = self.page_width
        page_height = self.page_height
        
        for (page_num, x_scaled, y_scaled), note_data in self.sticky_notes.items():
            if page_num == self.current_page:
                # Handle both old string format and new dict format
                if isinstance(note_data, str):
                    note_data = {
                        "text": note_data,
                        "base_x": x_scaled,
                        "base_y": y_scaled,
                        "insertion_rotation": 0  # Default for old notes
                    }
                    self.sticky_notes[(page_num, x_scaled, y_scaled)] = note_data
                
                base_x = note_data.get("base_x", x_scaled)
                base_y = note_data.get("base_y", y_scaled)
                insertion_rotation = note_data.get("insertion_rotation", 0)
                
                # Calculate rotation difference
                rotation_diff = (current_rotation - insertion_rotation) % 360
                
                # Scale to current zoom
                scaled_x = base_x * self.zoom_factor
                scaled_y = base_y * self.zoom_factor
                
                # Apply rotation if needed
                if rotation_diff == 0:
                    display_x = scaled_x
                    display_y = scaled_y
                else:
                    display_x, display_y = self.apply_sticky_note_rotation_to_point(
                        scaled_x, scaled_y, page_width, page_height, rotation_diff, insertion_rotation)
                    
                canvas_id = self.canvas.create_image(
                    display_x, display_y,
                    image=self.icons['thumb_pin'],
                    anchor="center",
                    tags="sticky_note")
                    
                self.sticky_note_ids[(page_num, x_scaled, y_scaled)] = canvas_id
                note_data["canvas_id"] = canvas_id
                
                self.canvas.tag_bind(canvas_id, "<ButtonPress-1>", self.on_sticky_note_press)
                self.canvas.tag_bind(canvas_id, "<B1-Motion>", self.on_sticky_note_drag)
                self.canvas.tag_bind(canvas_id, "<ButtonRelease-1>", self.on_sticky_note_release)
                
        self.annotation_is_available = True
        self.root.update_idletasks()

    def apply_sticky_note_rotation_to_point(self, x, y, page_width, page_height, rotation_angle, insertion_rotation):
        """Apply rotation transformation to text point (similar to image rotation)."""
        if rotation_angle == 0:
            return x, y
        center_x = page_width / 2
        center_y = page_height / 2
        tx = x - center_x
        ty = y - center_y
        if rotation_angle == 90:
            rotated_x = -ty
            rotated_y = tx
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x += (380 * self.zoom_factor)
                rotated_y += (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x += (-380 * self.zoom_factor)
                rotated_y += (-380 * self.zoom_factor)
        elif rotation_angle == 180:
            rotated_x = -tx
            rotated_y = -ty
        elif rotation_angle == 270:
            rotated_x = ty
            rotated_y = -tx
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x -= (380 * self.zoom_factor)
                rotated_y -= (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x -= (-380 * self.zoom_factor)
                rotated_y -= (-380 * self.zoom_factor)
        else:
            rotated_x = tx
            rotated_y = ty
        final_x = rotated_x + center_x
        final_y = rotated_y + center_y
        
        return final_x, final_y

    def on_sticky_note_press(self, event):
        """Store the selected sticky note ID when clicked."""
        if not (event.state & 0x0001):
            return
        self.sticky_note_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
        self.dragged_sticky_note = self.canvas.find_withtag("current")[0]

    def on_sticky_note_drag(self, event):
        """Drag the sticky note."""
        if self.dragged_sticky_note is not None and self.sticky_note_drag_start:
            x_start, y_start = self.sticky_note_drag_start
            x_current = self.canvas.canvasx(event.x)
            y_current = self.canvas.canvasy(event.y)
            dx = x_current - x_start
            dy = y_current - y_start
            self.canvas.move(self.dragged_sticky_note, dx, dy)
            self.sticky_note_drag_start = (x_current, y_current)

    def on_sticky_note_release(self, event):
        """Update sticky note data after dragging."""
        if self.dragged_sticky_note is None:
            return
            
        new_bbox = self.canvas.bbox(self.dragged_sticky_note)
        if not new_bbox:
            return
            
        # Get center position of the dragged sticky note
        x_center = (new_bbox[0] + new_bbox[2]) / 2
        y_center = (new_bbox[1] + new_bbox[3]) / 2
        
        # Convert to PDF coordinates
        new_x_scaled, new_y_scaled = self.canvas_point_to_pdf_coordinates(x_center, y_center)
        
        # Find and update the sticky note data
        old_key = None
        for key, note_data in self.sticky_notes.items():
            if isinstance(note_data, dict) and note_data.get("canvas_id") == self.dragged_sticky_note:
                old_key = key
                break
            elif key in self.sticky_note_ids and self.sticky_note_ids[key] == self.dragged_sticky_note:
                old_key = key
                break
                
        if old_key:
            note_data = self.sticky_notes.pop(old_key)
            
            # Handle both old string format and new dict format
            if isinstance(note_data, str):
                note_data = {
                    "text": note_data,
                    "base_x": new_x_scaled,
                    "base_y": new_y_scaled,
                    "insertion_rotation": self.pdf_document[self.current_page].rotation
                }
            else:
                note_data["base_x"] = new_x_scaled
                note_data["base_y"] = new_y_scaled
                
            # Create new key and update data
            new_key = (self.current_page, new_x_scaled, new_y_scaled)
            self.sticky_notes[new_key] = note_data
            note_data["canvas_id"] = self.dragged_sticky_note
            
            # Update sticky_note_ids
            if old_key in self.sticky_note_ids:
                self.sticky_note_ids.pop(old_key)
            self.sticky_note_ids[new_key] = self.dragged_sticky_note
            
            # Update change history
            for history in [self.change_history, self.undo_change_history]:
                for i, entry in enumerate(history):
                    if (entry[0] == "sticky_note" and entry[1] == old_key[0] and
                        abs(entry[2] - old_key[1]) < 1e-3 and abs(entry[3] - old_key[2]) < 1e-3):
                        history[i] = ("sticky_note", old_key[0], new_x_scaled, new_y_scaled, entry[4])
                        break

        self.dragged_sticky_note = None
        self.sticky_note_drag_start = None

    def on_canvas_click(self, event):
        """Add a sticky note at the clicked position on the canvas."""
        if not self.pdf_document or not self.sticky_note_mode:
            return
            
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        
        # Check boundaries
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return
            
        self.note_text = self.ask_for_note_text(x, y, "Add Sticky Note")
        if not self.note_text:
            return
            
        # Convert to PDF coordinates without rotation compensation
        x_scaled, y_scaled = self.canvas_point_to_pdf_coordinates(x, y)
        
        # Get current page rotation for insertion tracking
        current_rotation = self.pdf_document[self.current_page].rotation
        
        # Create note data with rotation tracking
        note_data = {
            "text": self.note_text,
            "base_x": x_scaled,
            "base_y": y_scaled,
            "insertion_rotation": current_rotation
        }
        
        # Store the sticky note data
        key = (self.current_page, x_scaled, y_scaled)
        self.sticky_notes[key] = note_data
        
        # Add to change history
        self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, self.note_text))
        self.undo_change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, self.note_text))
        
        self.annotation_is_available = True
        
        # Create the visual sticky note
        sticky_icon = self.icons.get("thumb_pin")
        if sticky_icon:
            canvas_id = self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
            self.sticky_note_ids[key] = canvas_id
            note_data["canvas_id"] = canvas_id
            
            self.canvas.tag_bind(canvas_id, "<ButtonPress-1>", self.on_sticky_note_press)
            self.canvas.tag_bind(canvas_id, "<B1-Motion>", self.on_sticky_note_drag)
            self.canvas.tag_bind(canvas_id, "<ButtonRelease-1>", self.on_sticky_note_release)
        else:
            print("Warning: 'thumb_pin' icon not found.")
            
        self.sticky_note_button.configure(fg_color="#00498f", hover_color="#023261")
        self.annotation_listed.append("sticky_note")

    def ask_for_note_text(self, x, y, title):
        """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
        dialog = ctk.CTkToplevel(self.root)
        dialog.title(title)
        dialog.geometry("400x250")
        dialog.resizable(False, False)
        
        label = ctk.CTkLabel(
            dialog, text="Enter your note:", font=ctk.CTkFont(size=14, weight="bold"))
        label.pack(pady=(15, 10))
        
        text_box = ctk.CTkTextbox(dialog, wrap="word", height=100, width=360)
        text_box.pack(padx=15, pady=5, fill="x")
        dialog.after(100, text_box.focus_set)
        
        note_text_var = ctk.StringVar()
        
        def on_ok_click():
            note_text = text_box.get("1.0", "end").strip()
            if note_text:
                note_text_var.set(note_text)
                dialog.destroy()
            else:
                messagebox.showerror("Empty Note", "You must enter some text to save the sticky note.")
        
        buttons_frame = ctk.CTkFrame(dialog)
        buttons_frame.pack(side="bottom", pady=15)
        
        ok_button = ctk.CTkButton(
            buttons_frame, text="Apply", command=on_ok_click, fg_color="#00498f", text_color="white")
        ok_button.pack(side="left", padx=10)
        
        cancel_button = ctk.CTkButton(
            buttons_frame, text="Cancel", command=dialog.destroy, fg_color="#6c757d", text_color="white")
        cancel_button.pack(side="left", padx=10)
        
        dialog.grab_set()
        dialog.wait_window()
        
        # Reset modes after dialog closes
        self.sticky_note_mode = False
        self.add_text_mode = False
        self.add_text_bg_mode = False
        self.sticky_note_button.configure(fg_color="#00498f", hover_color="#023261")
        self.text_button.configure(fg_color="#00498f", hover_color="#023261")
        self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")


        
        return note_text_var.get() or None
    
    def enable_delete_annotation_mode(self):
        """Enable deletion mode for any annotation type."""
        if self.active_deleteannotation:
            self.active_deleteannotation = False
            self.delete_button.configure(fg_color="#00498f",hover_color="#023261")
            self.canvas.unbind("<Button-1>")  # Unbind the delete event
            return
        self.active_deleteannotation = True
        self.deactivate_tools()
        self.delete_button.configure(fg_color="#d17a24",hover_color="#b56e26")
        self.deactivate_colour(self.delete_button,"active_deleteannotation")
        self.canvas.bind("<Button-1>", self.delete_annotation_at_point)
    
    def is_point_inside_ellipse(self, px, py, x1, y1, x2, y2, margin=5):
        cx = (x1 + x2) / 2
        cy = (y1 + y2) / 2
        rx = abs(x2 - x1) / 2 + margin
        ry = abs(y2 - y1) / 2 + margin
        return ((px - cx) ** 2) / (rx ** 2) + ((py - cy) ** 2) / (ry ** 2) <= 1
    
    def point_to_line_distance(self, px, py, x1, y1, x2, y2):
        """Calculate the distance from a point to a line segment."""
        line_length_sq = (x2 - x1) ** 2 + (y2 - y1) ** 2
        
        if line_length_sq == 0:
            return ((px - x1) ** 2 + (py - y1) ** 2) ** 0.5
        
        t = max(0, min(1, ((px - x1) * (x2 - x1) + (py - y1) * (y2 - y1)) / line_length_sq))
        closest_x = x1 + t * (x2 - x1)
        closest_y = y1 + t * (y2 - y1)
        return ((px - closest_x) ** 2 + (py - closest_y) ** 2) ** 0.5

    def delete_annotation_at_point(self, event):
        click_x = self.canvas.canvasx(event.x) / self.zoom_factor
        click_y = self.canvas.canvasy(event.y) / self.zoom_factor
        click_point = fitz.Point(click_x, click_y)
        click_poly = Point(click_x, click_y)
        page = self.pdf_document[self.current_page]
        annot = page.first_annot
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        # Only check polygons on the current page
        if self.current_page in self.polygon_annotations:        
            page = self.pdf_document[self.current_page]
            current_rotation = page.rotation
            polygons_on_page = self.polygon_annotations[self.current_page]
            for idx, polygon_data in enumerate(polygons_on_page):
                display_points = self.get_polygon_display_points(polygon_data)
                if self.is_point_inside_polygon(canvas_x, canvas_y, display_points):
                    # Save to undo history
                    self.undo_change_history.append((
                        "undo", "polygon", self.current_page,
                        polygon_data["base_points"].copy(),
                        polygon_data.get("polygon_id"),
                        polygon_data.get("mode")
                    ))
                    # Remove from annotation list
                    del self.polygon_annotations[self.current_page][idx]
                    self.redraw_polygons()
                    self.render_page(self.current_page) 
        
        # Handle sticky note deletion with proper rotation
        current_rotation = page.rotation
        page_width = self.page_width
        page_height = self.page_height
        
        for (page_num, x_scaled, y_scaled), note_data in list(self.sticky_notes.items()):
            if page_num == self.current_page:
                # Handle both old string format and new dict format
                if isinstance(note_data, str):
                    text = note_data
                    base_x, base_y = x_scaled, y_scaled
                    insertion_rotation = 0
                else:
                    text = note_data["text"]
                    base_x = note_data.get("base_x", x_scaled)
                    base_y = note_data.get("base_y", y_scaled)
                    insertion_rotation = note_data.get("insertion_rotation", 0)
                
                # Calculate display position with rotation
                rotation_diff = (current_rotation - insertion_rotation) % 360
                scaled_x = base_x * self.zoom_factor
                scaled_y = base_y * self.zoom_factor
                
                if rotation_diff == 0:
                    display_x = scaled_x
                    display_y = scaled_y
                else:
                    display_x, display_y = self.apply_sticky_note_rotation_to_point(
                        scaled_x, scaled_y, page_width, page_height, rotation_diff, insertion_rotation)
                
                # Check if click is near the sticky note
                click_distance = ((canvas_x - display_x)**2 + (canvas_y - display_y)**2) ** 0.5
                if click_distance <= 15:  # 15px clickable radius
                    # Add to undo history
                    self.undo_change_history = [
                        entry for entry in self.undo_change_history
                        if not (entry[0] == "undo" and entry[1] == "sticky_note" and entry[2] == self.current_page and
                                abs(entry[3] - x_scaled) < 1e-3 and abs(entry[4] - y_scaled) < 1e-3)
                    ]
                    
                    # Store the complete note data for undo
                    note_text = text if isinstance(note_data, str) else note_data
                    self.undo_change_history.append(("undo", "sticky_note", self.current_page, x_scaled, y_scaled, note_text))
                    
                    # Delete the sticky note
                    del self.sticky_notes[(page_num, x_scaled, y_scaled)]
                    
                    # Remove from sticky_note_ids if exists
                    if (page_num, x_scaled, y_scaled) in self.sticky_note_ids:
                        del self.sticky_note_ids[(page_num, x_scaled, y_scaled)]
                    
                    # Clean up change history
                    self.change_history = [
                        entry for entry in self.change_history
                        if not (entry[0] == "sticky_note" and entry[1] == self.current_page and
                                abs(entry[2] - x_scaled) < 1e-3 and abs(entry[3] - y_scaled) < 1e-3)
                    ]
                    
                    self.render_page(self.current_page)
                    return
        # Handle other annotations
        for entry in reversed(self.change_history):
            action_type = entry[0]
            if action_type == "freehand":
                _, page, line_id, stroke = entry
                bbox = self.canvas.bbox(line_id)
                if bbox and bbox[0] <= click_x * self.zoom_factor <= bbox[2] and bbox[1] <= click_y * self.zoom_factor <= bbox[3]:
                    # Remove any existing matching entry from undo_change_history
                    self.undo_change_history = [
                        undo_entry for undo_entry in self.undo_change_history
                        if not (undo_entry[0] == "undo" and undo_entry[1] == "freehand" and 
                                undo_entry[2] == page and undo_entry[3] == line_id)
                    ]
                    self.undo_change_history.append(("undo","freehand", page, line_id, stroke))
                    self.canvas.delete(line_id)
                    self.change_history.remove(entry)
                    self.render_page(self.current_page)
                    return
            # elif action_type == "add_annotation":
            #     annotation_data = entry[1]
            #     if isinstance(annotation_data, dict):
            #         annotation_type = annotation_data.get("type")
            #         canvas_id = annotation_data.get("id")
            #         if annotation_type in ("rectangle", "line", "arrow"):
            #             x1 = annotation_data.get("x1")
            #             y1 = annotation_data.get("y1")
            #             x2 = annotation_data.get("x2")
            #             y2 = annotation_data.get("y2")  # Fixed: was getting "x2" twice
                        
            #             if x1 is not None and y1 is not None and x2 is not None and y2 is not None:
            #                 # Get current page rotation
            #                 current_rotation = page.rotation
            #                 page_width = page.rect.width
            #                 page_height = page.rect.height
                            
            #                 # Transform PDF coordinates to current rotation's canvas coordinates
            #                 if current_rotation == 0:
            #                     cx1, cy1, cx2, cy2 = x1, y1, x2, y2
            #                 elif current_rotation == 90:
            #                     cx1, cy1 = page_height - y1, x1
            #                     cx2, cy2 = page_height - y2, x2
            #                 elif current_rotation == 180:
            #                     cx1, cy1 = page_width - x1, page_height - y1
            #                     cx2, cy2 = page_width - x2, page_height - y2
            #                 elif current_rotation == 270:
            #                     cx1, cy1 = y1, page_width - x1
            #                     cx2, cy2 = y2, page_width - x2
                            
            #                 # Scale to canvas coordinates
            #                 canvas_x1 = cx1 * self.zoom_factor
            #                 canvas_y1 = cy1 * self.zoom_factor
            #                 canvas_x2 = cx2 * self.zoom_factor
            #                 canvas_y2 = cy2 * self.zoom_factor
                            
            #                 # Get the bounding box
            #                 min_x = min(canvas_x1, canvas_x2)
            #                 max_x = max(canvas_x1, canvas_x2)
            #                 min_y = min(canvas_y1, canvas_y2)
            #                 max_y = max(canvas_y1, canvas_y2)
                            
            #                 # Use the raw canvas coordinates for comparison
            #                 click_canvas_x = self.canvas.canvasx(event.x)
            #                 click_canvas_y = self.canvas.canvasy(event.y)
                            
            #                 # Check if click is within the annotation bounds
            #                 if min_x <= click_canvas_x <= max_x and min_y <= click_canvas_y <= max_y:
            #                     # Remove from undo history to avoid duplicates
            #                     self.undo_change_history = [
            #                         undo_entry for undo_entry in self.undo_change_history
            #                         if not (undo_entry[0] == "undo" and undo_entry[1] == 'add_annotation' and 
            #                                 isinstance(undo_entry[2], dict) and undo_entry[2].get('id') == canvas_id)]
                                
            #                     # Add to undo history
            #                     self.undo_change_history.append(("undo", 'add_annotation', annotation_data))
                                
            #                     # Delete from canvas
            #                     if canvas_id:
            #                         self.canvas.delete(canvas_id)
                                
            #                     # Remove from appropriate list
            #                     if annotation_type == "rectangle":
            #                         self.rectangles = [rect for rect in self.rectangles if rect != annotation_data]
            #                     elif annotation_type == "line":
            #                         self.lines = [line for line in self.lines if line != annotation_data]
            #                     elif annotation_type == "arrow":
            #                         self.arrows = [arrow for arrow in self.arrows if arrow != annotation_data]
                                
            #                     # Remove from annotations list
            #                     self.annotations = [ann for ann in self.annotations if not (isinstance(ann, dict) and ann.get('id') == canvas_id)]
                                
            #                     # Remove from change history
            #                     self.change_history.remove(entry)
            #                     self.render_page(self.current_page)
            #                     return
            #         print("found for deletion.",self.change_history)


            elif action_type == "add_annotation":
                annotation_data = entry[1]
                if isinstance(annotation_data, dict):
                    annotation_type = annotation_data.get("type")
                    canvas_id = annotation_data.get("id")
                    if annotation_type in ("rectangle", "line", "arrow"):
                        x1 = annotation_data.get("x1")
                        y1 = annotation_data.get("y1")
                        x2 = annotation_data.get("x2")
                        y2 = annotation_data.get("y2")
                        
                        if x1 is not None and y1 is not None and x2 is not None and y2 is not None:
                            current_rotation = page.rotation
                            stored_rotation = annotation_data.get('rotation_when_created', 0)
                            canvas_coords = self.pdf_to_canvas_coordinates(x1, y1, x2, y2, current_rotation)
                            canvas_x1, canvas_y1, canvas_x2, canvas_y2 = canvas_coords
                            offset = 750 * self.zoom_factor
                            if current_rotation == 90:
                                canvas_x1 += offset
                                canvas_x2 += offset
                            elif current_rotation == 270:
                                canvas_y1 -= offset
                                canvas_y2 -= offset
                            min_x = min(canvas_x1, canvas_x2)
                            max_x = max(canvas_x1, canvas_x2)
                            min_y = min(canvas_y1, canvas_y2)
                            max_y = max(canvas_y1, canvas_y2)
                            tolerance = 5
                            min_x -= tolerance
                            max_x += tolerance
                            min_y -= tolerance
                            max_y += tolerance
                            
                            click_canvas_x = self.canvas.canvasx(event.x)
                            click_canvas_y = self.canvas.canvasy(event.y)
                            if min_x <= click_canvas_x <= max_x and min_y <= click_canvas_y <= max_y:
                                if annotation_type in ("line", "arrow"):
                                    dist = self.point_to_line_distance(
                                        click_canvas_x, click_canvas_y,
                                        canvas_x1, canvas_y1, canvas_x2, canvas_y2
                                    )
                                    if dist > 10:  # 10 pixel tolerance for lines
                                        continue
                                self.undo_change_history = [
                                    undo_entry for undo_entry in self.undo_change_history
                                    if not (undo_entry[0] == "undo" and undo_entry[1] == 'add_annotation' and 
                                            isinstance(undo_entry[2], dict) and undo_entry[2].get('id') == canvas_id)]
                                self.undo_change_history.append(("undo", 'add_annotation', annotation_data))
                                if canvas_id:
                                    self.canvas.delete(canvas_id)
                                if annotation_type == "rectangle":
                                    self.rectangles = [rect for rect in self.rectangles if rect != annotation_data]
                                elif annotation_type == "line":
                                    self.lines = [line for line in self.lines if line != annotation_data]
                                elif annotation_type == "arrow":
                                    self.arrows = [arrow for arrow in self.arrows if arrow != annotation_data]
                                self.annotations = [ann for ann in self.annotations if not (isinstance(ann, dict) and ann.get('id') == canvas_id)]
                                self.change_history.remove(entry)
                                self.render_page(self.current_page)
                                return
                elif isinstance(annotation_data, tuple) and annotation_data[0] == "ellipse":
                    _, x1, y1, x2, y2, ellipse_id, mode, page = annotation_data
                    if page != self.current_page:
                        continue
                    overlapping_items = self.canvas.find_overlapping(event.x, event.y, event.x, event.y)
                    if ellipse_id in overlapping_items:
                        # Remove any existing matching entry from undo_change_history
                        self.undo_change_history = [
                            undo_entry for undo_entry in self.undo_change_history
                            if not (undo_entry[0] == "undo" and undo_entry[1] == "add_annotation" and 
                                    isinstance(undo_entry[2], tuple) and undo_entry[2][0] == "ellipse" and
                                    undo_entry[2][5] == ellipse_id)
                        ]
                        self.undo_change_history.append(("undo", "add_annotation", annotation_data))
                        self.canvas.delete(ellipse_id)
                        self.annotations = [
                            ann for ann in self.annotations
                            if not (isinstance(ann, tuple) and ann[0] == "ellipse" and ann[5] == ellipse_id)]
                        if self.annotation_listed and self.annotation_listed[-1] == "ellipse":
                            self.annotation_listed.pop()
                        self.change_history.remove(entry)
                        self.render_page(self.current_page)
                        return
            elif action_type == "move_annotation":
                old_ann, new_ann = entry[1], entry[2]
                if isinstance(new_ann, tuple) and new_ann[0] == "ellipse":
                    _, x1, y1, x2, y2, ellipse_id, mode, page = new_ann
                    if page != self.current_page:
                        continue

                    overlapping_items = self.canvas.find_overlapping(event.x, event.y, event.x, event.y)
                    if ellipse_id in overlapping_items:
                        # Remove any existing matching entry from undo_change_history
                        self.undo_change_history = [
                            undo_entry for undo_entry in self.undo_change_history
                            if not (undo_entry[0] == "undo" and undo_entry[1] == "move_annotation" and 
                                    isinstance(undo_entry[3], tuple) and undo_entry[3][0] == "ellipse" and
                                    undo_entry[3][5] == ellipse_id)
                        ]
                        self.undo_change_history.append(("undo", "move_annotation", old_ann, new_ann))
                        self.canvas.delete(ellipse_id)
                        self.annotations = [
                            ann for ann in self.annotations
                            if not (isinstance(ann, tuple) and ann[0] == "ellipse" and ann[5] == ellipse_id)]
                        if self.annotation_listed and self.annotation_listed[-1] == "ellipse":
                            self.annotation_listed.pop()
                        self.change_history.remove(entry)
                        self.render_page(self.current_page)
                        return
            elif action_type == "image_overlay":
                _, page_no, overlay_info = entry
                if page_no == self.current_page and "canvas_id" in overlay_info:
                    coords = self.canvas.bbox(overlay_info["canvas_id"])
                    if coords and coords[0] <= click_x * self.zoom_factor <= coords[2] and coords[1] <= click_y * self.zoom_factor <= coords[3]:
                        # Remove any existing matching entry from undo_change_history
                        self.undo_change_history = [
                            undo_entry for undo_entry in self.undo_change_history
                            if not (undo_entry[0] == "undo" and undo_entry[1] == "image_overlay" and 
                                    undo_entry[2] == page_no and undo_entry[3].get("id") == overlay_info["id"])
                        ]
                        self.undo_change_history.append(("undo","image_overlay", page_no, overlay_info))
                        self.canvas.delete(overlay_info["canvas_id"])
                        if hasattr(self, "tk_images") and overlay_info["id"] in self.tk_images:
                            del self.tk_images[overlay_info["id"]]
                        self.image_overlays = [i for i in self.image_overlays if i["id"] != overlay_info["id"]]
                        self.change_history.remove(entry)
                        self.render_page(self.current_page)
                        return
            elif action_type in ("add_text", "add_text_bg"):
                _, page_num, x_scaled, y_scaled, text = entry
                if page_num == self.current_page:
                    annotation_dict = self.text_annotations if action_type == "add_text" else self.text_annotations_bg
                    found_key = None
                    deleted_annotation_data = None
                    
                    for key, annotation_entry in annotation_dict.items():
                        if key[0] != page_num:
                            continue
                        if isinstance(annotation_entry, dict) and "bbox" in annotation_entry:
                            x1, y1, x2, y2 = annotation_entry["bbox"]
                            if x1 <= click_x * self.zoom_factor <= x2 and y1 <= click_y * self.zoom_factor <= y2:
                                canvas_id = annotation_entry.get("canvas_id")
                                if canvas_id:
                                    self.canvas.delete(canvas_id)
                                found_key = key
                                deleted_annotation_data = annotation_entry.copy()
                                break
                    
                    if found_key:
                        # Clean up any existing undo entries for this specific annotation
                        self.undo_change_history = [
                            undo_entry for undo_entry in self.undo_change_history
                            if not (undo_entry[0] == "undo" and undo_entry[1] == action_type and 
                                    undo_entry[2] == page_num and 
                                    abs(undo_entry[3] - found_key[1]) < 1e-3 and 
                                    abs(undo_entry[4] - found_key[2]) < 1e-3)
                        ]
                        
                        # Add undo entry with the exact coordinates from found_key
                        self.undo_change_history.append(("undo", action_type, page_num, found_key[1], found_key[2], deleted_annotation_data))
                        
                        # Remove from annotation dictionary
                        del annotation_dict[found_key]
                        
                        # Remove the corresponding entry from change_history using the EXACT coordinates from found_key
                        self.change_history = [
                            h_entry for h_entry in self.change_history
                            if not (h_entry[0] == action_type and h_entry[1] == page_num and
                                    abs(h_entry[2] - found_key[1]) < 1e-3 and 
                                    abs(h_entry[3] - found_key[2]) < 1e-3)
                        ]
                        
                        self.render_page(self.current_page)
                        return
            # elif action_type in ("add_text", "add_text_bg"):
            #     _, page, x_scaled, y_scaled, text = entry
            #     if page == self.current_page:
            #         annotation_dict = self.text_annotations if action_type == "add_text" else self.text_annotations_bg
            #         found_key = None
            #         deleted_annotation_data = None  # Store the complete annotation data
                    
            #         for key, annotation_entry in annotation_dict.items():
            #             if key[0] != page:
            #                 continue
            #             if isinstance(annotation_entry, dict) and "bbox" in annotation_entry:
            #                 x1, y1, x2, y2 = annotation_entry["bbox"]
            #                 if x1 <= click_x * self.zoom_factor <= x2 and y1 <= click_y * self.zoom_factor <= y2:
            #                     canvas_id = annotation_entry.get("canvas_id")
            #                     if canvas_id:
            #                         self.canvas.delete(canvas_id)
            #                     found_key = key
            #                     deleted_annotation_data = annotation_entry.copy()  # Store complete data
            #                     break
                    
            #         if found_key:
            #             self.undo_change_history = [
            #                 undo_entry for undo_entry in self.undo_change_history
            #                 if not (undo_entry[0] == "undo" and undo_entry[1] == action_type and 
            #                         undo_entry[2] == page and abs(undo_entry[3] - found_key[1]) < 1e-3 and 
            #                         abs(undo_entry[4] - found_key[2]) < 1e-3)
            #             ]
            #             # Store complete annotation data instead of just text
            #             self.undo_change_history.append(("undo", action_type, page, x_scaled, y_scaled, deleted_annotation_data))
            #             del annotation_dict[found_key]
                        
            #             for h_entry in self.change_history:
            #                 if (h_entry[0] == action_type and h_entry[1] == page and
            #                     abs(h_entry[2] - found_key[1]) < 1e-3 and abs(h_entry[3] - found_key[2]) < 1e-3):
            #                     self.change_history.remove(h_entry)
            #                     break
            #             self.render_page(self.current_page)
            #             return
                    

    def undo_change(self):
        print("Undoing the last change...",self.undo_change_history)
        print("change history before undoing", self.change_history)
        if not self.undo_change_history:
            return

        last_action = self.undo_change_history.pop()
        action_type = last_action[0]
        print("all the list of rect",self.rectangles)
        print("all the list of lines",self.lines)
        print("all the list of arrows",self.arrows)
        
        if action_type == "undo":
            check_action = last_action[1]  # Skip the "undo" prefix
            if check_action == "sticky_note":
                _, _, page, x_scaled, y_scaled, text_note = last_action
                self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = text_note
                self.change_history.append(("sticky_note", page, x_scaled, y_scaled, text_note))
                self.undo_change_history.append(("sticky_note", page, x_scaled, y_scaled, text_note))
                self.render_page(self.current_page)
            
            elif check_action == "freehand":
                _,_, page, line_id, stroke = last_action
                # Redraw the freehand line
                self.freehand_drawings.append((page, line_id, stroke))
                self.change_history.append(("freehand", page, line_id, stroke))
                self.undo_change_history.append(("freehand", page, line_id, stroke))
                self.render_page(self.current_page)

            elif check_action == "polygon":
                _, _, page, base_points, polygon_id, mode = last_action
                if page not in self.polygon_annotations:
                    self.polygon_annotations[page] = []
                self.polygon_annotations[page].append({
                    "mode": mode,
                    "points": base_points.copy(),
                    "base_points": base_points.copy(),
                    "insertion_rotation": self.pdf_document[page].rotation,
                    "polygon_id": polygon_id
                })
                self.redraw_polygons()
                self.change_history.append(("polygon",page, base_points, polygon_id))
                self.undo_change_history.append(("polygon",page, base_points, polygon_id))
                
            
            elif check_action == "image_overlay":
                _, _, page, overlay_info = last_action
                self.image_overlays.append(overlay_info)
                self.change_history.append(("image_overlay", page, overlay_info))
                self.undo_change_history.append(("image_overlay", page, overlay_info)) 
                self.render_page(self.current_page)

            elif check_action == "add_annotation":
                annotation_data = last_action[2]
                
                if isinstance(annotation_data, dict):
                    annotation_type = annotation_data.get('type')
                    canvas_id = annotation_data.get('id')
                    
                    if annotation_type == 'line':
                        self.lines.append(annotation_data)
                        self.annotation_listed.append('line')
                    elif annotation_type == 'arrow':
                        self.arrows.append(annotation_data)
                        self.annotation_listed.append('arrow')
                    elif annotation_type == 'rectangle':
                        self.rectangles.append(annotation_data)
                        self.annotation_listed.append('rectangle')
                    
                    self.annotations.append(annotation_data)
                    if canvas_id:
                        # Recreate if needed, or skip if you re-render
                        pass
                    self.change_history.append(("add_annotation", annotation_data))
                    self.undo_change_history.append(("add_annotation", annotation_data))

                elif isinstance(annotation_data, tuple) and annotation_data[0] == "ellipse":
                    # Ellipse undo
                    _, x1, y1, x2, y2, old_id, mode, page = annotation_data
                    fill = "" if mode == "hollow" else "orange"
                    ellipse_id_new = self.canvas.create_oval(
                        x1 * self.zoom_factor, y1 * self.zoom_factor,
                        x2 * self.zoom_factor, y2 * self.zoom_factor,
                        outline="orange",
                        fill=fill,
                        width=4 if mode == "hollow" else 3,
                        tags=("annotation", "ellipse")
                    )
                    # Add to lists
                    new_tuple = ("ellipse", x1, y1, x2, y2, ellipse_id_new, mode, page)
                    self.annotations.append(new_tuple)
                    self.change_history.append(("add_annotation", new_tuple))
                    self.undo_change_history.append(("add_annotation", new_tuple))
                    self.annotation_listed.append("ellipse")

                    # Bind drag
                    self.canvas.tag_bind(ellipse_id_new, "<Button-1>", self.on_ellipse_press)
                    self.canvas.tag_bind(ellipse_id_new, "<B1-Motion>", self.on_ellipse_drag)
                    self.canvas.tag_bind(ellipse_id_new, "<ButtonRelease-1>", self.on_ellipse_release)

                self.render_page(self.current_page)
            
            elif check_action == "move_annotation":
                _, _, old_ann, new_ann = last_action
                if isinstance(new_ann, tuple) and new_ann[0] == "ellipse":
                    _, x1, y1, x2, y2, _, mode, page = new_ann
                    fill = "" if mode == "hollow" else "orange"
                    ellipse_id_new = self.canvas.create_oval(
                        x1 * self.zoom_factor, y1 * self.zoom_factor,
                        x2 * self.zoom_factor, y2 * self.zoom_factor,
                        outline="orange",
                        fill=fill,
                        width=4 if mode == "hollow" else 3,
                        tags=("annotation", "ellipse")
                    )
                    moved_tuple = ("ellipse", x1, y1, x2, y2, ellipse_id_new, mode, page)
                    self.annotations.append(moved_tuple)
                    self.change_history.append(("move_annotation", old_ann, moved_tuple))
                    self.undo_change_history.append(("add_annotation", moved_tuple))
                    self.annotation_listed.append("ellipse")

                    self.canvas.tag_bind(ellipse_id_new, "<Button-1>", self.on_ellipse_press)
                    self.canvas.tag_bind(ellipse_id_new, "<B1-Motion>", self.on_ellipse_drag)
                    self.canvas.tag_bind(ellipse_id_new, "<ButtonRelease-1>", self.on_ellipse_release)

                    self.render_page(self.current_page)


            # elif check_action == "add_text":
            #     _, _, page, x_scaled, y_scaled, annotation_data = last_action
                
            #     # Restore complete annotation data structure
            #     if isinstance(annotation_data, dict):
            #         # Complete annotation data with rotation info
            #         self.text_annotations[(page, x_scaled, y_scaled)] = annotation_data
            #     else:
            #         # Fallback for old format (just text string)
            #         # Get current page rotation for proper restoration
            #         page_obj = self.pdf_document[page] if self.pdf_document else None
            #         current_rotation = page_obj.rotation if page_obj else 0
                    
            #         self.text_annotations[(page, x_scaled, y_scaled)] = {
            #             "text": annotation_data,
            #             "font_size": 16,
            #             "max_width": page_obj.rect.width * 0.4 if page_obj else 400,
            #             "base_x": x_scaled,
            #             "base_y": y_scaled,
            #             "insertion_rotation": current_rotation
            #         }
                
            #     # Update change history with text content for consistency
            #     text_content = annotation_data.get("text", annotation_data) if isinstance(annotation_data, dict) else annotation_data
            #     self.change_history.append(("add_text", page, x_scaled, y_scaled, text_content))
            #     self.undo_change_history.append(("add_text", page, x_scaled, y_scaled, text_content))
            #     self.render_page(self.current_page)

            # elif check_action == "add_text_bg":
            #     _, _, page, x_scaled, y_scaled, annotation_data = last_action
                
            #     # Restore complete annotation data structure for background text
            #     if isinstance(annotation_data, dict):
            #         # Complete annotation data with rotation info
            #         self.text_annotations_bg[(page, x_scaled, y_scaled)] = annotation_data
            #     else:
            #         # Fallback for old format (just text string)
            #         # Get current page rotation for proper restoration
            #         page_obj = self.pdf_document[page] if self.pdf_document else None
            #         current_rotation = page_obj.rotation if page_obj else 0
                    
            #         self.text_annotations_bg[(page, x_scaled, y_scaled)] = {
            #             "text": annotation_data,
            #             "font_size": 16,
            #             "max_width": page_obj.rect.width * 0.4 if page_obj else 400,
            #             "base_x": x_scaled,
            #             "base_y": y_scaled,
            #             "insertion_rotation": current_rotation
            #         }
                
            #     # Update change history with text content for consistency
            #     text_content = annotation_data.get("text", annotation_data) if isinstance(annotation_data, dict) else annotation_data
            #     self.change_history.append(("add_text_bg", page, x_scaled, y_scaled, text_content))        
            #     self.undo_change_history.append(("add_text_bg", page, x_scaled, y_scaled, text_content))
            #     self.render_page(self.current_page)

            elif check_action == "add_text":
                _, _, page, x_scaled, y_scaled, annotation_data = last_action
                self.text_annotations[(page, x_scaled, y_scaled)] = annotation_data
                text_content = annotation_data.get("text", annotation_data) if isinstance(annotation_data, dict) else annotation_data
                self.change_history.append(("add_text", page, x_scaled, y_scaled, text_content))
                self.render_page(self.current_page)

            elif check_action == "add_text_bg":
                _, _, page, x_scaled, y_scaled, annotation_data = last_action
                self.text_annotations_bg[(page, x_scaled, y_scaled)] = annotation_data
                text_content = annotation_data.get("text", annotation_data) if isinstance(annotation_data, dict) else annotation_data
                self.change_history.append(("add_text_bg", page, x_scaled, y_scaled, text_content))        
                self.render_page(self.current_page)
                        
        elif action_type == "freehand":
            _, page, line_id, stroke = last_action
            bbox = self.canvas.bbox(line_id)
            if bbox:
                self.canvas.delete(line_id)

            # Remove from change and freehand lists
            for entry in self.change_history:
                if entry[0] == "freehand" and entry[1] == page and entry[2] == line_id:
                    self.change_history.remove(entry)
                    break

            self.freehand_drawings = [
                drawing for drawing in self.freehand_drawings
                if not (drawing[0] == page and drawing[1] == line_id)
            ]

            if self.annotation_listed and self.annotation_listed[-1] == "freehand":
                self.annotation_listed.pop()

            self.render_page(self.current_page)
            return
        
        elif action_type == "move_annotation":
            old_annotation = last_action[1]
            updated_annotation = last_action[2]
            print("in move annotation all the list of rect",self.rectangles)
            print("in move annotation all annotation list",self.annotations)
            print("in move annotation undo_change history",self.undo_change_history)

            if isinstance(old_annotation, dict):
                annotation_type = old_annotation.get("type")
                original_x1 = updated_annotation["x1"]
                original_y1 = updated_annotation["y1"]

                # Search in self.annotations for matching x1, y1
                matched_ann = None
                for ann in self.annotations:
                    if (
                        isinstance(ann, dict)
                        and ann.get("x1") == original_x1
                        and ann.get("y1") == original_y1
                        and ann.get("type") == annotation_type
                    ):
                        matched_ann = ann
                        break

                if matched_ann:
                    matched_id = matched_ann.get("id")
                    self.canvas.delete(matched_id)

                    # Remove from annotations
                    self.annotations = [ann for ann in self.annotations if ann.get("id") != matched_id]

                    # Remove from the specific type list
                    if annotation_type == 'line':
                        self.lines = [l for l in self.lines if l.get("id") != matched_id]
                    elif annotation_type == 'arrow':
                        self.arrows = [a for a in self.arrows if a.get("id") != matched_id]
                    elif annotation_type == 'rectangle':
                        self.rectangles = [r for r in self.rectangles if r.get("id") != matched_id]

                    if self.annotation_listed and self.annotation_listed[-1] == annotation_type:
                        self.annotation_listed.pop()
                    
                    self.undo_change_history = [
                        entry for entry in self.undo_change_history
                        if not (
                            entry[0] == "add_annotation" and
                            isinstance(entry[1], dict) and
                            entry[1].get("type") == annotation_type and
                            entry[1].get("page") == matched_ann.get("page") and
                            (
                                # For moved annotations, check if this was the original add entry
                                (entry[1].get("x1") == old_annotation.get("x1") and
                                entry[1].get("y1") == old_annotation.get("y1")) or
                                # Or if it matches the current position before undo
                                (entry[1].get("x1") == original_x1 and
                                entry[1].get("y1") == original_y1)
                            )
                        )
                    ]

                    self.render_page(self.current_page)
            
                print("after move annotation all the list of rect",self.rectangles)
                print("after move annotation all annotation list",self.annotations)
                print("after move annotation undo_change history",self.undo_change_history)

            elif isinstance(old_annotation, tuple) and old_annotation[0] == "ellipse":
                canvas_id = old_annotation[5]
                x1 = old_annotation[1] * self.zoom_factor
                y1 = old_annotation[2] * self.zoom_factor
                x2 = old_annotation[3] * self.zoom_factor
                y2 = old_annotation[4] * self.zoom_factor
                self.canvas.coords(canvas_id, x1, y1, x2, y2)
                for i, ann in enumerate(self.annotations):
                    if isinstance(ann, tuple) and ann[0] == "ellipse" and ann[5] == canvas_id:
                        self.annotations[i] = old_annotation
                        break


            print("Undo action completed. Remaining history:", self.undo_change_history)
        
        elif action_type == "add_annotation":
            annotation_data = last_action[1]

            if isinstance(annotation_data, dict):
                # Existing handling for dict-based annotations (line, arrow, rectangle)
                annotation_type = annotation_data.get('type')
                canvas_id = annotation_data.get('id')

                if canvas_id:
                    self.canvas.delete(canvas_id)
                    self.render_page(self.current_page)

                if annotation_type == 'line':
                    self.lines = [line for line in self.lines if line != annotation_data]
                    if self.annotation_listed and self.annotation_listed[-1] == "line":
                        self.annotation_listed.pop()
                        self.render_page(self.current_page)

                elif annotation_type == 'arrow':
                    self.arrows = [arrow for arrow in self.arrows if arrow != annotation_data]
                    if self.annotation_listed and self.annotation_listed[-1] == "arrow":
                        self.annotation_listed.pop()
                        self.render_page(self.current_page)

                elif annotation_type == 'rectangle':
                    self.rectangles = [rect for rect in self.rectangles if rect != annotation_data]
                    if self.annotation_listed and self.annotation_listed[-1] == "rectangle":
                        self.annotation_listed.pop()
                        self.render_page(self.current_page)

            elif isinstance(annotation_data, tuple) and annotation_data[0] == "ellipse":
                # New handling for ellipse
                _, x1, y1, x2, y2, canvas_id, mode, page = annotation_data

                self.canvas.delete(canvas_id)

                self.annotations = [
                    ann for ann in self.annotations
                    if not (isinstance(ann, tuple) and ann[0] == "ellipse" and ann[5] == canvas_id)
                ]

                if self.annotation_listed and self.annotation_listed[-1] == "ellipse":
                    self.annotation_listed.pop()

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
            if self.annotation_listed and self.annotation_listed[-1] == "text_bg":
                self.annotation_listed.pop()
            elif self.annotation_listed and self.annotation_listed[-1] == "text":
                self.annotation_listed.pop()
        
            print("Undo action completed balance list:", self.change_history)

        # elif action_type in ("add_text", "add_text_bg"):
        #     _, page, x_scaled, y_scaled, text = last_action
        #     annotation_dict = self.text_annotations if action_type == "add_text" else self.text_annotations_bg
        #     if (page, x_scaled, y_scaled) in annotation_dict:
        #         del annotation_dict[(page, x_scaled, y_scaled)]
        #         page_obj = self.pdf_document[page]
        #         annot = page_obj.first_annot
        #         while annot:
        #             if annot.info and annot.info.get("contents") == text:
        #                 page_obj.delete_annot(annot)
        #                 break
        #             annot = annot.next
        #         self.render_page(self.current_page)
        #     if self.annotation_listed[-1]=="text_bg":
        #         self.annotation_listed.pop()
        #     elif self.annotation_listed[-1]=="text":
        #         self.annotation_listed.pop()
        #     print("Undo action completed balance list:", self.change_history)

        elif action_type == "add_polygon":
            _, page, x, y, mode, points = last_action
            if page in self.polygon_annotations:
                # Find matching polygon by comparing points
                for i, polygon_data in enumerate(self.polygon_annotations[page]):
                    if polygon_data["base_points"] == points or polygon_data["points"] == points:
                        del self.polygon_annotations[page][i]
                        break
                if page == self.current_page:
                    self.redraw_polygons()
                    self.render_page(self.current_page)
            if self.annotation_listed and self.annotation_listed[-1] == "polygon":
                self.annotation_listed.pop()
            print("Undo: removed last added polygon.")


        elif action_type == "polygon":
            _, page, prev_base_points, polygon_id = last_action
            if page in self.polygon_annotations:
                for i, polygon_data in enumerate(self.polygon_annotations[page]):
                    if polygon_data.get("polygon_id") == polygon_id:
                        if prev_base_points is not None:
                            # Undo polygon creation: remove it
                            del self.polygon_annotations[page][i]
                        else:
                            # Undo move/reshape: restore previous base_points
                            polygon_data["base_points"] = polygon_data["points"].copy()
                        break
                if page == self.current_page:
                    self.redraw_polygons()
                    self.render_page(self.current_page)

            if self.annotation_listed and self.annotation_listed[-1] == "polygon":
                self.annotation_listed.pop()
            print("Undo action completed. Remaining change history:", self.undo_change_history)

        elif action_type == "sticky_note":
            _, page, x_scaled, y_scaled, _ = last_action
            if (page, x_scaled, y_scaled) in self.sticky_notes:
                del self.sticky_notes[(page, x_scaled, y_scaled)]
                if self.annotation_listed[-1]=="sticky_note":
                    self.annotation_listed.pop()
                self.render_page(self.current_page)
            print("Undo action completed balance list:", self.undo_change_history)
        elif action_type == "image_overlay":
            _, page, overlay_info = last_action
            # Remove from image_overlays list
            if hasattr(self, "image_overlays"):
                self.image_overlays = [overlay for overlay in self.image_overlays 
                                    if overlay["id"] != overlay_info["id"]]
            
            # Delete the image from canvas if it exists
            if "canvas_id" in overlay_info:
                self.canvas.delete(overlay_info["canvas_id"])
            
            # Remove from tk_images dictionary to free memory
            if hasattr(self, "tk_images") and overlay_info["id"] in self.tk_images:
                del self.tk_images[overlay_info["id"]]
            
            if self.annotation_listed[-1]=="image_overlay":
                self.annotation_listed.pop()
            
            # Only re-render if we're on the same page
            if page == self.current_page:
                self.render_page(self.current_page)
            print("Undo action completed balance list:", self.undo_change_history)
        else:
            print(f"Unknown action type: {action_type}")

    def deactivate_colour(self, valu, deact=None):
        """Deactivate the color button"""
        # , self.highlight_button
        list_of_buttons = [self.selectzoom_button, self.sticky_note_button, 
                           self.delete_button, self.text_button, self.text_bg_button, self.draw_button, 
                           self.filled_polygon_button, self.hollow_polygon_button, self.image_button, 
                           self.line_button, self.arrow_button, self.hollow_rectangle_button, 
                           self.filled_rectangle_button, self.hollow_ellipse_button, self.filled_ellipse_button, 
                           self.redact_button,self.deleteredact_button,self.filled_highlight_rectangle_button]
        

        deactivating_function = [ "active_deleteannotation", "active_freehandline", "active_filledpolygon", "active_hollowpolgon", "active_line", "sticky_note_mode",
                "active_arrow", "active_hollowrectangle", "active_filledrectangle", "active_hollowellipse", "active_filledellipse", "active_redact", "activedeleteredact_button","active_highlight_filledrectangle"]
        for button in list_of_buttons:
            print("button------------------",button)
            if button != valu:
                if button == self.filled_polygon_button or button == self.hollow_polygon_button:
                    button.configure(text="",fg_color="#00498f",hover_color="#023261")
                    self.polygon_mode = None
                    self.start_point = None
                    self.polygon_created = False  # Reset creation flag
                    self.polygon_active = "no"
                    self.canvas.unbind("<Button-1>")
                    self.canvas.config(cursor="arrow")
                else:
                    button.configure(fg_color="#00498f",hover_color="#023261")
        
        for attr_name in deactivating_function:
            if attr_name != deact:  # Compare by string name
                setattr(self, attr_name, False)

#################################################################################################################

    def activate_Highlight_rectangle_tool(self):
        """Activate the filled rectangle drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_highlight_filledrectangle:
            self.deactivate_tools()
            self.active_highlight_filledrectangle = False
            self.filled_highlight_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_highlight_filledrectangle = True
        self.deactivate_colour(self.filled_highlight_rectangle_button,"active_highlight_filledrectangle")
        self.filled_highlight_rectangle_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools()
        self.is_drawing_filled_rect = True
        self.is_drawing_hollow_rect = False
        self.highlight_mode = False
        self.canvas.bind("<Button-1>", self.start_Highlight_rectangle_drawing)
        self.canvas.bind("<B1-Motion>", self.draw_Highlight_rectangle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_Highlight_filled_rectangle)

    def start_Highlight_rectangle_drawing(self, event):
        """Start drawing a rectangle (for hollow/filled tools)."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        outline_color = "yellow"
        fill_color = "" if self.is_drawing_hollow_rect else "yellow"
        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
            outline=outline_color, fill=fill_color,stipple='gray25', width=4, tags="annotation_preview")

    def draw_Highlight_rectangle_preview(self, event):
        """Show a preview of the rectangle while dragging."""
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        outline_color = "yellow"
        fill_color = "" if self.is_drawing_hollow_rect else "yellow"
        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, end_x, end_y,
            outline=outline_color, fill=fill_color,stipple='gray25', width=4, tags="annotation_preview")


    def finish_Highlight_filled_rectangle(self, event):
        """Finish drawing the filled rectangle and add it to annotations."""
        self.finish_Highlight_rectangle(event, filled=True)
        

    def finish_Highlight_rectangle(self, event, filled):
        """Finish drawing a rectangle and add it to annotations."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        
        # Ensure coordinates are properly ordered (top-left to bottom-right)
        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        
        # Delete the preview rectangle
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        
        # Create visual rectangle on canvas
        outline_color = "yellow"
        fill_color = "" if not filled else "yellow"
        border_width = 4 if not filled else 3
        rect_id = self.canvas.create_rectangle(
            x1, y1, x2, y2,
            outline=outline_color, fill=fill_color,stipple='gray25', width=border_width, tags="annotation")
        
        # Store rectangle data (in original PDF coordinates)
        pdf_coords = self.canvas_to_pdf_coordinates(x1, y1, x2, y2)
        rect_data = {
            'type': 'rectangle',
            'page': self.current_page,
            'x1': pdf_coords[0],
            'y1': pdf_coords[1],
            'x2': pdf_coords[2],
            'y2': pdf_coords[3],
            'filled': filled,
            'id': rect_id,
            'color': "yellow",
            'rotation_page': self.pdf_document[self.current_page].rotation
        }
        
        self.rectangles.append(rect_data)
        self.annotations.append(rect_data)
        self.change_history.append(('add_annotation', rect_data))
        self.undo_change_history.append(('add_annotation', rect_data))
        self.annotation_is_available = True
        # self.deactivate_tools()
        self.annotation_listed.append("rectangle")
        self.canvas.tag_bind(rect_id, "<Button-1>", self.on_Highlight_rectangle_press)
        self.canvas.tag_bind(rect_id, "<B1-Motion>", self.on_Highlight_rectangle_drag)
        self.canvas.tag_bind(rect_id, "<ButtonRelease-1>", self.on_Highlight_rectangle_release)

    def on_Highlight_rectangle_press(self, event):
        """Handle mouse press on rectangle."""
        if not (event.state & 0x0001):
            return
        # Get the clicked item
        clicked_item = self.canvas.find_closest(event.x, event.y)[0]
        
        # Check if the clicked item is actually a rectangle annotation
        item_tags = self.canvas.gettags(clicked_item)
        if "annotation" in item_tags or "yellow_rectangle" in item_tags:
            # Verify it's actually a rectangle from our annotations
            for rect in self.rectangles:
                if rect.get("id") == clicked_item and rect["page"] == self.current_page:
                    self.dragged_rectangle_id = clicked_item
                    self.rect_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
                    # Prevent the event from propagating to the canvas (which would start page dragging)
                    return "break"
            
            # If we found an annotation tag but no matching rectangle, clear any drag state
            self.dragged_rectangle_id = None
            self.rect_drag_start = None
        else:
            # Not clicking on a rectangle, clear drag state
            self.dragged_rectangle_id = None
            self.rect_drag_start = None

    def on_Highlight_rectangle_drag(self, event):
        """Handle dragging of rectangle."""
        if self.dragged_rectangle_id and self.rect_drag_start:
            x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            dx = x - self.rect_drag_start[0]
            dy = y - self.rect_drag_start[1]
            
            # Deactivate rectangle tools when dragging
            self.deactivate_tools()
            self.active_highlight_filledrectangle = False
            self.active_highlight_filledrectangle = False
            self.filled_highlight_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")            
            self.canvas.move(self.dragged_rectangle_id, dx, dy)
            self.rect_drag_start = (x, y)
            
            # Prevent event propagation to avoid page dragging
            return "break"

    def on_Highlight_rectangle_release(self, event):
        """Update stored annotation data after dragging."""
        if not self.dragged_rectangle_id:
            return
            
        bbox = self.canvas.bbox(self.dragged_rectangle_id)
        if not bbox:
            self.dragged_rectangle_id = None
            self.rect_drag_start = None
            return
            
        new_x1, new_y1, new_x2, new_y2 = [v / self.zoom_factor for v in bbox]

        # Update rectangle data
        for rect in self.rectangles:
            if rect["id"] == self.dragged_rectangle_id and rect["page"] == self.current_page:
                old_data = dict(rect)  # Store old data for history
                rect.update({
                    "x1": new_x1, "y1": new_y1,
                    "x2": new_x2, "y2": new_y2
                })
                self.change_history.append(('move_annotation', old_data, dict(rect)))
                self.undo_change_history.append(('move_annotation', old_data, dict(rect)))
                break

        # Safely update annotation data
        for annotation in self.annotations:
            if isinstance(annotation, dict) and annotation.get("id") == self.dragged_rectangle_id and annotation["page"] == self.current_page:
                annotation.update({
                    "x1": new_x1, "y1": new_y1,
                    "x2": new_x2, "y2": new_y2
                })
                break
        self.dragged_rectangle_id = None
        self.rect_drag_start = None

        return "break"



    # def on_mouse_hover(self, event):
    #     """Change cursor when hovering over a polygon or sticky note."""
    #     if not self.pdf_document or self.current_page is None:
    #         return
    #     x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
    #     tooltip_shown = False
    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation

    #     # Adjust the coordinates for zoom
    #     adjusted_x, adjusted_y = x / self.zoom_factor, y / self.zoom_factor

    #       # for drawing in self.page_drawings.get(self.current_page, []):
    #     for drawing in getattr(self, 'current_page_drawings', []):
    #         if isinstance(drawing, tuple) and len(drawing) == 3:  # Polygon (id, points, color)
    #             _, points, _ = drawing

    #             # Adjust the polygon coordinates for zoom
    #             zoomed_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in zip(points[::2], points[1::2])]

    #             if self.is_point_inside_polygon(x, y, sum(zoomed_points, ())):  # Flatten the list
    #                 self.canvas.config(cursor="hand2")
    #                 return  # Exit function early if hovering over a polygon

    #     # Sticky note cursor handling
    #     for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
    #         if page_num == self.current_page:
    #             x_position = x_scaled * self.zoom_factor
    #             y_position = y_scaled * self.zoom_factor
    #             page_width = page.rect.width * self.zoom_factor
    #             page_height = page.rect.height * self.zoom_factor

    #             # Handle rotation
    #             if rotation_angle == 90:
    #                 rotated_x, rotated_y = self.page_height + (180 * self.zoom_factor) - y_position, x_position
    #             elif rotation_angle == 180:
    #                 rotated_x = page_width - x_position
    #                 rotated_y = page_height - y_position
    #             elif rotation_angle == 270:
    #                 rotated_x, rotated_y = y_position, self.page_width - (180 * self.zoom_factor) - x_position
    #             else:  # 0 degrees
    #                 rotated_x = x_position
    #                 rotated_y = y_position

    #             if abs(x - rotated_x) < 20 and abs(y - rotated_y) < 20:  # Adjust hover sensitivity
    #                 if not tooltip_shown:
    #                     self.show_tooltip(event.x_root, event.y_root, text)
    #                     tooltip_shown = True
    #                 break

    #     if not tooltip_shown:
    #         if self.active_tooltip:
    #             self.active_tooltip.destroy()
    #             self.active_tooltip = None
    #         self.canvas.config(cursor="arrow")  # Ensure cursor resets correctly

    def on_mouse_hover(self, event):
        """Change cursor when hovering over a polygon or sticky note."""
        if not self.pdf_document or self.current_page is None:
            return
            
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        tooltip_shown = False
        
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        page_width = self.page_width
        page_height = self.page_height
        
        # Check for polygon hover (keeping original logic)
        for drawing in getattr(self, 'current_page_drawings', []):
            if isinstance(drawing, tuple) and len(drawing) == 3:
                _, points, _ = drawing
                zoomed_points = [(px * self.zoom_factor, py * self.zoom_factor) 
                            for px, py in zip(points[::2], points[1::2])]
                
                if self.is_point_inside_polygon(x, y, sum(zoomed_points, ())):
                    self.canvas.config(cursor="hand2")
                    return
        
        # Check for sticky note hover with proper rotation handling
        for (page_num, x_scaled, y_scaled), note_data in self.sticky_notes.items():
            if page_num == self.current_page:
                # Handle both old string format and new dict format
                if isinstance(note_data, str):
                    text = note_data
                    base_x, base_y = x_scaled, y_scaled
                    insertion_rotation = 0
                else:
                    text = note_data["text"]
                    base_x = note_data.get("base_x", x_scaled)
                    base_y = note_data.get("base_y", y_scaled)
                    insertion_rotation = note_data.get("insertion_rotation", 0)
                
                # Calculate display position with rotation
                rotation_diff = (current_rotation - insertion_rotation) % 360
                scaled_x = base_x * self.zoom_factor
                scaled_y = base_y * self.zoom_factor
                
                if rotation_diff == 0:
                    display_x = scaled_x
                    display_y = scaled_y
                else:
                    display_x, display_y = self.apply_sticky_note_rotation_to_point(
                        scaled_x, scaled_y, page_width, page_height, rotation_diff, insertion_rotation)
                
                # Check if mouse is near the sticky note
                if abs(x - display_x) < 20 and abs(y - display_y) < 20:
                    if not tooltip_shown:
                        self.show_tooltip(event.x_root, event.y_root, text)
                        tooltip_shown = True
                    break
        
        if not tooltip_shown:
            if self.active_tooltip:
                self.active_tooltip.destroy()
                self.active_tooltip = None
            self.canvas.config(cursor="arrow")



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
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.sticky_note_mode:
            self.sticky_note_mode = False
            self.canvas.unbind("<Button-1>")
            self.sticky_note_button.configure(fg_color="#00498f", hover_color="#023261")
        else:
            self.deactivate_colour(self.sticky_note_button,"sticky_note_mode")
            self.deactivate_tools()
            self.sticky_note_button.configure(fg_color="#d17a24",hover_color="#b56e26")
            self.enable_sticky_note_mode()

# -----------------------------------------------------------------------------------------------------------
######################################################################################################################################

    def save_pdf(self, file_path=None):
        """Save the PDF with embedded sticky notes and upload directly to the server."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF document to save.")
            return

        print("self.annotation_listed",self.annotation_listed)
        print("edit_file_name-----------------",self.edit_file_name)  
        print("Serverurl--------------------------------------------------------------------------------------------------",self.server_url)
        try:
            temp_pdf = fitz.open()
            for page_num in range(len(self.pdf_document)):
                page = self.pdf_document[page_num]
                temp_pdf.insert_pdf(self.pdf_document, from_page=page_num, to_page=page_num)

            for page_num in self.polygon_annotations:
                if page_num < len(temp_pdf):
                    page = temp_pdf[page_num]
                    # Add debug info
                    print(f"Saving polygons for page {page_num}, page rotation: {page.rotation}")
                    for i, polygon_data in enumerate(self.polygon_annotations[page_num]):
                        print(f"  Polygon {i}: insertion_rotation={polygon_data.get('insertion_rotation', 0)}")
                        print(f"  First few base_points: {polygon_data['base_points'][:8]}")
                    self._embed_polygons_to_page(page, page_num)
            try:
                for annotation in self.annotations:
                    if isinstance(annotation, tuple) and annotation[0] == 'ellipse' and annotation[1] is not None:
                        _, x1, y1, x2, y2, _, mode,numb = annotation
                        page_num = numb
                        page = temp_pdf[page_num]
                        self.add_ellipse_annotation(page, x1, y1, x2, y2, mode)
            except:
                print("Error adding ellipse annotations")
            
            if hasattr(self, "image_overlays"):
                for overlay in self.image_overlays:
                    page_num = overlay["page"]
                    if page_num < len(temp_pdf):
                        page = temp_pdf[page_num]
                        self.add_image_overlay_to_pdf(page, overlay)
            print("terethetttehht reached here .........................")
            try:

                for rect in self.rectangles:
                    if rect['type'] != 'rectangle' or rect['page'] >= len(temp_pdf):
                        continue
                    if rect['color'] not in ('red', 'yellow'):
                        print(f"Skipping non-red rectangle: {rect['color']}")  # Optional debug
                        continue
                    # Only proceed if the rectangle is red and within valid page range
                    page = temp_pdf[rect['page']]
                    rect_coords = fitz.Rect(rect['x1'], rect['y1'], rect['x2'], rect['y2'])
                    if rect['color'] == 'yellow':
                        rgb_color = (1, 1, 0)  # Yellow
                        fill_opacity = 0.4
                    else:
                        rgb_color = (1, 0, 0)  # Red
                        fill_opacity = 1.0
                    print("rect colorr", rect['color'])
                    if rect['filled']:
                        page.draw_rect(rect_coords, color=rgb_color, fill=rgb_color, width=4, fill_opacity=fill_opacity)
                    else:
                        page.draw_rect(rect_coords, color=rgb_color, fill=None, width=3)

                # Add line annotations
                for line in self.lines:
                    if line['type'] == 'line' and line['page'] < len(temp_pdf):
                        page = temp_pdf[line['page']]
                        # Create a line using PyMuPDF
                        start_point = fitz.Point(line['x1'], line['y1'])
                        end_point = fitz.Point(line['x2'], line['y2'])
                        rgb_color = (1, 0, 0)  # Red in RGB (0-1 range)
                        page.draw_line(start_point, end_point, color=rgb_color, width=4)
                        
                # Add arrow annotations
                for arrow in self.arrows:
                    if arrow['page'] < len(temp_pdf):
                        page = temp_pdf[arrow['page']]
                        start_point = fitz.Point(arrow['x1'], arrow['y1'])
                        end_point = fitz.Point(arrow['x2'], arrow['y2'])
                        
                        # Create the arrow annotation
                        annot = page.add_line_annot(start_point, end_point)
                        annot.set_colors(stroke=(1, 0, 0))  # Red color
                        ## Line end styles: 0=None, 1=Square, 2=Circle, 3=Diamond, 4=OpenArrow, 5=ClosedArrow, 6=Butt, 7=ROpenArrow, 8=RClosedArrow
                        annot.set_line_ends(0, 5)  # First value is start style, second is end style (2 = arrow)
                        annot.set_border(width=4)
                        annot.update()

            except Exception as e:
                print(f"Error adding rectangle annotations: {str(e)}")
            for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
                page = temp_pdf[page_num]
                self.add_text_sticky_annotation(page, x_scaled, y_scaled, text)
            for (page_num, x_scaled, y_scaled), annotation_data in self.text_annotations.items():
                page = temp_pdf[page_num]           
                if isinstance(annotation_data, dict):
                    text = annotation_data["text"]
                else:
                    text = annotation_data
                self.add_plain_text_annotation(page, x_scaled, y_scaled, text)
            try:
                for (page_num, x_scaled, y_scaled), annotation_data in self.text_annotations_bg.items():
                    page = temp_pdf[page_num]
                    if isinstance(annotation_data, dict):
                        text = annotation_data.get("text", "")
                    else:
                        text = annotation_data
                    self.add_text_with_bg_annotation(page, x_scaled, y_scaled, text)
            except Exception as e:
                print(f"Error adding text with background annotations: {e}")
            print("before freehand")
            # Add freehand drawings to the PDF
            for item in self.change_history:
                if item[0] == "freehand":
                    _, page_num, _, points = item
                    page = temp_pdf[page_num]
                    self.add_freehand_line_annotation(page, points)
            pdf_buffer = io.BytesIO()
            temp_pdf.save(pdf_buffer, garbage=4, deflate=True, deflate_images=True, clean=True)
            pdf_buffer.seek(0)
            print("before save function-----------------")
            try:
                delete_url = "https://idms-dev.blockchaincloudapps.com/api/v1/delete-pdf-viewer-redact-info"
                # delete_url = "http://172.20.1.60:5000/api/v1/delete-pdf-viewer-redact-info"
                delete_payload = json.dumps({
                    "temp_id": str(self.temp_id)
                })
                headers = {
                                'Authorization': 'Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJmcmVzaCI6ZmFsc2UsImlhdCI6MTc1NTY2NzY3NywianRpIjoiMWViZThiODAtZTJiZS00MmZkLWIxZWMtNmU2MmI4NWFlOTNkIiwidHlwZSI6ImFjY2VzcyIsInN1YiI6ImRob25pIiwibmJmIjoxNzU1NjY3Njc3LCJjc3JmIjoiZGIxN2UzNzYtOGVlYi00YmI1LTk0MTctZWMyMWJmMjQ1YzgxIiwiZXhwIjoxNzU1NjY4NTc3fQ.oXKx53IBNUtYP575pm53b7WyR8RJXB5jxt1amUdG_wk',
                                'Content-Type': 'application/json'
                            }
                delete_response = requests.delete(delete_url, headers=headers, data=delete_payload)
                print(f"Delete existing redaction data status: {delete_response.status_code}")
                if delete_response.status_code not in [200, 201, 204]:
                    print(f"Warning: Failed to delete existing redaction data: {delete_response.text}")
            except Exception as e:
                print(f"Error deleting existing redaction data: {str(e)}")
            
            # Insert data from self.all_page_rectangles
            if hasattr(self, 'all_page_rectangles') and self.all_page_rectangles:
                try:
                    redact_url_api = "https://idms-dev.blockchaincloudapps.com/api/v1/insert-pdf-viewer-redact-info"
                    # redact_url_api = "http://172.20.1.60:5000/api/v1/insert-pdf-viewer-redact-info"
                    headers = {
                                'Authorization': 'Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJmcmVzaCI6ZmFsc2UsImlhdCI6MTc1NTY2NzY3NywianRpIjoiMWViZThiODAtZTJiZS00MmZkLWIxZWMtNmU2MmI4NWFlOTNkIiwidHlwZSI6ImFjY2VzcyIsInN1YiI6ImRob25pIiwibmJmIjoxNzU1NjY3Njc3LCJjc3JmIjoiZGIxN2UzNzYtOGVlYi00YmI1LTk0MTctZWMyMWJmMjQ1YzgxIiwiZXhwIjoxNzU1NjY4NTc3fQ.oXKx53IBNUtYP575pm53b7WyR8RJXB5jxt1amUdG_wk',
                                'Content-Type': 'application/json'
                            }
                    for page_num, rectangles in self.all_page_rectangles.items():
                        for rect_data in rectangles:
                            # Get page size for this rectangle
                            page = self.pdf_document.load_page(page_num)
                            page_size = [page.rect.width, page.rect.height]
                            print(f"checking page rotation in all_page_rectangles page{page_num}: {page.rotation}")
                            payload = json.dumps({
                                "file_name": self.filename_pdf,
                                "temp_id": str(self.temp_id),
                                "doc_id": str(self.doc_id),
                                "coordinate": str(rect_data),
                                "page_size": str(page_size),
                                "rotation_degree": page.rotation,
                                "zoom_size": self.zoom_factor,
                                "stored_from": "Viewer"
                            })                    
                            response = requests.post(redact_url_api, headers=headers, data=payload)
                            print(f"Insert all_page_rectangles status: {response.status_code}")
                            if response.status_code not in [200, 201]:
                                print(f"Warning: Failed to insert rectangle data: {response.text}")
                                
                except Exception as e:
                    print(f"Error inserting data from all_page_rectangles: {str(e)}")
            
            # Insert data from self.redact_api_rectangles (existing logic)
            if len(self.redact_api_rectangles) > 0:
                print("redact_api_rectangles", self.redact_api_rectangles)
                try:
                    for rect_data in self.redact_api_rectangles:
                        if rect_data['source'] == "local":
                            page_size = self.add_pagesize[rect_data['id']]
                            page_here = self.pdf_document.load_page(rect_data['page'])
                            print(f"checking page rotation in redact_api_rectangles page{rect_data['page']}: {page_here.rotation}")
                            redact_url = "https://idms-dev.blockchaincloudapps.com/api/v1/insert-pdf-viewer-redact-info"
                            # redact_url = "http://172.20.1.60:5000/api/v1/insert-pdf-viewer-redact-info"
                            payload = json.dumps({
                                    "file_name": self.filename_pdf,
                                    "temp_id": str(self.temp_id),
                                    "doc_id": str(self.doc_id),
                                    "coordinate": str(rect_data),
                                    "page_size": str(page_size),
                                    "zoom_size": self.zoom_factor,
                                    "rotation_degree": page_here.rotation,
                                    "stored_from": "Viewer"
                                    })
                            headers = {
                                'Authorization': 'Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJmcmVzaCI6ZmFsc2UsImlhdCI6MTc1NTY2NzY3NywianRpIjoiMWViZThiODAtZTJiZS00MmZkLWIxZWMtNmU2MmI4NWFlOTNkIiwidHlwZSI6ImFjY2VzcyIsInN1YiI6ImRob25pIiwibmJmIjoxNzU1NjY3Njc3LCJjc3JmIjoiZGIxN2UzNzYtOGVlYi00YmI1LTk0MTctZWMyMWJmMjQ1YzgxIiwiZXhwIjoxNzU1NjY4NTc3fQ.oXKx53IBNUtYP575pm53b7WyR8RJXB5jxt1amUdG_wk',
                                'Content-Type': 'application/json'
                            }
                            response = requests.request("POST", redact_url, headers=headers, data=payload)
                            print("redact_api status", response.text, response.status_code)
                except Exception as e:
                    print("Error in sending redaction data to API:", str(e))

            if len(self.change_redact_history) > 0 or len(self.redactions) > 0:
                print("its has redactions or changes_redact_history in it")
                if "_redact_with_annotations" in self.filename_pdf:
                    print("1")
                    edit_file_name = self.edit_file_name
                    files = {'id': (None, self.doc_id),
                            'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                    response = requests.post(self.server_url, files=files)
                    if response.status_code in [200, 201]:
                        messagebox.showinfo("Success", "File saved successfully")
                        print("File saved successfully  _redact.pdf")
                    else:
                        messagebox.showerror("Error", "Failed to save the file.")
                        return
                elif "redact" in self.filename_pdf:
                    print("2")
                    print("____________________redact.pdf")
                    if len(self.annotation_listed)==0:   
                        edit_file_name = self.edit_file_name
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return  
                    elif len(self.annotation_listed)>0:
                        print("3")
                        edit_file_name = self.edit_file_name.replace("redact", "redact_with_annotations")
                        print("***************rdnsgrsrfb*******************************************************************rdrdht******************")
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return
                elif "with_annotations" in self.filename_pdf:
                    print("4")
                    edit_file_name = self.edit_file_name.replace("with_annotations", "redact_with_annotations")
                    print("***************rdnsgrsrfb*******************************************************************rdrdht******************")
                    print("redact_file_name--*****-",edit_file_name)
                    files = {'id': (None, self.doc_id),
                            'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                    response = requests.post(self.server_url, files=files)
                    if response.status_code in [200, 201]:
                        messagebox.showinfo("Success", "File saved successfully")
                        print("File saved successfully  _redact.pdf")
                    else:
                        messagebox.showerror("Error", "Failed to save the file.")
                        return

                else:
                    if len(self.annotation_listed)==0:
                        print("5")
                        edit_file_name = self.edit_file_name.replace(".pdf", "_redact.pdf")
                        print("***************rdnsgrsrfb*******************************************************************rdrdht******************")
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return
                    elif len(self.annotation_listed) > 0:
                        print("6")
                        edit_file_name = self.edit_file_name.replace(".pdf", "_redact_with_annotations.pdf")
                        print("***************rdnsgrsrfb*******************************************************************rdrdht******************")
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return
            elif len(self.redactions) == 0:
                print("no redactions svsvsfbbfxxfsdvxfsdfxfxf    elifff")      
                if len(self.annotation_listed)>0:
                    # changes_data = self.change_history
                    # changes_data = str(changes_data)
                    # print("beforeexe----",beforeexe)
                    # sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
                    # val = (beforeexe,self.doc_id,changes_data,0)
                    # mycursor.execute(sql, val)
                    # mydb.commit()
                    print("yes")                 
                    if "redact_with_annotations" in self.edit_file_name:
                        print("_____________________redact_with_annotations.pdf")
                        edit_file_name = self.edit_file_name
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return
                    elif "with_annotations" in self.edit_file_name:
                        print("_____-----------------------________________with_annotations.pdf")
                        edit_file_name = self.edit_file_name
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return
                    elif "redact" in self.filename_pdf:
                        print("___________------------------------_________redact.pdf")
                        edit_file_name = self.edit_file_name.replace("redact", "redact_with_annotations")
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return
                    else:
                        print("elseee---------------------------------------------------------------")
                        edit_file_name = self.edit_file_name.replace(".pdf", "_with_annotations.pdf")
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.")
                            return
                           
                else:
                    messagebox.showinfo("Info", "No Annotation made to save the file.")
        except:
            print(f"Failed to save PDF")

    def add_ellipse_annotation(self, page, x1, y1, x2, y2, mode):
        """Add ellipse annotation to the PDF page."""
        try:
            shape = page.new_shape()
            
            # Calculate center and radii of the ellipse
            cx = (x1 + x2) / 2
            cy = (y1 + y2) / 2
            rx = abs(x2 - x1) / 2
            ry = abs(y2 - y1) / 2
            
            # Draw the ellipse
            shape.draw_oval(fitz.Rect(x1, y1, x2, y2))
            
            # Set fill and stroke properties
            fill_color = None
            if mode == "filled":
                fill_color = (1, 0.5, 0)  # Orange color
            
            # Finish the shape with or without fill
            shape.finish(color=(1, 0.5, 0), fill=fill_color, width=6)
            
            # Commit the shape to the page
            shape.commit(overlay=True)
        except Exception as e:
            print(f"Error adding ellipse annotation: {e}")

    def add_image_overlay_to_pdf(self, page, overlay):
        """Add image overlay to the PDF page."""
        try:
            # Extract overlay properties
            base_x = overlay["base_x"]
            base_y = overlay["base_y"]
            base_width = overlay["base_width"]
            base_height = overlay["base_height"]
            image_path = overlay["image_path"]
            
            # Create a rectangle for the image placement
            rect = fitz.Rect(base_x, base_y, base_x + base_width, base_y + base_height)
            
            # Check if the image file exists and is readable
            if os.path.isfile(image_path):
                try:
                    # Insert the image onto the page
                    page.insert_image(rect, filename=image_path)
                except Exception as img_error:
                    print(f"Error inserting image into PDF: {img_error}")
            else:
                print(f"Image file not found: {image_path}")
        except Exception as e:
            print(f"Error adding image overlay: {e}")

    # def _embed_polygons_to_page(self, page, page_num):
    #     """Embed polygons to a specific page using polygon_annotations."""
    #     try:
    #         if not hasattr(self, 'polygon_annotations'):
    #             return
    #         if page_num not in self.polygon_annotations:
    #             return

    #         # Clear existing polygon annotations on this page
    #         for annot in page.annots():
    #             if annot.info.get("title") == "polygon_annotation":
    #                 annot.delete()

    #         for polygon_data in self.polygon_annotations[page_num]:
    #             base_points = polygon_data["base_points"]
    #             mode = polygon_data.get("mode", "hollow")

    #             if len(base_points) < 6:  # Must be at least a triangle
    #                 continue

    #             # Convert base_points to (x, y) pairs
    #             point_pairs = [
    #                 (base_points[i], base_points[i + 1])
    #                 for i in range(0, len(base_points), 2)
    #             ]

    #             # Draw polygon shape on the page
    #             shape = page.new_shape()
    #             for i in range(len(point_pairs)):
    #                 p1 = point_pairs[i]
    #                 p2 = point_pairs[(i + 1) % len(point_pairs)]
    #                 shape.draw_line(p1, p2)

    #             # Fill or outline the shape
    #             if mode == "filled":
    #                 shape.finish(fill=(0, 0, 1), color=None)
    #             elif mode == "hollow":
    #                 shape.finish(color=(1, 0, 0), fill=None, width=3)

    #             shape.commit(overlay=True)

    #         # Mark as embedded
    #         if not hasattr(self, 'embedded_polygons'):
    #             self.embedded_polygons = {}
    #         self.embedded_polygons[page_num] = self.polygon_annotations[page_num].copy()

    #     except Exception as e:
    #         print(f"Error embedding polygons to page {page_num}: {e}")
######################################################################################################################
# ok but still needs improvement as it does not support rotation in all cases
    # def _embed_polygons_to_page(self, page, page_num):
    #     """Embed polygons to a specific page using polygon_annotations with rotation support."""
    #     try:
    #         if not hasattr(self, 'polygon_annotations'):
    #             return
    #         if page_num not in self.polygon_annotations:
    #             return
            
    #         # Remove existing polygon annotations
    #         for annot in page.annots():
    #             if annot.info.get("title") == "polygon_annotation":
    #                 annot.delete()
            
    #         # Get page rotation
    #         rotation = page.rotation
            
    #         for polygon_data in self.polygon_annotations[page_num]:
    #             base_points = polygon_data["base_points"]
    #             mode = polygon_data.get("mode", "hollow")
                
    #             if len(base_points) < 6:
    #                 continue
                
    #             # Transform points based on page rotation
    #             transformed_points = self._transform_points_for_rotation(base_points, page, rotation)
                
    #             # Create point pairs from transformed points
    #             point_pairs = [
    #                 (transformed_points[i], transformed_points[i + 1])
    #                 for i in range(0, len(transformed_points), 2)
    #             ]
                
    #             # Draw the polygon
    #             shape = page.new_shape()
    #             for i in range(len(point_pairs)):
    #                 p1 = point_pairs[i]
    #                 p2 = point_pairs[(i + 1) % len(point_pairs)]
    #                 shape.draw_line(p1, p2)
                
    #             if mode == "filled":
    #                 shape.finish(fill=(0, 0, 1), color=None)
    #             elif mode == "hollow":
    #                 shape.finish(color=(1, 0, 0), fill=None, width=3)
                
    #             shape.commit(overlay=True)
            
    #         if not hasattr(self, 'embedded_polygons'):
    #             self.embedded_polygons = {}
    #         self.embedded_polygons[page_num] = self.polygon_annotations[page_num].copy()

    #     except Exception as e:
    #         print(f"Error embedding polygons to page {page_num}: {e}")

    # def _transform_points_for_rotation(self, points, page, rotation):
    #     """Transform polygon points based on page rotation."""
    #     if rotation == 0:
    #         return points
        
    #     # Get page dimensions
    #     page_rect = page.rect
    #     width = page_rect.width
    #     height = page_rect.height
        
    #     transformed_points = []
        
    #     # Process points in pairs (x, y)
    #     for i in range(0, len(points), 2):
    #         x = points[i]
    #         y = points[i + 1]
            
    #         if rotation == 90:
    #             # 90° clockwise: (x, y) -> (y, width - x)
    #             new_x = y
    #             new_y = width - x
    #         elif rotation == 180:
    #             # 180°: (x, y) -> (width - x, height - y)
    #             new_x = width - x
    #             new_y = height - y
    #         elif rotation == 270:
    #             # 270° clockwise (or 90° counter-clockwise): (x, y) -> (height - y, x)
    #             new_x = height - y
    #             new_y = x
    #         else:
    #             # No rotation or unsupported rotation
    #             new_x = x
    #             new_y = y
            
    #         transformed_points.extend([new_x, new_y])
        
    #     return transformed_points
###########################################################################################################
  
    def _embed_polygons_to_page(self, page, page_num):
        """Embed polygons to a specific page using polygon_annotations with rotation support."""
        try:
            if not hasattr(self, 'polygon_annotations'):
                return
            if page_num not in self.polygon_annotations:
                return
            for annot in page.annots():
                if annot.info.get("title") == "polygon_annotation":
                    annot.delete()
            current_rotation = page.rotation
            page_width = page.rect.width
            page_height = page.rect.height
            for polygon_data in self.polygon_annotations[page_num]:
                base_points = polygon_data["base_points"]
                mode = polygon_data.get("mode", "hollow")
                if len(base_points) < 6:
                    continue
                insertion_rotation = polygon_data.get("insertion_rotation", 0)
                rotation_diff = (current_rotation - insertion_rotation) % 360
                if rotation_diff == 0:
                    embed_points = base_points
                else:
                    embed_points = []
                    for i in range(0, len(base_points), 2):
                        x = base_points[i]
                        y = base_points[i + 1]
                        # Apply rotation transformation analogous to display, but in PDF scale
                        center_x = page_width / 2
                        center_y = page_height / 2
                        tx = x - center_x
                        ty = y - center_y
                        if rotation_diff == 90:
                            rotated_x = -ty
                            rotated_y = tx
                            if insertion_rotation == 0 or insertion_rotation == 180:
                                rotated_x += 380
                                rotated_y += 380
                            elif insertion_rotation == 90 or insertion_rotation == 270:
                                rotated_x += -380
                                rotated_y += -380
                        elif rotation_diff == 180:
                            rotated_x = -tx
                            rotated_y = -ty
                        elif rotation_diff == 270:
                            rotated_x = ty
                            rotated_y = -tx
                            if insertion_rotation == 0 or insertion_rotation == 180:
                                rotated_x -= 380
                                rotated_y -= 380
                            elif insertion_rotation == 90 or insertion_rotation == 270:
                                rotated_x -= -380
                                rotated_y -= -380
                        else:
                            rotated_x = tx
                            rotated_y = ty
                        final_x = rotated_x + center_x
                        final_y = rotated_y + center_y
                        embed_points.extend([final_x, final_y])
                point_pairs = [
                    (embed_points[i], embed_points[i + 1])
                    for i in range(0, len(embed_points), 2)]
                shape = page.new_shape()
                for i in range(len(point_pairs)):
                    p1 = fitz.Point(*point_pairs[i])
                    p2 = fitz.Point(*point_pairs[(i + 1) % len(point_pairs)])
                    shape.draw_line(p1, p2)
                if mode == "filled":
                    shape.finish(fill=(0, 0, 1), color=None)
                elif mode == "hollow":
                    shape.finish(color=(1, 0, 0), fill=None, width=3)
                shape.commit(overlay=True)
            if not hasattr(self, 'embedded_polygons'):
                self.embedded_polygons = {}
            self.embedded_polygons[page_num] = self.polygon_annotations[page_num].copy()
        except Exception as e:
            print(f"Error embedding polygons to page {page_num}: {e}")

    # def add_text_sticky_annotation(self, page, x_scaled, y_scaled, text):
    #     """Helper function to add text annotations properly."""
    #     today = date.today().strftime("%m-%d-%Y")
    #     base_text_size = 20  
    #     scaling_factor = max(page.rect.width, page.rect.height) / 1000  
    #     text_size = int(base_text_size * scaling_factor)
    #     marker_size = int(12 * scaling_factor)
    #     text_offset = int(15 * scaling_factor)
    #     padding = int(10 * scaling_factor)
    #     vertical_padding = int(15 * scaling_factor)
        
    #     marker_color = (1, 0, 0)
    #     page.draw_circle(center=(x_scaled, y_scaled), radius=marker_size / 2, color=marker_color, fill=marker_color)
        
    #     lines = self.wrap_text(f"{today}\n{text}", 50)
    #     max_text_width = max(len(line) for line in lines) * text_size * 0.6
    #     max_text_height = len(lines) * text_size * 1.5
    #     background_width = max_text_width + padding * 2
    #     background_height = max_text_height + vertical_padding * 2.5
        
    #     page.draw_rect(
    #         rect=(x_scaled, y_scaled + text_offset - vertical_padding, 
    #               x_scaled + background_width, y_scaled + text_offset + background_height),
    #         color=(1, 1, 0), overlay=True, fill_opacity=0.9, fill=(1, 1, 0)
    #     )
        
    #     text_x = x_scaled + padding
    #     text_y = y_scaled + text_offset
    #     for i, line in enumerate(lines):
    #         page.insert_text(point=(text_x, text_y + (i * text_size * 1.5)), text=line, fontsize=text_size, color=(0, 0, 0))

    def add_text_sticky_annotation(self, page, x_scaled, y_scaled, text):
        """Helper function to add text annotations properly."""
        try:
            # Find the annotation data to get rotation information
            annotation_data = None
            for (page_num, stored_x, stored_y), data in self.sticky_notes.items():
                if (page_num == page.number and 
                    abs(stored_x - x_scaled) < 1e-3 and 
                    abs(stored_y - y_scaled) < 1e-3):
                    annotation_data = data
                    break
            
            # Get rotation information
            current_rotation = page.rotation
            insertion_rotation = 0
            base_x = x_scaled
            base_y = y_scaled
            
            if annotation_data and isinstance(annotation_data, dict):
                insertion_rotation = annotation_data.get("insertion_rotation", 0)
                base_x = annotation_data.get("base_x", x_scaled)
                base_y = annotation_data.get("base_y", y_scaled)
                text_val = annotation_data.get("text", "")
            else:
                # Handle legacy string format
                text_val = text if isinstance(text, str) else str(text)
            
            # Calculate rotation difference
            rotation_diff = (current_rotation - insertion_rotation) % 360
            
            # Apply rotation transformation if needed
            final_x = base_x
            final_y = base_y
            
            if rotation_diff != 0:
                page_width = page.rect.width
                page_height = page.rect.height
                center_x = page_width / 2
                center_y = page_height / 2
                
                # Translate to center
                tx = base_x - center_x
                ty = base_y - center_y
                
                # Apply rotation
                if rotation_diff == 90:
                    rotated_x = -ty
                    rotated_y = tx
                    if insertion_rotation == 0 or insertion_rotation == 180:
                        rotated_x += 380
                        rotated_y += 380
                    elif insertion_rotation == 90 or insertion_rotation == 270:
                        rotated_x -= 380
                        rotated_y -= 380
                elif rotation_diff == 180:
                    rotated_x = -tx
                    rotated_y = -ty
                elif rotation_diff == 270:
                    rotated_x = ty
                    rotated_y = -tx
                    if insertion_rotation == 0 or insertion_rotation == 180:
                        rotated_x -= 380
                        rotated_y -= 380
                    elif insertion_rotation == 90 or insertion_rotation == 270:
                        rotated_x += 380
                        rotated_y += 380
                else:
                    rotated_x = tx
                    rotated_y = ty
                
                # Translate back from center
                final_x = rotated_x + center_x
                final_y = rotated_y + center_y
            
            # Get today's date
            today = date.today().strftime("%m-%d-%Y")
            
            # Calculate text size based on page dimensions
            base_text_size = 20  
            scaling_factor = max(page.rect.width, page.rect.height) / 1000  
            text_size = int(base_text_size * scaling_factor)
            text_offset = int(15 * scaling_factor)
            padding = int(10 * scaling_factor)
            vertical_padding = int(15 * scaling_factor)
            
            # Create display text with date
            display_text = f"{today}\n{text_val}"
            lines = self.wrap_text(display_text, 50)
            
            # Calculate background dimensions
            max_text_width = max(len(line) for line in lines) * text_size * 0.6
            max_text_height = len(lines) * text_size * 1.5
            background_width = max_text_width + padding * 2
            background_height = max_text_height + vertical_padding * 2.5
            
            # Position text box based on rotation
            if rotation_diff == 0:
                rect_x1 = final_x + text_offset
                rect_y1 = final_y - vertical_padding
                rect_x2 = final_x + text_offset + background_width
                rect_y2 = final_y + background_height - vertical_padding
                text_x = final_x + text_offset + padding
                text_y = final_y
            elif rotation_diff == 90:
                rect_x1 = final_x - background_height
                rect_y1 = final_y + text_offset
                rect_x2 = final_x - text_offset + vertical_padding
                rect_y2 = final_y + text_offset + background_width
                text_x = final_x - text_offset
                text_y = final_y + text_offset + padding
            elif rotation_diff == 180:
                rect_x1 = final_x - text_offset - background_width
                rect_y1 = final_y - background_height + vertical_padding
                rect_x2 = final_x - text_offset
                rect_y2 = final_y + vertical_padding
                text_x = final_x - text_offset - padding
                text_y = final_y
            elif rotation_diff == 270:
                rect_x1 = final_x + text_offset - vertical_padding
                rect_y1 = final_y - text_offset - background_width
                rect_x2 = final_x + background_height
                rect_y2 = final_y - text_offset
                text_x = final_x + text_offset
                text_y = final_y - text_offset - padding
            else:
                # Default positioning (same as rotation_diff == 0)
                rect_x1 = final_x + text_offset
                rect_y1 = final_y - vertical_padding
                rect_x2 = final_x + text_offset + background_width
                rect_y2 = final_y + background_height - vertical_padding
                text_x = final_x + text_offset + padding
                text_y = final_y
            
            # Draw yellow background rectangle (removed red dot)
            page.draw_rect(
                rect=(rect_x1, rect_y1, rect_x2, rect_y2),
                color=(1, 1, 0),  # Yellow border
                overlay=True, 
                fill_opacity=0.9, 
                fill=(1, 1, 0)  # Yellow fill
            )
            
            # Determine text rotation based on rotation difference
            if rotation_diff == 90:
                text_rotation = 270  # Use 270 instead of 90
            elif rotation_diff == 270:
                text_rotation = 90   # Use 90 instead of 270
            else:
                text_rotation = rotation_diff
            
            # Insert text lines with appropriate rotation
            for i, line in enumerate(lines):
                page.insert_text(
                    point=(text_x, text_y + (i * text_size * 1.5)), 
                    text=line, 
                    fontsize=text_size, 
                    color=(0, 0, 0),  # Black text
                    rotate=text_rotation  # Apply corrected rotation
                )
                
        except Exception as e:
            print(f"Error adding sticky text annotation: {e}")

    def add_freehand_line_annotation(self, page, points):
        """Add freehand line drawing to the PDF page."""
        if not points or len(points) < 2:
            return     
        # Set line properties
        stroke_color = (0, 0, 0)  # Black color   
        # Calculate scaling factor for line width based on page size
        scaling_factor = max(page.rect.width, page.rect.height) / 1000
        line_width = 2 * scaling_factor  # Adjust line width based on page size      
        # Convert the points to a continuous line
        page.draw_polyline(points, color=stroke_color, width=line_width)

    
    def add_plain_text_annotation(self, page, x_scaled, y_scaled, text):
        """Add plain text annotation to the PDF page with proper rotation handling."""
        try:
            annotation_data = None
            for (page_num, stored_x, stored_y), data in self.text_annotations.items():
                if (page_num == page.number and 
                    abs(stored_x - x_scaled) < 1e-3 and 
                    abs(stored_y - y_scaled) < 1e-3):
                    annotation_data = data
                    break
            current_rotation = page.rotation
            insertion_rotation = 0
            base_x = x_scaled
            base_y = y_scaled
            
            if annotation_data and isinstance(annotation_data, dict):
                insertion_rotation = annotation_data.get("insertion_rotation", 0)
                base_x = annotation_data.get("base_x", x_scaled)
                base_y = annotation_data.get("base_y", y_scaled)
            rotation_diff = (current_rotation - insertion_rotation) % 360
            final_x = base_x
            final_y = base_y
            
            if rotation_diff != 0:
                page_width = page.rect.width
                page_height = page.rect.height
                center_x = page_width / 2
                center_y = page_height / 2
                tx = base_x - center_x
                ty = base_y - center_y
                if rotation_diff == 90:
                    rotated_x = -ty
                    rotated_y = tx
                    if insertion_rotation == 0 or insertion_rotation == 180:
                        rotated_x += 380
                        rotated_y += 380
                    elif insertion_rotation == 90 or insertion_rotation == 270:
                        rotated_x -= 380
                        rotated_y -= 380
                elif rotation_diff == 180:
                    rotated_x = -tx
                    rotated_y = -ty
                elif rotation_diff == 270:
                    rotated_x = ty
                    rotated_y = -tx
                    if insertion_rotation == 0 or insertion_rotation == 180:
                        rotated_x -= 380
                        rotated_y -= 380
                    elif insertion_rotation == 90 or insertion_rotation == 270:
                        rotated_x += 380
                        rotated_y += 380
                else:
                    rotated_x = tx
                    rotated_y = ty
                final_x = rotated_x + center_x
                final_y = rotated_y + center_y
            
            text_size = 20  # Default text size
            scaling_factor = max(page.rect.width, page.rect.height) / 1000
            adjusted_text_size = int(text_size * scaling_factor)
            max_width = page.rect.width - final_x - 20  # 20-unit buffer from edge
            wrapped_text = self.wrap_text_for_saving(text, max_width, adjusted_text_size)
            
            # Calculate text dimensions and positioning 
            lines = wrapped_text.split('\n')
            max_line_length = max(len(line) for line in lines) if lines else 0
            actual_text_width = max_line_length * adjusted_text_size * 0.6
            text_height = len(lines) * adjusted_text_size * 1.2

            # Fix rotation values - swap 90 and 270 to match expected orientation
            if rotation_diff == 0:
                text_start_x = final_x
                text_start_y = final_y
                text_rotation = 0
            elif rotation_diff == 90:
                text_start_x = final_x
                text_start_y = final_y
                text_rotation = 270  # Use 270 instead of 90
            elif rotation_diff == 180:
                text_start_x = final_x
                text_start_y = final_y
                text_rotation = 180
            elif rotation_diff == 270:
                text_start_x = final_x
                text_start_y = final_y
                text_rotation = 90   # Use 90 instead of 270
            else:
                text_start_x = final_x
                text_start_y = final_y
                text_rotation = 0

            # Insert text with corrected rotation
            for i, line in enumerate(lines):
                page.insert_text(
                    point=(text_start_x, text_start_y + (i * adjusted_text_size * 1.2)),
                    text=line,
                    fontsize=adjusted_text_size,
                    color=(0, 0, 0),
                    rotate=text_rotation
                )
                
        except Exception as e:
            print(f"Error adding text annotation: {e}")

    
    def wrap_text_for_saving(self, text, max_width, font_size):
        """Ensure text is properly wrapped before saving to PDF."""
        # PyMuPDF doesn't automatically wrap text, so we need to do it manually
        # Approximate character width based on font size
        char_width = font_size * 0.5  # Rough estimate
        
        # Calculate max chars per line
        max_chars = int(max_width / char_width * 0.9)  # 10% safety margin
        max_chars = max(min(max_chars, 80), 5)  # Reasonable bounds
        
        # If text already contains newlines, respect them
        if '\n' in text:
            lines = text.split('\n')
            wrapped_lines = []
            for line in lines:
                if len(line) <= max_chars:
                    wrapped_lines.append(line)
                else:
                    # Wrap this line
                    words = line.split()
                    current_line = []
                    current_length = 0
                    
                    for word in words:
                        word_len = len(word)
                        space_len = 1 if current_length > 0 else 0
                        
                        if current_length + word_len + space_len > max_chars:
                            if current_line:  # Add current line if it exists
                                wrapped_lines.append(' '.join(current_line))
                            current_line = [word]
                            current_length = word_len
                        else:
                            current_line.append(word)
                            current_length += word_len + space_len
                    
                    if current_line:  # Add the last line
                        wrapped_lines.append(' '.join(current_line))
            
            return '\n'.join(wrapped_lines)
        else:
            # Wrap text that doesn't already have newlines
            words = text.split()
            lines = []
            current_line = []
            current_length = 0
            
            for word in words:
                word_len = len(word)
                space_len = 1 if current_length > 0 else 0
                
                if current_length + word_len + space_len > max_chars:
                    if current_line:  # Add current line if it exists
                        lines.append(' '.join(current_line))
                    current_line = [word]
                    current_length = word_len
                else:
                    current_line.append(word)
                    current_length += word_len + space_len
            
            if current_line:  # Add the last line
                lines.append(' '.join(current_line))
            
            return '\n'.join(lines)

    # def add_text_with_bg_annotation(self, page, x_scaled, y_scaled, text):
    #     """Add text with background annotation to the PDF page with proper rotation handling."""
    #     try:
    #         annotation_data = None
    #         for (page_num, stored_x, stored_y), data in self.text_annotations_bg.items():
    #             if (page_num == page.number and 
    #                 abs(stored_x - x_scaled) < 1e-3 and 
    #                 abs(stored_y - y_scaled) < 1e-3):
    #                 annotation_data = data
    #                 break

    #         current_rotation = page.rotation
    #         insertion_rotation = 0
    #         base_x = x_scaled
    #         base_y = y_scaled
    #         if annotation_data and isinstance(annotation_data, dict):
    #             insertion_rotation = annotation_data.get("insertion_rotation", 0)
    #             base_x = annotation_data.get("base_x", x_scaled)
    #             base_y = annotation_data.get("base_y", y_scaled)

    #         rotation_diff = (current_rotation - insertion_rotation) % 360
    #         final_x = base_x
    #         final_y = base_y

    #         if rotation_diff != 0:
    #             page_width = page.rect.width
    #             page_height = page.rect.height
    #             center_x = page_width / 2
    #             center_y = page_height / 2
    #             tx = base_x - center_x
    #             ty = base_y - center_y
    #             if rotation_diff == 90:
    #                 rotated_x = -ty
    #                 rotated_y = tx
    #                 if insertion_rotation == 0 or insertion_rotation == 180:
    #                     rotated_x += 380
    #                     rotated_y += 380
    #                 elif insertion_rotation == 90 or insertion_rotation == 270:
    #                     rotated_x -= 380
    #                     rotated_y -= 380
    #             elif rotation_diff == 180:
    #                 rotated_x = -tx
    #                 rotated_y = -ty
    #             elif rotation_diff == 270:
    #                 rotated_x = ty
    #                 rotated_y = -tx
    #                 if insertion_rotation == 0 or insertion_rotation == 180:
    #                     rotated_x -= 380
    #                     rotated_y -= 380
    #                 elif insertion_rotation == 90 or insertion_rotation == 270:
    #                     rotated_x += 380
    #                     rotated_y += 380
    #             else:
    #                 rotated_x = tx
    #                 rotated_y = ty
    #             final_x = rotated_x + center_x
    #             final_y = rotated_y + center_y

    #         text_size = 18  # Default text size
    #         scaling_factor = max(page.rect.width, page.rect.height) / 1000
    #         adjusted_text_size = int(text_size * scaling_factor)
    #         padding = int(15 * scaling_factor)

    #         # Wrap text to fit within page boundaries
    #         max_width = page.rect.width - final_x - 20  # 20-unit buffer from edge
    #         wrapped_text = self.wrap_text_for_saving(text, max_width, adjusted_text_size)
    #         lines = wrapped_text.split('\n')
    #         max_line_length = max(len(line) for line in lines) if lines else 0
    #         actual_text_width = max_line_length * adjusted_text_size * 0.6
    #         text_height = len(lines) * adjusted_text_size * 1.2

    #         # Adjust rectangle and text coordinates based on rotation
    #         if rotation_diff == 0:
    #             rect_x1 = final_x - padding
    #             rect_y1 = final_y - padding
    #             rect_x2 = final_x + actual_text_width + padding
    #             rect_y2 = final_y + text_height + padding
    #             text_start_x = final_x
    #             text_start_y = final_y
    #         elif rotation_diff == 90:
    #             rect_x1 = final_x - text_height - padding
    #             rect_y1 = final_y - padding
    #             rect_x2 = final_x + padding
    #             rect_y2 = final_y + actual_text_width + padding
    #             text_start_x = final_x  # Start at left edge of rectangle
    #             text_start_y = final_y + padding # Offset to inside top
    #         elif rotation_diff == 180:
    #             rect_x1 = final_x - actual_text_width - padding
    #             rect_y1 = final_y - text_height - padding
    #             rect_x2 = final_x + padding
    #             rect_y2 = final_y + padding
    #             text_start_x = final_x
    #             text_start_y = final_y
    #         elif rotation_diff == 270:
    #             rect_x1 = final_x - padding
    #             rect_y1 = final_y - actual_text_width - padding
    #             rect_x2 = final_x + text_height + padding
    #             rect_y2 = final_y + padding
    #             text_start_x = final_x + padding  # Start at top edge of rectangle
    #             text_start_y = final_y
    #         else:
    #             rect_x1 = final_x - padding
    #             rect_y1 = final_y - padding
    #             rect_x2 = final_x + actual_text_width + padding
    #             rect_y2 = final_y + text_height + padding
    #             text_start_x = final_x
    #             text_start_y = final_y

    #         # Draw background rectangle
    #         page.draw_rect(
    #             rect=(rect_x1, rect_y1, rect_x2, rect_y2),
    #             color=(0, 1, 1),  # Cyan color
    #             fill=(0, 1, 1),
    #             fill_opacity=0.9
    #         )

    #         # Insert text with adjusted positioning to stay within rectangle
    #         for i, line in enumerate(lines):
    #             page.insert_text(
    #                 point=(text_start_x, text_start_y + (i * adjusted_text_size * 1.2)),
    #                 text=line,
    #                 fontsize=adjusted_text_size,
    #                 color=(0, 0, 0),
    #                 rotate=rotation_diff  # Apply rotation to text
    #             )

    #     except Exception as e:
    #         print(f"Error adding text with background annotation: {e}")


    def add_text_with_bg_annotation(self, page, x_scaled, y_scaled, text):
        """Add text with background annotation to the PDF page with proper rotation handling."""
        try:
            annotation_data = None
            for (page_num, stored_x, stored_y), data in self.text_annotations_bg.items():
                if (page_num == page.number and 
                    abs(stored_x - x_scaled) < 1e-3 and 
                    abs(stored_y - y_scaled) < 1e-3):
                    annotation_data = data
                    break

            current_rotation = page.rotation
            insertion_rotation = 0
            base_x = x_scaled
            base_y = y_scaled
            if annotation_data and isinstance(annotation_data, dict):
                insertion_rotation = annotation_data.get("insertion_rotation", 0)
                base_x = annotation_data.get("base_x", x_scaled)
                base_y = annotation_data.get("base_y", y_scaled)

            rotation_diff = (current_rotation - insertion_rotation) % 360
            final_x = base_x
            final_y = base_y

            if rotation_diff != 0:
                page_width = page.rect.width
                page_height = page.rect.height
                center_x = page_width / 2
                center_y = page_height / 2
                tx = base_x - center_x
                ty = base_y - center_y
                if rotation_diff == 90:
                    rotated_x = -ty
                    rotated_y = tx
                    if insertion_rotation == 0 or insertion_rotation == 180:
                        rotated_x += 380
                        rotated_y += 380
                    elif insertion_rotation == 90 or insertion_rotation == 270:
                        rotated_x -= 380
                        rotated_y -= 380
                elif rotation_diff == 180:
                    rotated_x = -tx
                    rotated_y = -ty
                elif rotation_diff == 270:
                    rotated_x = ty
                    rotated_y = -tx
                    if insertion_rotation == 0 or insertion_rotation == 180:
                        rotated_x -= 380
                        rotated_y -= 380
                    elif insertion_rotation == 90 or insertion_rotation == 270:
                        rotated_x += 380
                        rotated_y += 380
                else:
                    rotated_x = tx
                    rotated_y = ty
                final_x = rotated_x + center_x
                final_y = rotated_y + center_y

            text_size = 18  # Default text size
            scaling_factor = max(page.rect.width, page.rect.height) / 1000
            adjusted_text_size = int(text_size * scaling_factor)
            padding = int(15 * scaling_factor)

            # Wrap text to fit within page boundaries
            max_width = page.rect.width - final_x - 20  # 20-unit buffer from edge
            wrapped_text = self.wrap_text_for_saving(text, max_width, adjusted_text_size)
            lines = wrapped_text.split('\n')
            max_line_length = max(len(line) for line in lines) if lines else 0
            actual_text_width = max_line_length * adjusted_text_size * 0.6
            text_height = len(lines) * adjusted_text_size * 1.2

            # Adjust rectangle and text coordinates based on rotation
            if rotation_diff == 0:
                rect_x1 = final_x - padding
                rect_y1 = final_y - padding
                rect_x2 = final_x + actual_text_width + padding
                rect_y2 = final_y + text_height + padding
                text_start_x = final_x
                text_start_y = final_y
            elif rotation_diff == 90:
                rect_x1 = final_x - text_height - padding
                rect_y1 = final_y - padding
                rect_x2 = final_x + padding
                rect_y2 = final_y + actual_text_width + padding
                text_start_x = final_x  # Start at left edge of rectangle
                text_start_y = final_y + padding # Offset to inside top
            elif rotation_diff == 180:
                rect_x1 = final_x - actual_text_width - padding
                rect_y1 = final_y - text_height - padding
                rect_x2 = final_x + padding
                rect_y2 = final_y + padding
                text_start_x = final_x
                text_start_y = final_y
            elif rotation_diff == 270:
                rect_x1 = final_x - padding
                rect_y1 = final_y - actual_text_width - padding
                rect_x2 = final_x + text_height + padding
                rect_y2 = final_y + padding
                text_start_x = final_x + padding  # Start at top edge of rectangle
                text_start_y = final_y
            else:
                rect_x1 = final_x - padding
                rect_y1 = final_y - padding
                rect_x2 = final_x + actual_text_width + padding
                rect_y2 = final_y + text_height + padding
                text_start_x = final_x
                text_start_y = final_y

            # Draw background rectangle
            page.draw_rect(
                rect=(rect_x1, rect_y1, rect_x2, rect_y2),
                color=(0, 1, 1),  # Cyan color
                fill=(0, 1, 1),
                fill_opacity=0.9
            )

            # Determine correct rotation value (fix for 90/270 swap)
            if rotation_diff == 90:
                text_rotation = 270  # Use 270 instead of 90
            elif rotation_diff == 270:
                text_rotation = 90   # Use 90 instead of 270
            else:
                text_rotation = rotation_diff

            # Insert text with corrected rotation
            for i, line in enumerate(lines):
                page.insert_text(
                    point=(text_start_x, text_start_y + (i * adjusted_text_size * 1.2)),
                    text=line,
                    fontsize=adjusted_text_size,
                    color=(0, 0, 0),
                    rotate=text_rotation  # Apply corrected rotation to text
                )

        except Exception as e:
            print(f"Error adding text with background annotation: {e}")

                
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
    
    # def update_page_display(self):
    #     if self.pdf_document:
    #         total_pages = len(self.pdf_document)
    #         self.page_entry.delete(0, ctk.END)
    #         self.page_entry.insert(0, str(self.current_page + 1))  # One-based index
    #         self.page_total_label.configure(text=f"/ {total_pages}")

    def update_page_display(self):
        """Update the page entry and total pages display"""
        if self.pdf_document and hasattr(self, 'page_entry'):
            total_pages = len(self.pdf_document)
            current_page_display = self.current_page + 1  # Convert to 1-based index
            
            # Clear and update page entry with proper validation
            self.page_entry.delete(0, ctk.END)
            self.page_entry.insert(0, str(current_page_display))
            
            # Update total pages label
            if hasattr(self, 'page_total_label'):
                self.page_total_label.configure(text=f"/ {total_pages}")
            
            print(f"Page display updated: {current_page_display} / {total_pages}")  # Debug log

    def prev_page(self, event=None):
        """Go to the previous page in the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.current_page > 0:
            print(f"Page Width: {self.page_width}, Page Height: {self.page_height}")
            first_page = self.pdf_document[self.current_page]
            self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
            print(f"Page size: width {self.page_width} x hight {self.page_height}")
            global is_small_page
            if  self.page_width < 850 and self.page_height < 550:
                is_small_page = "very small"
            elif self.page_width < 1000:
                is_small_page = "yes"
            elif self.page_width <= 1500 and self.page_height < 1000:
                is_small_page = "smaller"
            elif self.page_width <= 1500 and self.page_height < 2000:
                is_small_page = "small"
            elif 2000 < self.page_width < 3000 and self.page_height > 2800:
                is_small_page = "longer"
            elif 3000 < self.page_width < 3500 and 2000 < self.page_height < 3000:
                is_small_page = "wider"
            elif 1000 <= self.page_width < 2500:
                is_small_page = "slightly"
            elif 2500 <= self.page_width < 3000:
                is_small_page = "maybe"
            elif 3000 <= self.page_width < 5000:
                is_small_page = "nope large"
            elif self.page_width >= 10000:
                is_small_page = "nope very large"
            else:
                is_small_page = "no"
            print("is_small_page----",is_small_page)
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
            print(f"Page Width: {self.page_width}, Page Height: {self.page_height}")
            first_page = self.pdf_document[self.current_page]
            self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
            print(f"Page size: width {self.page_width} x hight {self.page_height}")
            global is_small_page
            if  self.page_width < 850 and self.page_height < 550:
                is_small_page = "very small"
            elif self.page_width < 1000:
                is_small_page = "yes"
            elif self.page_width <= 1500 and self.page_height < 1000:
                is_small_page = "smaller"
            elif self.page_width <= 1500 and self.page_height < 2000:
                is_small_page = "small"
            elif 2000 < self.page_width < 3000 and self.page_height > 2800:
                is_small_page = "longer"
            elif 3000 < self.page_width < 3500 and 2000 < self.page_height < 3000:
                is_small_page = "wider"
            elif 1000 <= self.page_width < 2500:
                is_small_page = "slightly"
            elif 2500 <= self.page_width < 3000:
                is_small_page = "maybe"
            elif 3000 <= self.page_width < 5000:
                is_small_page = "nope large"
            elif self.page_width >= 10000:
                is_small_page = "nope very large"
            else:
                is_small_page = "no"
            print("is_small_page----",is_small_page)
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
        rotation_angle = page.rotation
        page.set_rotation((page.rotation + 90) % 360)
        self.render_page(self.current_page)

    def rotate_180clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        page.set_rotation((page.rotation + 180) % 360)
        self.render_page(self.current_page)

    def rotate_270clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        page.set_rotation((page.rotation + 270) % 360)
        self.render_page(self.current_page)

    def toggle_invert_colors(self):
        """Toggle color inversion for the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.is_inverted:
            self.invert_button.configure(fg_color="#00498f",hover_color="#023261")
        else:
            self.invert_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
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

    # def toggle_drawing(self):
    #     """Toggle the freehand drawing mode without embedding strokes into the PDF."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return

    #     if self.active_freehandline:
    #         self.canvas.unbind("<Button-1>")
    #         self.canvas.unbind("<B1-Motion>")
    #         self.canvas.unbind("<ButtonRelease-1>")
    #         self.active_freehandline = False
    #         self.draw_button.configure(fg_color="#00498f", hover_color="#023261")
    #         return

    #     self.active_freehandline = True
    #     self.draw_button.configure(fg_color="#d17a24", hover_color="#b56e26")
    #     self.deactivate_colour(self.draw_button,"active_freehandline")

    #     self.canvas.bind("<Button-1>", self.start_freehand_drawing)
    #     self.canvas.bind("<B1-Motion>", self.draw_freehand_line)
    #     self.canvas.bind("<ButtonRelease-1>", self.finish_freehand_drawing)


    # def start_freehand_drawing(self, event):
    #     """Start recording a freehand drawing stroke with unscaled coordinates."""
    #     self.freehand_stroke = [(event.x / self.zoom_factor, event.y / self.zoom_factor)]
    #     self.current_line = self.canvas.create_line(
    #         self.freehand_stroke[0][0] * self.zoom_factor,
    #         self.freehand_stroke[0][1] * self.zoom_factor,
    #         self.freehand_stroke[0][0] * self.zoom_factor,
    #         self.freehand_stroke[0][1] * self.zoom_factor, 
    #         fill="black" if not self.is_inverted else "white", width=2
    #     )

    # def draw_freehand_line(self, event):
    #     """Draw a freehand stroke in real-time with unscaled coordinates."""
    #     if not hasattr(self, "freehand_stroke"):
    #         return

    #     x, y = event.x / self.zoom_factor, event.y / self.zoom_factor
    #     page_width = self.page_width / self.zoom_factor
    #     page_height = self.page_height / self.zoom_factor

    #     # Ensure the stroke stays within the page bounds
    #     x = max(0, min(x, page_width))
    #     y = max(0, min(y, page_height))

    #     self.freehand_stroke.append((x, y))
    #     scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in self.freehand_stroke]
    #     self.canvas.coords(self.current_line, *sum(scaled_points, ()))

    # def finish_freehand_drawing(self, event):
    #     """Save the drawn freehand stroke for undo functionality without embedding into the PDF."""
    #     if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
    #         return
    #     self.freehand_drawings.append((self.current_page, self.current_line, self.freehand_stroke))
    #     self.change_history.append(("freehand", self.current_page, self.current_line, self.freehand_stroke))
    #     self.undo_change_history.append(("freehand", self.current_page, self.current_line, self.freehand_stroke))

    #     self.annotation_is_available = True
    #     self.render_page(self.current_page)  # Re-render to ensure it's drawn correctly
    #     self.redraw_freehand_drawings()
    #     self.annotation_listed.append("freehand")

    # def redraw_freehand_drawings(self):
    #     """Redraw all freehand drawings, applying zoom and rotation transformations."""
    #     self.canvas.delete("freehand")

    #     for i, entry in enumerate(self.change_history):
    #         if entry[0] == "freehand":
    #             _, page, old_line_id, points = entry
    #             if page != self.current_page:
    #                 continue

    #             transformed_points = [self.apply_transformations(x, y) for x, y in points]
    #             scaled_points = [(x * self.zoom_factor, y * self.zoom_factor) for x, y in transformed_points]
    #             fill_color = "black" if not self.is_inverted else "white"
    #             new_line_id = self.canvas.create_line(
    #                 *sum(scaled_points, ()),
    #                 fill=fill_color, width=3, tags="freehand"
    #             )

    #             # Update the change history with new line_id
    #             self.change_history[i] = ("freehand", page, new_line_id, points)

    #             # Also update the undo history so it matches
    #             for j, undo_entry in enumerate(self.undo_change_history):
    #                 if undo_entry[0] == "freehand" and undo_entry[1] == page and undo_entry[2] == old_line_id:
    #                     self.undo_change_history[j] = ("freehand", page, new_line_id, points)

    # def apply_transformations(self, x, y):
    #     """Apply rotation first, then zoom transformations to a given point."""
    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation
    #     page_width = self.page_width / self.zoom_factor  # Unscaled width
    #     page_height = self.page_height / self.zoom_factor  # Unscaled height

    #     # Apply rotation without zooming
    #     if rotation_angle == 90:
    #         if is_small_page == "yes":
    #             x, y = page_height+(180) - y, x
    #         elif is_small_page == "very small":
    #             print("buka buka very small")
    #             x, y = page_height+(80) - y, x
    #         elif is_small_page == "smaller":
    #             print("buka buka smaller")
    #             x, y = page_height+(-550) - y, x
    #         elif is_small_page == "small":
    #             print("buka buka small")
    #             x, y = page_height+(370) - y, x
    #         elif is_small_page == "slightly":
    #             x,y = page_height+(1050)-y,x
    #         elif is_small_page == "longer":
    #             x, y = page_height+(720) - y, x
    #         elif is_small_page == "maybe":
    #             x, y = page_height+(750) - y, x
    #         elif is_small_page == "nope large":
    #             x, y = page_height+(1000) - y, x
    #         elif is_small_page == "nope very large":
    #             x, y = page_height+(43000) - y, x
    #         else:
    #             x, y = page_height+(2000) - y, x
    #     elif rotation_angle == 180:
    #         x, y = page_width - x, page_height - y
    #     elif rotation_angle == 270:
    #         if is_small_page == "yes":
    #             x, y = y, page_width-(180) - x
    #         elif is_small_page == "very small":
    #             x, y = y, page_width-(80) - x
    #         elif is_small_page == "smaller":
    #             x, y = y, page_width-(-550) - x
    #         elif is_small_page == "small":
    #             x, y = y, page_width-(370) - x
    #         elif is_small_page == "slightly":
    #             x,y = y, page_width-(1050) - x
    #         elif is_small_page == "longer":
    #             x, y = y, page_width-(720) - x
    #         elif is_small_page == "maybe":
    #             x, y = y, page_width-(750) - x
    #         elif is_small_page == "nope large":
    #             x, y = y, page_width-(1000) - x
    #         elif is_small_page == "nope very large":
    #             x, y = y, page_width-(4300) - x
    #         else:
    #             x, y = y, page_width-(2000) - x
    #     return x, y

    # def toggle_drawing(self):
    #     """Toggle the freehand drawing mode without embedding strokes into the PDF."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return

    #     if self.active_freehandline:
    #         self.canvas.unbind("<Button-1>")
    #         self.canvas.unbind("<B1-Motion>")
    #         self.canvas.unbind("<ButtonRelease-1>")
    #         self.active_freehandline = False
    #         self.draw_button.configure(fg_color="#00498f", hover_color="#023261")
    #         return

    #     self.active_freehandline = True
    #     self.draw_button.configure(fg_color="#d17a24", hover_color="#b56e26")
    #     self.deactivate_colour(self.draw_button,"active_freehandline")

    #     self.canvas.bind("<Button-1>", self.start_freehand_drawing)
    #     self.canvas.bind("<B1-Motion>", self.draw_freehand_line)
    #     self.canvas.bind("<ButtonRelease-1>", self.finish_freehand_drawing)

    # def start_freehand_drawing(self, event):
    #     """Start recording a freehand drawing stroke with unscaled coordinates."""
    #     self.freehand_stroke = [(event.x / self.zoom_factor, event.y / self.zoom_factor)]
    #     self.current_line = self.canvas.create_line(
    #         self.freehand_stroke[0][0] * self.zoom_factor,
    #         self.freehand_stroke[0][1] * self.zoom_factor,
    #         self.freehand_stroke[0][0] * self.zoom_factor,
    #         self.freehand_stroke[0][1] * self.zoom_factor, 
    #         fill="black" if not self.is_inverted else "white", width=2)

    # def draw_freehand_line(self, event):
    #     """Draw a freehand stroke in real-time with unscaled coordinates."""
    #     if not hasattr(self, "freehand_stroke"):
    #         return
    #     x, y = event.x / self.zoom_factor, event.y / self.zoom_factor
    #     page_width = self.page_width / self.zoom_factor
    #     page_height = self.page_height / self.zoom_factor
    #     x = max(0, min(x, page_width))
    #     y = max(0, min(y, page_height))
    #     self.freehand_stroke.append((x, y))
    #     scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in self.freehand_stroke]
    #     self.canvas.coords(self.current_line, *sum(scaled_points, ()))

    # def finish_freehand_drawing(self, event):
    #     """Save the drawn freehand stroke for undo functionality without embedding into the PDF."""
    #     if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
    #         return
        
    #     # Convert canvas coordinates to PDF coordinates for storage
    #     pdf_points = []
    #     for canvas_x, canvas_y in self.freehand_stroke:
    #         pdf_coords = self.canvas_point_to_pdf_linecoordinates(canvas_x * self.zoom_factor, canvas_y * self.zoom_factor)
    #         pdf_points.append(pdf_coords)
        
    #     self.freehand_drawings.append((self.current_page, self.current_line, pdf_points))
    #     self.change_history.append(("freehand", self.current_page, self.current_line, pdf_points))
    #     self.undo_change_history.append(("freehand", self.current_page, self.current_line, pdf_points))
    #     self.annotation_is_available = True
    #     self.render_page(self.current_page) 
    #     # self.redraw_freehand_drawings()
    #     self.annotation_listed.append("freehand")

    def toggle_drawing(self):
        """Toggle the freehand drawing mode without embedding strokes into the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_freehandline:
            self.canvas.unbind("<Button-1>")
            self.canvas.unbind("<B1-Motion>")
            self.canvas.unbind("<ButtonRelease-1>")
            self.active_freehandline = False
            self.draw_button.configure(fg_color="#00498f", hover_color="#023261")
            # Reset drawing state when deactivating
            self.drawing_allowed = False
            return
        self.active_freehandline = True
        self.draw_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_colour(self.draw_button,"active_freehandline")
        # Initialize drawing state when activating
        self.drawing_allowed = False
        self.canvas.bind("<Button-1>", self.start_freehand_drawing)
        self.canvas.bind("<B1-Motion>", self.draw_freehand_line)
        self.canvas.bind("<ButtonRelease-1>", self.finish_freehand_drawing)

    def start_freehand_drawing(self, event):
        """Start recording a freehand drawing stroke with unscaled coordinates."""
        # Always initialize drawing_allowed to False first
        self.drawing_allowed = False
        
        # Clean up any existing stroke data
        if hasattr(self, "freehand_stroke"):
            del self.freehand_stroke
        if hasattr(self, "current_line"):
            try:
                self.canvas.delete(self.current_line)
            except:
                pass
        
        # Check if the initial click is within the canvas boundaries
        # Get the actual page dimensions on the canvas
        page_width_on_canvas = self.page_width
        page_height_on_canvas = self.page_height
        
        # Check if click is within the visible page area
        if (event.x < 0 or event.x > page_width_on_canvas or 
            event.y < 0 or event.y > page_height_on_canvas):
            # Click is outside the page area, ignore it completely
            return
        
        # Click is within bounds, allow drawing
        self.drawing_allowed = True
        self.freehand_stroke = [(event.x / self.zoom_factor, event.y / self.zoom_factor)]
        self.current_line = self.canvas.create_line(
            self.freehand_stroke[0][0] * self.zoom_factor,
            self.freehand_stroke[0][1] * self.zoom_factor,
            self.freehand_stroke[0][0] * self.zoom_factor,
            self.freehand_stroke[0][1] * self.zoom_factor, 
            fill="black" if not self.is_inverted else "white", width=2)

    def draw_freehand_line(self, event):
        """Draw a freehand stroke in real-time with unscaled coordinates."""
        # Always check if drawing is allowed - use getattr with default False
        if not getattr(self, "drawing_allowed", False):
            return
        
        # Check if freehand_stroke exists and is valid
        if not hasattr(self, "freehand_stroke") or not self.freehand_stroke:
            return
        
        # Check if current_line exists
        if not hasattr(self, "current_line"):
            return
        
        x, y = event.x / self.zoom_factor, event.y / self.zoom_factor
        page_width = self.page_width / self.zoom_factor
        page_height = self.page_height / self.zoom_factor
        x = max(0, min(x, page_width))
        y = max(0, min(y, page_height))
        self.freehand_stroke.append((x, y))
        scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in self.freehand_stroke]
        
        try:
            self.canvas.coords(self.current_line, *sum(scaled_points, ()))
        except:
            # If line doesn't exist, stop drawing
            self.drawing_allowed = False

    def finish_freehand_drawing(self, event):
        """Save the drawn freehand stroke for undo functionality without embedding into the PDF."""
        # Use getattr to safely check if drawing was allowed
        drawing_was_allowed = getattr(self, "drawing_allowed", False)
        
        # Always reset the drawing state first
        self.drawing_allowed = False
        
        # Only proceed if drawing was allowed to start
        if not drawing_was_allowed:
            # Clean up any partial state
            if hasattr(self, "freehand_stroke"):
                del self.freehand_stroke
            if hasattr(self, "current_line"):
                try:
                    self.canvas.delete(self.current_line)
                except:
                    pass
            return
        
        if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
            # Clean up incomplete strokes
            if hasattr(self, "freehand_stroke"):
                del self.freehand_stroke
            if hasattr(self, "current_line"):
                try:
                    self.canvas.delete(self.current_line)
                except:
                    pass
            return
        
        pdf_points = []
        for canvas_x, canvas_y in self.freehand_stroke:
            pdf_coords = self.canvas_point_to_pdf_linecoordinates(canvas_x * self.zoom_factor, canvas_y * self.zoom_factor)
            pdf_points.append(pdf_coords)
        self.freehand_drawings.append((self.current_page, self.current_line, pdf_points))
        self.change_history.append(("freehand", self.current_page, self.current_line, pdf_points))
        self.undo_change_history.append(("freehand", self.current_page, self.current_line, pdf_points))
        self.annotation_is_available = True
        self.render_page(self.current_page) 
        self.annotation_listed.append("freehand")
        
        # Clean up stroke data for next use
        if hasattr(self, "freehand_stroke"):
            del self.freehand_stroke

    def redraw_freehand_drawings(self):
        """Redraw all freehand drawings, applying zoom and rotation transformations."""
        self.canvas.delete("freehand")

        for i, entry in enumerate(self.change_history):
            if entry[0] == "freehand":
                _, page, old_line_id, points = entry
                if page != self.current_page:
                    continue

                transformed_points = [self.apply_transformations(x, y) for x, y in points]
                scaled_points = [(x * self.zoom_factor, y * self.zoom_factor) for x, y in transformed_points]
                fill_color = "black" if not self.is_inverted else "white"
                new_line_id = self.canvas.create_line(
                    *sum(scaled_points, ()),
                    fill=fill_color, width=3, tags="freehand"
                )

                # Update the change history with new line_id
                self.change_history[i] = ("freehand", page, new_line_id, points)

                # Also update the undo history so it matches
                for j, undo_entry in enumerate(self.undo_change_history):
                    if undo_entry[0] == "freehand" and undo_entry[1] == page and undo_entry[2] == old_line_id:
                        self.undo_change_history[j] = ("freehand", page, new_line_id, points)

    def apply_transformations(self, x, y):
        """Apply rotation first, then zoom transformations to a given point."""
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        page_width = self.page_width / self.zoom_factor  # Unscaled width
        page_height = self.page_height / self.zoom_factor  # Unscaled height

        # Apply rotation without zooming
        if rotation_angle == 90:
            if is_small_page == "yes":
                x, y = page_height+(180) - y, x
            elif is_small_page == "very small":
                print("buka buka very small")
                x, y = page_height+(80) - y, x
            elif is_small_page == "smaller":
                print("buka buka smaller")
                x, y = page_height+(-550) - y, x
            elif is_small_page == "small":
                print("buka buka small")
                x, y = page_height+(370) - y, x
            elif is_small_page == "slightly":
                x,y = page_height+(1050)-y,x
            elif is_small_page == "longer":
                x, y = page_height+(720) - y, x
            elif is_small_page == "maybe":
                x, y = page_height+(750) - y, x
            elif is_small_page == "nope large":
                x, y = page_height+(1000) - y, x
            elif is_small_page == "nope very large":
                x, y = page_height+(43000) - y, x
            else:
                x, y = page_height+(2000) - y, x
        elif rotation_angle == 180:
            x, y = page_width - x, page_height - y
        elif rotation_angle == 270:
            if is_small_page == "yes":
                x, y = y, page_width-(180) - x
            elif is_small_page == "very small":
                x, y = y, page_width-(80) - x
            elif is_small_page == "smaller":
                x, y = y, page_width-(-550) - x
            elif is_small_page == "small":
                x, y = y, page_width-(370) - x
            elif is_small_page == "slightly":
                x,y = y, page_width-(1050) - x
            elif is_small_page == "longer":
                x, y = y, page_width-(720) - x
            elif is_small_page == "maybe":
                x, y = y, page_width-(750) - x
            elif is_small_page == "nope large":
                x, y = y, page_width-(1000) - x
            elif is_small_page == "nope very large":
                x, y = y, page_width-(4300) - x
            else:
                x, y = y, page_width-(2000) - x
        return x, y

    def canvas_point_to_pdf_linecoordinates(self, canvas_x, canvas_y):
        """Convert a single canvas point to PDF coordinates accounting for rotation."""
        page = self.pdf_document[self.current_page]
        rotation = page.rotation
        original_rect = page.rect
        page_width = original_rect.width
        page_height = original_rect.height

        cx = canvas_x / self.zoom_factor
        cy = canvas_y / self.zoom_factor

        if rotation == 0:
            x, y = cx, cy
        elif rotation == 90:
            x, y = cy, page_width - cx
        elif rotation == 180:
            x, y = page_width - cx, page_height - cy
        elif rotation == 270:
            x, y = page_height - cy, cx
        
        return (x, y)
    
    def toggle_filled_polygon_mode(self):
        """Toggle filled polygon drawing mode."""
        if self.polygon_mode == "filled":
            self.filled_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")
            self.polygon_mode = None
            self.start_point = None
            self.polygon_created = False
            self.polygon_active = "no"
            self.active_filledpolygon = False
            self.canvas.unbind("<Button-1>")
            self.canvas.unbind("<ButtonRelease-1>")
            self.canvas.config(cursor="arrow")
            self.redraw_polygons()
            return

        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return

        if self.active_filledpolygon:
            self.canvas.unbind("<ButtonRelease-1>")
            self.canvas.config(cursor="arrow")
            self.hollow_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")
            self.active_filledpolygon = False
            return

        self.active_filledpolygon = True
        self.deactivate_tools()
        self.deactivate_colour(self.filled_polygon_button,"active_filledpolygon")

        if self.polygon_mode == "hollow":
            self.hollow_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")

        self.filled_polygon_button.configure(text="#", fg_color="#d17a24", hover_color="#b56e26")
        self.polygon_active = "yes"
        self.polygon_mode = "filled"
        self.start_point = None
        self.polygon_created = False
        self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)

    def toggle_hollow_polygon_mode(self):
        """Toggle hollow polygon drawing mode."""
        if self.polygon_mode == "hollow":
            self.hollow_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")
            self.polygon_mode = None
            self.start_point = None
            self.polygon_created = False
            self.polygon_active = "no"
            self.active_hollowpolgon = False
            self.canvas.unbind("<Button-1>")
            self.canvas.unbind("<ButtonRelease-1>")
            self.canvas.config(cursor="arrow")
            self.redraw_polygons()
            return
        
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        
        if self.active_hollowpolgon:
            self.canvas.unbind("<ButtonRelease-1>")
            self.canvas.config(cursor="arrow")
            self.filled_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")
            self.active_hollowpolgon = False
            return
        
        self.active_hollowpolgon = True
        self.deactivate_tools()
        self.deactivate_colour(self.hollow_polygon_button,"active_hollowpolgon")
        
        if self.polygon_mode == "filled":
            self.filled_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")
        
        self.hollow_polygon_button.configure(text="#", fg_color="#d17a24", hover_color="#b56e26")
        self.polygon_active = "yes"
        self.polygon_mode = "hollow"
        self.start_point = None
        self.polygon_created = False
        self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)

    def is_point_inside_polygon(self, x, y, points):
        """Check if a point is inside a polygon using ray casting algorithm."""
        if len(points) < 6:  # Need at least 3 points (6 coordinates)
            return False
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

    
    def on_canvas_polygon_click(self, event):
        """Handle canvas clicks for creating polygons and detecting vertex/polygon dragging."""
        if not self.polygon_mode or not self.pdf_document:
            return
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        if canvas_x < 0 or canvas_x > self.page_width or canvas_y < 0 or canvas_y > self.page_height:
            return
        if not hasattr(self, 'polygon_annotations'):
            self.polygon_annotations = {}
        if self.current_page not in self.polygon_annotations:
            self.polygon_annotations[self.current_page] = []
        
        # Check vertex drag FIRST with higher priority
        vertex_found = self.check_vertex_drag(canvas_x, canvas_y)
        if vertex_found:
            return
        
        # Only check polygon drag if no vertex was found
        polygon_found = self.check_polygon_drag(canvas_x, canvas_y)
        if polygon_found:
            return
        
        self.create_new_polygon(canvas_x, canvas_y)


    def check_vertex_drag(self, canvas_x, canvas_y):
        """Check if click is near a vertex for vertex dragging with very precise detection."""
        # Much smaller vertex tolerance - only activate when very close to the exact corner
        vertex_tolerance = max(4, 6 / self.zoom_factor)  # Very small area for precise vertex selection
        
        for polygon_idx, polygon_data in enumerate(self.polygon_annotations[self.current_page]):
            display_points = self.get_polygon_display_points(polygon_data)
            
            # Check each vertex with precise detection
            for vertex_idx in range(0, len(display_points), 2):
                vertex_x = display_points[vertex_idx]
                vertex_y = display_points[vertex_idx + 1]
                
                distance = ((vertex_x - canvas_x) ** 2 + (vertex_y - canvas_y) ** 2) ** 0.5
                
                if distance < vertex_tolerance:
                    self.dragging_vertex = {
                        'polygon_idx': polygon_idx,
                        'vertex_idx': vertex_idx // 2,
                        'polygon_data': polygon_data,
                        'original_base_points': polygon_data['base_points'].copy()  # Store original points
                    }
                    self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
                    self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                    self.canvas.config(cursor="crosshair")
                    return True
        return False

    def check_polygon_drag(self, canvas_x, canvas_y):
        """Check if click is inside a polygon for whole polygon dragging with minimal vertex exclusion."""
        # Small exclusion zone around vertices - just enough to avoid conflicts
        vertex_exclusion_tolerance = max(5, 7 / self.zoom_factor)  # Minimal exclusion zone
        
        for polygon_idx, polygon_data in enumerate(self.polygon_annotations[self.current_page]):
            display_points = self.get_polygon_display_points(polygon_data)
            
            # Check if we're too close to any vertex (minimal exclusion zone)
            near_vertex = False
            for vertex_idx in range(0, len(display_points), 2):
                vertex_x = display_points[vertex_idx]
                vertex_y = display_points[vertex_idx + 1]
                
                distance = ((vertex_x - canvas_x) ** 2 + (vertex_y - canvas_y) ** 2) ** 0.5
                
                if distance < vertex_exclusion_tolerance:
                    near_vertex = True
                    break
            
            # Allow polygon drag if we're not too close to vertices AND inside the polygon
            if not near_vertex and self.is_point_inside_polygon(canvas_x, canvas_y, display_points):
                self.dragging_polygon = {
                    'polygon_idx': polygon_idx,
                    'polygon_data': polygon_data,
                    'start_x': canvas_x,
                    'start_y': canvas_y,
                    'original_base_points': polygon_data['base_points'].copy()  # Store original points
                }
                self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
                self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                self.canvas.config(cursor="fleur")
                return True
        return False

    def create_new_polygon(self, canvas_x, canvas_y):
        """Create a new polygon at the clicked location."""
        # Convert to PDF coordinates
        x_scaled, y_scaled = self.canvas_point_to_pdf_coordinates(canvas_x, canvas_y)
        
        # Get current page and rotation
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        
        # Generate polygon points in PDF coordinates
        radius = self.polygon_size / self.zoom_factor
        points = self.generate_polygon_points(x_scaled, y_scaled, radius, 5)
        
        # Store polygon annotation data
        polygon_id = f"polygon_{self.current_page}_{len(self.polygon_annotations[self.current_page])}"
        
        polygon_data = {
            "mode": self.polygon_mode,
            "points": points,
            "base_points": points.copy(),
            "insertion_rotation": current_rotation,
            "polygon_id": polygon_id
        }
        
        self.polygon_annotations[self.current_page].append(polygon_data)
        
        # Add to history
        self.change_history.append(("add_polygon", self.current_page, x_scaled, y_scaled, self.polygon_mode, points))
        self.undo_change_history.append(("add_polygon", self.current_page, x_scaled, y_scaled, self.polygon_mode, points))
        self.annotation_listed.append("polygon")
        
        # Set annotation available flag
        self.annotation_is_available = True
        
        # Redraw to show the new polygon
        self.redraw_polygons()

    def canvas_point_to_pdf_coordinates(self, canvas_x, canvas_y):
        """Convert a single canvas point to PDF coordinates WITHOUT rotation compensation."""
        pdf_x = canvas_x / self.zoom_factor
        pdf_y = canvas_y / self.zoom_factor
        return pdf_x, pdf_y

    def canvas_point_to_pdf_coordinates_with_rotation(self, canvas_x, canvas_y, insertion_rotation=0):
        """Convert canvas point to PDF coordinates WITH rotation compensation."""
        if not self.pdf_document:
            return self.canvas_point_to_pdf_coordinates(canvas_x, canvas_y)
        
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        
        # Calculate the rotation difference from when polygon was inserted
        rotation_diff = (current_rotation - insertion_rotation) % 360
        
        # If no rotation difference, use simple conversion
        if rotation_diff == 0:
            return self.canvas_point_to_pdf_coordinates(canvas_x, canvas_y)
        
        # Apply inverse rotation to get the original PDF coordinates
        center_x = self.page_width / 2
        center_y = self.page_height / 2
        
        # Translate to center
        tx = canvas_x - center_x
        ty = canvas_y - center_y
        
        # Apply inverse rotation based on rotation difference
        if rotation_diff == 90:
            # Inverse of 90° rotation is -90° (or 270°)
            rotated_x = ty
            rotated_y = -tx
        elif rotation_diff == 180:
            # Inverse of 180° rotation is 180°
            rotated_x = -tx
            rotated_y = -ty
        elif rotation_diff == 270:
            # Inverse of 270° rotation is -270° (or 90°)
            rotated_x = -ty
            rotated_y = tx
        else:
            rotated_x = tx
            rotated_y = ty
        
        # Translate back and convert to PDF coordinates
        final_canvas_x = rotated_x + center_x
        final_canvas_y = rotated_y + center_y
        
        return self.canvas_point_to_pdf_coordinates(final_canvas_x, final_canvas_y)

    def get_polygon_display_points(self, polygon_data):
        """Get polygon points as they should be displayed on canvas (with rotation)."""
        if not self.pdf_document:
            return [coord * self.zoom_factor for coord in polygon_data["base_points"]]
        
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        insertion_rotation = polygon_data.get("insertion_rotation", 0)
        rotation_diff = (current_rotation - insertion_rotation) % 360
        
        base_points = polygon_data["base_points"]
        
        if rotation_diff == 0:
            # No rotation needed, just scale
            scaled_points = [coord * self.zoom_factor for coord in base_points]
            return scaled_points
        else:
            # Apply rotation transformation
            rotated_points = []
            for i in range(0, len(base_points), 2):
                x_scaled = base_points[i] * self.zoom_factor
                y_scaled = base_points[i + 1] * self.zoom_factor
                
                rotated_x, rotated_y = self.apply_polygon_rotation_to_point(
                    x_scaled, y_scaled, self.page_width, self.page_height, 
                    rotation_diff, insertion_rotation)
                
                rotated_points.extend([rotated_x, rotated_y])
            
            return rotated_points

    def apply_polygon_rotation_to_point(self, x, y, page_width, page_height, rotation_angle, insertion_rotation):
        """Apply rotation transformation to polygon point (similar to text rotation)."""
        if rotation_angle == 0:
            return x, y
        
        center_x = page_width / 2
        center_y = page_height / 2
        
        # Translate to center
        tx = x - center_x
        ty = y - center_y
        
        # Apply rotation
        if rotation_angle == 90:
            rotated_x = -ty
            rotated_y = tx
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x += (380 * self.zoom_factor)
                rotated_y += (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x += (-380 * self.zoom_factor)
                rotated_y += (-380 * self.zoom_factor)
        elif rotation_angle == 180:
            rotated_x = -tx
            rotated_y = -ty
        elif rotation_angle == 270:
            rotated_x = ty
            rotated_y = -tx
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x -= (380 * self.zoom_factor)
                rotated_y -= (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x -= (-380 * self.zoom_factor)
                rotated_y -= (-380 * self.zoom_factor)
        else:
            rotated_x = tx
            rotated_y = ty
        
        # Translate back
        final_x = rotated_x + center_x
        final_y = rotated_y + center_y
        
        return final_x, final_y

    def on_polygon_drag_vertex(self, event):
        """Handle vertex dragging with corrected rotation compensation."""
        if not hasattr(self, 'dragging_vertex'):
            return
        
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        
        # Keep within canvas bounds
        canvas_x = max(0, min(canvas_x, self.page_width))
        canvas_y = max(0, min(canvas_y, self.page_height))
        
        polygon_data = self.dragging_vertex['polygon_data']
        vertex_idx = self.dragging_vertex['vertex_idx']
        
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        insertion_rotation = polygon_data.get("insertion_rotation", 0)
        rotation_diff = (current_rotation - insertion_rotation) % 360
        
        # Convert canvas coordinates to PDF coordinates
        pdf_x, pdf_y = self.canvas_point_to_pdf_coordinates(canvas_x, canvas_y)
        
        # Apply inverse rotation if needed to get the base coordinates
        if rotation_diff != 0:
            center_x = self.page_width / (2 * self.zoom_factor)
            center_y = self.page_height / (2 * self.zoom_factor)
            
            # Translate to origin
            tx = pdf_x - center_x
            ty = pdf_y - center_y
            
            # Apply inverse rotation
            if rotation_diff == 90:
                # For 90° rotation, inverse is -90° (or 270°)
                unrotated_x = ty
                unrotated_y = -tx
            elif rotation_diff == 180:
                # For 180° rotation, inverse is 180°
                unrotated_x = -tx
                unrotated_y = -ty
            elif rotation_diff == 270:
                # For 270° rotation, inverse is -270° (or 90°)
                unrotated_x = -ty
                unrotated_y = tx
            else:
                unrotated_x = tx
                unrotated_y = ty
            
            # Translate back
            final_x = unrotated_x + center_x
            final_y = unrotated_y + center_y
        else:
            final_x = pdf_x
            final_y = pdf_y
        
        # Update the vertex position in base coordinates
        polygon_data['base_points'][vertex_idx * 2] = final_x
        polygon_data['base_points'][vertex_idx * 2 + 1] = final_y
        
        self.redraw_polygons()

    def apply_inverse_rotation_to_point(self, x, y, rotation_diff):
        """Apply inverse rotation to convert rotated canvas coordinates back to base coordinates."""
        center_x = self.page_width / (2 * self.zoom_factor)
        center_y = self.page_height / (2 * self.zoom_factor)
        
        # Translate to origin
        tx = x - center_x
        ty = y - center_y
        
        # Apply inverse rotation
        if rotation_diff == 90:
            # Inverse of 90° is -90° (or 270°)
            x_new = center_x + ty
            y_new = center_y - tx
        elif rotation_diff == 180:
            # Inverse of 180° is 180°
            x_new = center_x - tx
            y_new = center_y - ty
        elif rotation_diff == 270:
            # Inverse of 270° is -270° (or 90°)
            x_new = center_x - ty
            y_new = center_y + tx
        else:
            x_new = x
            y_new = y
        
        return x_new, y_new
    
    def on_polygon_drag_entire(self, event):
        """Handle dragging the entire polygon with improved rotation compensation."""
        if not hasattr(self, 'dragging_polygon'):
            return
        
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        
        polygon_data = self.dragging_polygon['polygon_data']
        start_x = self.dragging_polygon['start_x']
        start_y = self.dragging_polygon['start_y']
        
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        insertion_rotation = polygon_data.get("insertion_rotation", 0)
        rotation_diff = (current_rotation - insertion_rotation) % 360
        
        # Convert canvas coordinates to PDF coordinates
        start_pdf_x, start_pdf_y = self.canvas_point_to_pdf_coordinates(start_x, start_y)
        current_pdf_x, current_pdf_y = self.canvas_point_to_pdf_coordinates(canvas_x, canvas_y)
        
        # Calculate movement delta in PDF coordinates
        if rotation_diff != 0:
            # Apply inverse rotation to both start and current positions
            start_adj_x, start_adj_y = self.apply_inverse_rotation_to_point(start_pdf_x, start_pdf_y, rotation_diff)
            end_adj_x, end_adj_y = self.apply_inverse_rotation_to_point(current_pdf_x, current_pdf_y, rotation_diff)
        else:
            start_adj_x, start_adj_y = start_pdf_x, start_pdf_y
            end_adj_x, end_adj_y = current_pdf_x, current_pdf_y
        
        # Calculate the movement delta
        dx = end_adj_x - start_adj_x
        dy = end_adj_y - start_adj_y
        
        # Apply the delta to all vertices
        base_points = polygon_data['base_points']
        for i in range(0, len(base_points), 2):
            base_points[i] += dx
            base_points[i + 1] += dy
        
        # Update the start position for next iteration
        self.dragging_polygon['start_x'] = canvas_x
        self.dragging_polygon['start_y'] = canvas_y
        
        self.redraw_polygons()


    def on_polygon_drag_release(self, event):
        """Release polygon or vertex dragging and clean up."""
        # Clean up dragging state
        if hasattr(self, 'dragging_vertex'):
            del self.dragging_vertex
        if hasattr(self, 'dragging_polygon'):
            del self.dragging_polygon
        
        # Unbind motion events and reset cursor
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.canvas.config(cursor="arrow")
        
        # Rebind the original click handler for polygon creation
        self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)

    def redraw_polygons(self):
        """Redraw all polygons with consistent rotation logic like text annotations."""
        if not self.pdf_document or self.current_page is None:
            return
        
        # Clear existing polygons
        self.canvas.delete("polygon")
        
        # Initialize if needed
        if not hasattr(self, 'polygon_annotations'):
            self.polygon_annotations = {}
        
        if self.current_page not in self.polygon_annotations:
            return
        
        # Draw each polygon
        for polygon_data in self.polygon_annotations[self.current_page]:
            display_points = self.get_polygon_display_points(polygon_data)
            
            if len(display_points) < 6:  # Need at least 3 points
                continue
            
            # Create polygon on canvas
            fill_color = "blue" if polygon_data["mode"] == "filled" else ""
            outline_color = "blue" if polygon_data["mode"] == "filled" else "red"
            
            polygon_id = self.canvas.create_polygon(
                display_points,
                fill=fill_color,
                outline=outline_color,
                width=4,
                tags=("polygon",)
            )
            
            # Update the canvas_id in polygon_data
            polygon_data["canvas_id"] = polygon_id


    # def toggle_hollow_polygon_mode(self):
    #     """Toggle hollow polygon drawing mode."""
    #     if self.polygon_mode == "hollow":
    #         self.hollow_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")
    #         self.polygon_mode = None
    #         self.start_point = None
    #         self.polygon_created = False
    #         self.polygon_active = "no"
    #         self.active_hollowpolgon = False
    #         self.canvas.unbind("<Button-1>")
    #         self.canvas.unbind("<ButtonRelease-1>")
    #         self.canvas.config(cursor="arrow")
    #         self.redraw_polygons()
    #         return

    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
    #         return

    #     if self.active_hollowpolgon:
    #         self.canvas.unbind("<ButtonRelease-1>")
    #         self.canvas.config(cursor="arrow")
    #         self.filled_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")
    #         self.active_hollowpolgon = False
    #         return

    #     self.active_hollowpolgon = True
    #     self.deactivate_tools()
    #     self.deactivate_colour(self.hollow_polygon_button,"active_hollowpolgon")

    #     if self.polygon_mode == "filled":
    #         self.filled_polygon_button.configure(text="", fg_color="#00498f", hover_color="#023261")

    #     self.hollow_polygon_button.configure(text="#", fg_color="#d17a24", hover_color="#b56e26")
    #     self.polygon_active = "yes"
    #     self.polygon_mode = "hollow"
    #     self.start_point = None
    #     self.polygon_created = False
    #     self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)



    # def is_point_inside_polygon(self, x, y, points):
    #     num_points = len(points) // 2
    #     polygon = [(points[i * 2], points[i * 2 + 1]) for i in range(num_points)]
    #     inside = False

    #     for i in range(num_points):
    #         x1, y1 = polygon[i]
    #         x2, y2 = polygon[(i + 1) % num_points]

    #         if ((y1 > y) != (y2 > y)) and (x < (x2 - x1) * (y - y1) / (y2 - y1) + x1):
    #             inside = not inside

    #     return inside

    # def generate_polygon_points(self, x, y, radius, sides):
    #     """Generate the points of a regular polygon with given sides and radius."""
    #     points = []
    #     for i in range(sides):
    #         angle = 2 * math.pi * i / sides
    #         px = x + radius * math.cos(angle)
    #         py = y + radius * math.sin(angle)
    #         points.append(px)
    #         points.append(py)
    #     return points

    # def on_canvas_polygon_click(self, event):
    #     """Handle canvas clicks for creating or modifying polygons."""
    #     if not self.polygon_mode:
    #         return
        
    #     # Convert the click position to PDF space
    #     x = self.canvas.canvasx(event.x) / self.zoom_factor
    #     y = self.canvas.canvasy(event.y) / self.zoom_factor

    #     if self.current_page not in self.page_drawings:
    #         self.page_drawings[self.current_page] = []

    #     for idx, drawing in enumerate(self.page_drawings[self.current_page]):
    #         if len(drawing) != 3:
    #             continue

    #         mode, points, polygon_id = drawing

    #         if self.is_point_inside_polygon(x, y, points):
    #             self.canvas.config(cursor="hand2")

    #             # Convert the zoom factor correctly for dragging
    #             zoom_adjusted_radius = max(10, 15 / self.zoom_factor)
    #             for i in range(0, len(points), 2):
    #                 vx, vy = points[i], points[i + 1]
    #                 if abs(vx - x) < zoom_adjusted_radius and abs(vy - y) < zoom_adjusted_radius:
    #                     self.dragging_polygon = (idx, i // 2)
    #                     self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
    #                     self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
    #                     self.canvas.config(cursor="fleur")
    #                     return

    #             self.dragging_polygon = (idx, None)
    #             self.start_drag_x, self.start_drag_y = x, y
    #             self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
    #             self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
    #             self.canvas.config(cursor="fleur")
    #             return

    #     # If a new polygon needs to be created
    #     if self.start_point is None:
    #         self.start_point = (x, y)

    #         points = self.generate_polygon_points(
    #             x, y, 
    #             self.polygon_size / self.zoom_factor, 
    #             5
    #         )

    #         # Scale points back for display on the canvas
    #         scaled_points = [coord * self.zoom_factor for coord in points]

    #         polygon_id = self.canvas.create_polygon(
    #             scaled_points,
    #             fill="blue" if self.polygon_mode == "filled" else "",
    #             outline="blue" if self.polygon_mode == "filled" else "red",
    #             tags=("polygon",)
    #         )

    #         self.page_drawings[self.current_page].append((self.polygon_mode, points, polygon_id))
    #         self.polygon_cord.append((self.current_page, polygon_id, points))
    #         self.polygon_mode_created.append((polygon_id , self.polygon_mode))
    #         self.change_history.append(("polygon", self.current_page, points, polygon_id))
    #         self.undo_change_history.append(("polygon", self.current_page, points, polygon_id))
    #         self.annotation_listed.append("polygon")
    #     else:
    #         self.start_point = None

    #     self.redraw_polygons()

    # def embed_polygons_in_pdf(self):
    #     """Embed only existing polygons in the PDF with proper scaling."""
    #     if not self.pdf_document or self.current_page not in self.page_drawings:
    #         return  # No valid PDF or no drawings on the current page

    #     page = self.pdf_document[self.current_page]
        
    #     # Remove old polygon annotations before embedding new ones
    #     for annot in page.annots():
    #         if annot.info.get("title") == "polygon_annotation":
    #             annot.delete()

    #     zoom_matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
    #     self.annotation_is_available = True

    #     # Ensure only non-removed polygons get embedded
    #     remaining_polygons = []
        
    #     for drawing in self.page_drawings[self.current_page]:  
    #         if len(drawing) != 3:
    #             print(f"Skipping invalid entry: {drawing}")
    #             continue

    #         mode, points, polygon_id = drawing

    #         # Check if this polygon has been removed via undo
    #         if self.current_page in self.embedded_polygons:
    #             if any(p[2] == polygon_id for p in self.embedded_polygons[self.current_page]):
    #                 continue  # Skip embedding removed polygons

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

    #         remaining_polygons.append(drawing)  # Only keep actually embedded polygons

    #     self.embedded_polygons[self.current_page] = remaining_polygons  # Update embedded list
       

    # def on_polygon_drag_vertex(self, event):
    #     if not hasattr(self, 'dragging_polygon'):
    #         return

    #     idx, vertex_idx = self.dragging_polygon
    #     if vertex_idx is None:
    #         return

    #     mode, points, polygon_id = self.page_drawings[self.current_page][idx]
    #     x = self.canvas.canvasx(event.x) / self.zoom_factor
    #     y = self.canvas.canvasy(event.y) / self.zoom_factor

    #     x = max(0, min(x, self.page_width / self.zoom_factor))
    #     y = max(0, min(y, self.page_height / self.zoom_factor))

    #     points[vertex_idx * 2] = x
    #     points[vertex_idx * 2 + 1] = y

    #     scaled_points = [p * self.zoom_factor for p in points]
    #     self.canvas.coords(polygon_id, *scaled_points)


    # def on_polygon_drag_entire(self, event):
    #     if not hasattr(self, 'dragging_polygon'):
    #         return
    #     idx, _ = self.dragging_polygon
    #     mode, points, polygon_id = self.page_drawings[self.current_page][idx]
    #     x, y = self.canvas.canvasx(event.x) / self.zoom_factor, self.canvas.canvasy(event.y) / self.zoom_factor
    #     dx, dy = x - self.start_drag_x, y - self.start_drag_y

    #     # Constrain entire polygon to remain inside the page boundary
    #     min_x = min(points[::2]) + dx
    #     min_y = min(points[1::2]) + dy
    #     max_x = max(points[::2]) + dx
    #     max_y = max(points[1::2]) + dy

    #     if min_x < 0 or max_x > self.page_width / self.zoom_factor or min_y < 0 or max_y > self.page_height / self.zoom_factor:
    #         return  # Prevent movement outside the page

    #     for i in range(0, len(points), 2):
    #         points[i] += dx
    #         points[i + 1] += dy

    #     scaled_points = [(p * self.zoom_factor) for p in points]
    #     self.canvas.coords(polygon_id, scaled_points)

    #     self.start_drag_x, self.start_drag_y = x, y


    # def on_polygon_drag_release(self, event):
    #     """Release the polygon after dragging."""
    #     if hasattr(self, 'dragging_polygon'):
    #         del self.dragging_polygon
    #     self.canvas.unbind("<B1-Motion>")
    #     self.canvas.unbind("<ButtonRelease-1>")
    #     self.redraw_polygons()




    # def attach_image_to_pdf(self):
    #     """Attach an image to the currently loaded PDF with interactive placement and resizing."""
    #     if not self.pdf_document:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
    #     self.deactivate_tools()
    #     self.deactivate_colour(self.image_button)
    #     self.image_button.configure(fg_color="#d17a24", hover_color="#b56e26") 
    #     image_path = filedialog.askopenfilename(
    #         title="Select an Image",
    #         filetypes=[("Image Files", "*.png;*.jpg;*.jpeg"), ("All Files", "*.*")])
            
    #     if not image_path:
    #         self.image_button.configure(fg_color="#00498f", hover_color="#023261")
    #         return  # User canceled the dialog       
    #     try:
    #         img = Image.open(image_path)
    #         img.thumbnail((200, 200), Image.LANCZOS)  # Initial size
    #         self.tk_image = ImageTk.PhotoImage(img)  # Convert to Tkinter-compatible format
            
    #         # Create the image on canvas
    #         self.active_image = self.canvas.create_image(
    #             100, 100, 
    #             image=self.tk_image, 
    #             anchor="nw", 
    #             tags="temp_image_overlay"
    #         )
            
    #         # Store the image data for manipulation
    #         self.image_data = {
    #             "id": f"img_{len(self.image_overlays)}",
    #             "image_path": image_path,
    #             "image_obj": img,
    #             "x": 100, "y": 100,
    #             "width": img.width, "height": img.height,
    #             "base_x": 100 / self.zoom_factor,  # Store unscaled coordinates
    #             "base_y": 100 / self.zoom_factor,
    #             "base_width": img.width / self.zoom_factor,
    #             "base_height": img.height / self.zoom_factor,
    #             "page": self.current_page
    #         }
            
    #         # Bind events for manipulation
    #         self.canvas.tag_bind(self.active_image, "<ButtonPress-1>", self.start_move)
    #         self.canvas.tag_bind(self.active_image, "<B1-Motion>", self.do_move)
    #         self.canvas.tag_bind(self.active_image, "<ButtonRelease-1>", self.finalize_move)
    #         self.canvas.bind_all("<MouseWheel>", self.resize_image)
            
    #     except Exception as e:
    #         messagebox.showerror("Error", f"Failed to load image: {str(e)}")

    # def start_move(self, event):
    #     """Start dragging the image."""
    #     self.image_data["start_x"] = event.x
    #     self.image_data["start_y"] = event.y

    # def do_move(self, event):
    #     """Move the image as the mouse drags."""
    #     dx = event.x - self.image_data["start_x"]
    #     dy = event.y - self.image_data["start_y"]
        
    #     self.canvas.move(self.active_image, dx, dy)
    #     self.image_data["x"] += dx
    #     self.image_data["y"] += dy
        
    #     # Update base coordinates (unscaled)
    #     self.image_data["base_x"] = self.image_data["x"] / self.zoom_factor
    #     self.image_data["base_y"] = self.image_data["y"] / self.zoom_factor
        
    #     self.image_data["start_x"] = event.x
    #     self.image_data["start_y"] = event.y

    # def finalize_move(self, event):
    #     """Finalize the image overlay position."""
    #     user_response = messagebox.askyesnocancel(
    #         "Confirm Position",
    #         "Are you satisfied with the current position and size of the image? To Resize hold shift and scroll")
            
    #     if user_response is None:  # User clicked 'Cancel'
    #         self.canvas.delete(self.active_image)  # Remove the temporary image from canvas
    #         self.active_image = None
    #         self.image_data = None
    #         self.image_button.configure(fg_color="#00498f", hover_color="#023261")
    #         return
            
    #     if not user_response:  # User clicked 'No', allow them to move/reshape again
    #         return  # Do nothing, letting them continue adjusting the image
        
    #     self.annotation_is_available = True
        
    #     try:
    #         # Create the final overlay information
    #         overlay_info = {
    #             "id": self.image_data["id"],
    #             "type": "image_overlay",
    #             "image_path": self.image_data["image_path"],
    #             "x": self.image_data["x"],
    #             "y": self.image_data["y"],
    #             "width": self.image_data["width"],
    #             "height": self.image_data["height"],
    #             "base_x": self.image_data["base_x"],
    #             "base_y": self.image_data["base_y"],
    #             "base_width": self.image_data["base_width"],
    #             "base_height": self.image_data["base_height"],
    #             "page": self.current_page,
    #             "canvas_id": self.active_image
    #         }
            
    #         # Add to image overlays list and change history
    #         self.image_overlays.append(overlay_info)
    #         self.change_history.append(("image_overlay", self.current_page, overlay_info))
    #         self.undo_change_history.append(("image_overlay", self.current_page, overlay_info))
            
    #         # Remove the temporary image and redraw it as a permanent one
    #         self.canvas.delete("temp_image_overlay")
    #         self.redraw_image_overlays(self.current_page)
            
    #         # Unbind events - this prevents the image from being moved after finalization
    #         self.canvas.unbind_all("<MouseWheel>")
    #         self.active_image = None
    #         self.annotation_listed.append("image_overlay")
    #         self.image_button.configure(fg_color="#00498f", hover_color="#023261")
    #     except Exception as e:
    #         messagebox.showerror("Error", f"Failed to add image overlay: {e}")

    # def resize_image(self, event):
    #     """Resize the image using the mouse scroll."""
    #     if event.state & 0x0001 == 0:
    #         return  # Shift not pressed; ignore scroll
            
    #     scale_factor = 1.1 if event.delta > 0 else 0.9
        
    #     # Calculate new width and height
    #     new_width = int(self.image_data["width"] * scale_factor)
    #     new_height = int(self.image_data["height"] * scale_factor)
        
    #     # Prevent the image from becoming too small
    #     if new_width < 50 or new_height < 50:
    #         return
            
    #     # Update image data
    #     self.image_data["width"] = new_width
    #     self.image_data["height"] = new_height
    #     self.image_data["base_width"] = new_width / self.zoom_factor
    #     self.image_data["base_height"] = new_height / self.zoom_factor
        
    #     # Resize the image
    #     img_resized = self.image_data["image_obj"].resize((new_width, new_height), Image.LANCZOS)
    #     self.tk_image = ImageTk.PhotoImage(img_resized)
    #     self.canvas.itemconfig(self.active_image, image=self.tk_image)


    def attach_image_to_pdf(self):
        """Attach an image to the currently loaded PDF with interactive placement and resizing."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.deactivate_tools()
        self.deactivate_colour(self.image_button)
        self.image_button.configure(fg_color="#d17a24", hover_color="#b56e26") 
        image_path = filedialog.askopenfilename(
            title="Select an Image",
            filetypes=[("Image Files", "*.png;*.jpg;*.jpeg"), ("All Files", "*.*")])
        if not image_path:
            self.image_button.configure(fg_color="#00498f", hover_color="#023261")
            return  # User canceled the dialog       
        try:
            img = Image.open(image_path)
            img.thumbnail((200, 200), Image.LANCZOS)  # Initial size
            self.tk_image = ImageTk.PhotoImage(img) 
            canvas_x, canvas_y = 100, 100
            
            # Convert canvas coordinates to absolute PDF coordinates (no rotation compensation)
            pdf_coords = self.image_canvas_to_absolute_pdf_coordinates(canvas_x, canvas_y)
            
            self.active_image = self.canvas.create_image(
                canvas_x, canvas_y, 
                image=self.tk_image, 
                anchor="nw", 
                tags="temp_image_overlay")
            self.image_data = {
                "id": f"img_{len(self.image_overlays)}",
                "image_path": image_path,
                "image_obj": img,
                "canvas_x": canvas_x, 
                "canvas_y": canvas_y,
                "pdf_x": pdf_coords[0],  # Absolute PDF coordinates
                "pdf_y": pdf_coords[1],
                "width": img.width, 
                "height": img.height,
                "pdf_width": img.width / self.zoom_factor,  # Absolute PDF dimensions
                "pdf_height": img.height / self.zoom_factor,
                "page": self.current_page}
            self.canvas.tag_bind(self.active_image, "<ButtonPress-1>", self.start_move)
            self.canvas.tag_bind(self.active_image, "<B1-Motion>", self.do_move)
            self.canvas.tag_bind(self.active_image, "<ButtonRelease-1>", self.finalize_move)
            self.canvas.bind_all("<MouseWheel>", self.resize_image)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load image: {str(e)}")

    def start_move(self, event):
        """Start dragging the image."""
        self.image_data["start_x"] = event.x
        self.image_data["start_y"] = event.y

    def do_move(self, event):
        """Move the image as the mouse drags."""
        dx = event.x - self.image_data["start_x"]
        dy = event.y - self.image_data["start_y"]
        self.canvas.move(self.active_image, dx, dy)
        self.image_data["canvas_x"] += dx
        self.image_data["canvas_y"] += dy
        
        # Update absolute PDF coordinates (no rotation compensation)
        pdf_coords = self.image_canvas_to_absolute_pdf_coordinates(
            self.image_data["canvas_x"], 
            self.image_data["canvas_y"])
        self.image_data["pdf_x"] = pdf_coords[0]
        self.image_data["pdf_y"] = pdf_coords[1]
        self.image_data["start_x"] = event.x
        self.image_data["start_y"] = event.y

    def finalize_move(self, event):
        """Finalize the image overlay position."""
        user_response = messagebox.askyesnocancel(
            "Confirm Position",
            "Are you satisfied with the current position and size of the image? To Resize hold shift and scroll")
        if user_response is None: 
            self.canvas.delete(self.active_image) 
            self.active_image = None
            self.image_data = None
            self.image_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        if not user_response:  
            return  
        self.annotation_is_available = True
        try:
            # Get the current page rotation at insertion time
            current_rotation = 0
            if self.pdf_document:
                page = self.pdf_document[self.current_page]
                current_rotation = page.rotation
                
            overlay_info = {
                "id": self.image_data["id"],
                "type": "image_overlay",
                "image_path": self.image_data["image_path"],
                "pdf_x": self.image_data["pdf_x"],
                "pdf_y": self.image_data["pdf_y"],
                "pdf_width": self.image_data["pdf_width"],
                "pdf_height": self.image_data["pdf_height"],
                "page": self.current_page,
                "canvas_id": self.active_image,
                # Store absolute coordinates (unrotated)
                "base_x": self.image_data["pdf_x"],
                "base_y": self.image_data["pdf_y"],
                "base_width": self.image_data["pdf_width"],
                "base_height": self.image_data["pdf_height"],
                # Store rotation at insertion time for future rotation tracking
                "insertion_rotation": current_rotation,
            }
            self.image_overlays.append(overlay_info)
            print("overlay_info----",overlay_info)
            self.change_history.append(("image_overlay", self.current_page, overlay_info))
            self.undo_change_history.append(("image_overlay", self.current_page, overlay_info))
            self.canvas.delete("temp_image_overlay")
            self.redraw_image_overlays(self.current_page)
            self.canvas.unbind_all("<MouseWheel>")
            self.active_image = None
            self.annotation_listed.append("image_overlay")
            self.image_button.configure(fg_color="#00498f", hover_color="#023261")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to add image overlay: {e}")

    def resize_image(self, event):
        """Resize the image using the mouse scroll."""
        if event.state & 0x0001 == 0:
            return  # Shift not pressed; ignore scroll
        scale_factor = 1.1 if event.delta > 0 else 0.9
        new_width = int(self.image_data["width"] * scale_factor)
        new_height = int(self.image_data["height"] * scale_factor)
        if new_width < 50 or new_height < 50:
            return
        self.image_data["width"] = new_width
        self.image_data["height"] = new_height
        self.image_data["pdf_width"] = new_width / self.zoom_factor
        self.image_data["pdf_height"] = new_height / self.zoom_factor
        img_resized = self.image_data["image_obj"].resize((new_width, new_height), Image.LANCZOS)
        self.tk_image = ImageTk.PhotoImage(img_resized)
        self.canvas.itemconfig(self.active_image, image=self.tk_image)

    def image_canvas_to_absolute_pdf_coordinates(self, canvas_x, canvas_y):
        """Convert canvas coordinates to absolute PDF coordinates (no rotation compensation)."""
        # Simple conversion without any rotation compensation
        x = canvas_x / self.zoom_factor
        y = canvas_y / self.zoom_factor
        return (x, y)
    

    def redraw_image_overlays(self, page_number):
        """Redraw image overlays for the current page with proper scaling and rotation."""
        if not hasattr(self, "image_overlays"):
            self.image_overlays = []
            return
        self.canvas.delete("image_overlay")
        self.tk_images = {}  # Reset the tk_images dictionary
        
        current_rotation = 0
        if self.pdf_document:
            page = self.pdf_document[page_number]
            current_rotation = page.rotation
            
        page_width = self.page_width
        page_height = self.page_height
        current_page_overlays = [overlay for overlay in self.image_overlays if overlay["page"] == page_number]
        
        for overlay in current_page_overlays:
            try:
                # Get absolute coordinates (these are always stored without rotation)
                base_x = overlay["base_x"]
                base_y = overlay["base_y"]
                base_width = overlay["base_width"]
                base_height = overlay["base_height"]
                page_oreintation = overlay["insertion_rotation"]
                print("page_oreintation===================================",page_oreintation)
                
                # Get insertion rotation (default to 0 for backward compatibility)
                insertion_rotation = overlay.get("insertion_rotation", 0)
                
                # Calculate how much the page has been rotated since insertion
                rotation_diff = (current_rotation - insertion_rotation) % 360
                
                # Scale the base coordinates
                scaled_x = base_x * self.zoom_factor
                scaled_y = base_y * self.zoom_factor
                scaled_width = base_width * self.zoom_factor
                scaled_height = base_height * self.zoom_factor
                
                if rotation_diff == 0:
                    # No rotation since insertion - display at absolute coordinates
                    display_x = scaled_x
                    display_y = scaled_y
                    display_width = scaled_width
                    display_height = scaled_height
                    image_rotation = 0
                else:
                    # Page rotated since insertion - apply rotation transformation
                    center_x = scaled_x + (scaled_width / 2)
                    center_y = scaled_y + (scaled_height / 2)
                    
                    # Apply rotation to the center point
                    rotated_center_x, rotated_center_y = self.apply_rotation_to_point( 
                        center_x, center_y, page_width, page_height, rotation_diff,page_oreintation)
                    
                    # Adjust dimensions for 90/270 degree rotations
                    if rotation_diff in [90, 270]:
                        display_width = scaled_height
                        display_height = scaled_width
                    else:
                        display_width = scaled_width
                        display_height = scaled_height
                    
                    # Calculate final position
                    display_x = rotated_center_x - (display_width / 2)
                    display_y = rotated_center_y - (display_height / 2)
                    image_rotation = rotation_diff
                
                # Update overlay position for reference
                overlay["x"] = display_x
                overlay["y"] = display_y
                overlay["width"] = display_width
                overlay["height"] = display_height
                
                # Load and process the image
                img = Image.open(overlay["image_path"])
                
                # Apply rotation to the image if needed
                if image_rotation != 0:
                    pil_rotation = {
                        90: 270,   # Counter-clockwise in PIL
                        180: 180,
                        270: 90    # Counter-clockwise in PIL
                    }.get(image_rotation, 0)
                    img = img.rotate(pil_rotation, expand=True)
                
                img = img.resize((int(display_width), int(display_height)), Image.LANCZOS)
                tk_img = ImageTk.PhotoImage(img)
                self.tk_images[overlay["id"]] = tk_img
                
                canvas_id = self.canvas.create_image(
                    display_x, display_y,
                    image=tk_img,
                    anchor="nw",
                    tags=("image_overlay", overlay["id"]))
                overlay["canvas_id"] = canvas_id
                
            except Exception as e:
                print(f"Failed to redraw image overlay: {e}")

    def apply_rotation_to_point(self, x, y, page_width, page_height, rotation_angle, page_orientation):
        """Apply rotation transformation to a point around the page center."""
        if rotation_angle == 0:
            return x, y
        
        center_x = page_width / 2
        center_y = page_height / 2
        tx = x - center_x
        ty = y - center_y
        
        print("apply_rotation_to_point page_orientation", page_orientation)
        
        # Calculate the adjustment offset based on the difference between orientations
        # This creates a consistent offset system
        orientation_diff = (page_orientation - 0) % 360
        
        if rotation_angle == 90:
            print("90° rotation: image added at", page_orientation)
            # Standard 90° rotation
            rotated_x = -ty
            rotated_y = tx
            
            # Apply consistent adjustments - use the same 380 offset that works for 0°/180°
            if page_orientation == 0 or page_orientation == 180:
                rotated_x += (380 * self.zoom_factor)
                rotated_y += (380 * self.zoom_factor)
            elif page_orientation == 90 or page_orientation == 270:
                print("image added at 90 or 270")
                # For 90°, we need to adjust the coordinates differently
                # Since the image was added at 90°, we need to account for that
                rotated_x += (-380 * self.zoom_factor)
                rotated_y += (-380 * self.zoom_factor)
                
        elif rotation_angle == 180:
            print("180° rotation")
            # 180° rotation works correctly with standard transformation
            rotated_x = -tx
            rotated_y = -ty
            
        elif rotation_angle == 270:
            print("270° rotation: image added at", page_orientation)
            # Standard 270° rotation
            rotated_x = ty
            rotated_y = -tx
            
            # Apply consistent adjustments - use the same offset pattern as 90°
            if page_orientation == 0 or page_orientation == 180:
                rotated_x -= (380 * self.zoom_factor)
                rotated_y -= (380 * self.zoom_factor)
            elif page_orientation == 90 or page_orientation == 270:
                # For 90°, we need to adjust the coordinates differently
                rotated_x -= (-380 * self.zoom_factor)
                rotated_y -= (-380 * self.zoom_factor)
        else:
            rotated_x = tx
            rotated_y = ty
        
        final_x = rotated_x + center_x
        final_y = rotated_y + center_y
        return final_x, final_y


    # def apply_rotation_to_point(self, x, y, page_width, page_height, rotation_angle,page_oreintation):
    #     """Apply rotation transformation to a point around the page center."""
    #     if rotation_angle == 0:
    #         return x, y
        
    #     # Get page center
    #     center_x = page_width / 2
    #     center_y = page_height / 2
        
    #     # Translate point to origin
    #     tx = x - center_x
    #     ty = y - center_y
        
    #     # Apply rotation
    #     print("apply_rotation_to_point page_oreintation",page_oreintation)
    #     if rotation_angle == 90:
    #         if is_small_page == "small":        
    #             if page_oreintation == 0 or page_oreintation == 180:
    #                 print("gfdfdfdfdfdfffdfdthttjt dgdggg")
    #                 rotated_x = -ty + (185*self.zoom_factor)
    #                 rotated_y = tx + (185*self.zoom_factor)
    #             elif page_oreintation == 90 :
    #                 print("image added at 90")
    #                 rotated_x = -tx + (1000*self.zoom_factor)
    #                 rotated_y = -ty + (20*self.zoom_factor)
    #             elif page_oreintation == 270:
    #                 print("image added at 270")
    #                 rotated_x = tx + (10*self.zoom_factor)
    #                 rotated_y = ty - (635*self.zoom_factor)
    #             else:
    #                 rotated_x = -ty
    #                 rotated_y = tx
    #         elif is_small_page == "longer":
    #             if page_oreintation == 0 or page_oreintation == 180:
                #     print("gfdfdfdfdfdfffdfdthttjt dgdggg")
                #     rotated_x = -ty + (380*self.zoom_factor)
                #     rotated_y = tx + (380*self.zoom_factor)
                # elif page_oreintation == 90 :
                #     print("image added at 90")
                #     rotated_x = -tx + (2228*self.zoom_factor)
                #     rotated_y = -ty + (-335*self.zoom_factor)
                # elif page_oreintation == 270:
                #     print("image added at 270")
                #     rotated_x = tx + (-345*self.zoom_factor)
                #     rotated_y = ty - (1485*self.zoom_factor)
    #         else:
    #             rotated_x = -ty
    #             rotated_y = tx
    #     elif rotation_angle == 180:
    #         print("image added at 90 or 270 but else is printing")
    #         rotated_x = -tx
    #         rotated_y = -ty
    #     elif rotation_angle == 270:
    #         if is_small_page == "small": 
    #             if page_oreintation == 0 or page_oreintation == 180:
    #                 rotated_x = ty - (185*self.zoom_factor)
    #                 rotated_y = -tx - (185*self.zoom_factor)
    #             elif page_oreintation == 90 or page_oreintation == 270:
    #                 print("image added at 90 or 270")
    #                 rotated_x = ty + (185*self.zoom_factor)
    #                 rotated_y = -tx + (185*self.zoom_factor)
    #             else:
    #                 rotated_x = ty
    #                 rotated_y = -tx
    #         elif is_small_page == "longer":
    #             if page_oreintation == 0 or page_oreintation == 180:
        #             rotated_x = ty - (380*self.zoom_factor)
        #             rotated_y = -tx - (380*self.zoom_factor)
        #         elif page_oreintation == 90 :
        #             print("image added at 90")
        #             rotated_x = tx - (2228*self.zoom_factor)
        #             rotated_y = ty - (-335*self.zoom_factor)
        #         elif page_oreintation == 270:
        #             print("image added at 270")
        #             rotated_x = -tx - (-345*self.zoom_factor)
        #             rotated_y = -ty + (1485*self.zoom_factor)
        # #     else:
    #         rotated_x = tx
    #         rotated_y = ty
        
    #     # Translate back
    #     final_x = rotated_x + center_x
    #     final_y = rotated_y + center_y
        
    #     return final_x, final_y

    def add_text_to_pdf(self):
        """Enable text-adding mode on the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.add_text_mode == True:
            self.add_text_mode = False
            self.text_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.text_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools()
        self.deactivate_colour(self.text_button)
        self.canvas.bind("<Button-1>", self.on_add_text_click)
        self.add_text_mode = True


    # def on_add_text_click(self, event):
    #     """Handle adding text overlay at the clicked position with strict boundary enforcement."""
    #     if not self.pdf_document or not self.add_text_mode:
    #         return

    #     x = self.canvas.canvasx(event.x)
    #     y = self.canvas.canvasy(event.y)

    #     if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
    #         return

    #     text = self.ask_for_note_text(x, y, "Add Text")
    #     if not text:
    #         self.text_button.configure(fg_color="#00498f", hover_color="#023261")
    #         return

    #     # x_scaled = x / self.zoom_factor
    #     # y_scaled = y / self.zoom_factor
    #     x_scaled, y_scaled = self.canvas_point_to_pdf_coordinates(x, y)
    #     self.text_button.configure(fg_color="#00498f", hover_color="#023261")
    #     page = self.pdf_document[self.current_page]
    #     page_width_scaled = page.rect.width
    #     max_text_width = min(page_width_scaled - x_scaled - 20, page_width_scaled * 0.4)

    #     self.annotation_data = {
    #         "text": text,
    #         "font_size": 16,
    #         "max_width": max_text_width
    #     }

    #     self.text_annotations[(self.current_page, x_scaled, y_scaled)] = self.annotation_data
    #     self.change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))
    #     self.undo_change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))
    #     self.render_page(self.current_page)
    #     self.add_text_mode = False
    #     self.canvas.unbind("<Button-1>")
    #     self.annotation_is_available = True
    #     self.annotation_listed.append("text")
    #     self.text_button.configure(fg_color="#00498f", hover_color="#023261")

    # def canvas_point_to_pdf_coordinates(self, canvas_x, canvas_y):
    #     """Convert a single canvas point to PDF coordinates accounting for rotation."""
    #     page = self.pdf_document[self.current_page]
    #     rotation = page.rotation
    #     rect = page.rect
    #     page_width = rect.width
    #     page_height = rect.height

    #     pdf_x = canvas_x / self.zoom_factor
    #     pdf_y = canvas_y / self.zoom_factor

    #     if rotation == 90:
    #         new_x = pdf_y
    #         new_y = page_height - pdf_x
    #     elif rotation == 180:
    #         new_x = page_width - pdf_x
    #         new_y = page_height - pdf_y
    #     elif rotation == 270:
    #         new_x = page_width - pdf_y
    #         new_y = pdf_x
    #     else:  # rotation == 0
    #         new_x = pdf_x
    #         new_y = pdf_y

    #     return new_x, new_y


    # def redraw_text_annotations(self):
    #     """Redraw text annotations with strict boundary enforcement."""
    #     self.canvas.delete("plain_text_annotation")
    #     if not self.pdf_document:
    #         return

    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation
    #     fill_color = "black" if not self.is_inverted else "white"

    #     for (page_num, x_scaled, y_scaled), annotation_data in list(self.text_annotations.items()):
    #         if page_num != self.current_page:
    #             continue
    #         base_font_size = 16
    #         # font_size_zoom = base_font_size * self.zoom_factor
    #         if isinstance(annotation_data, str):
    #             annotation_data = {
    #                 "text": annotation_data,
    #                 "max_width": page.rect.width * 0.4,
    #                 "font_size": base_font_size
    #             }

    #         text = annotation_data["text"]
    #         max_width = annotation_data["max_width"] * self.zoom_factor
    #         font_size = annotation_data["font_size"]
    #         x_position = x_scaled * self.zoom_factor
    #         y_position = y_scaled * self.zoom_factor
            
    #         if rotation_angle == 90:  # Rotate text **clockwise**
    #             if is_small_page == "yes":
    #                 rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "very small":
    #                 print("buka buka very small")
    #                 rotated_x, rotated_y = self.page_height+(80*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "smaller":
    #                 print("buka buka smaller")
    #                 rotated_x, rotated_y = self.page_height+(-550*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "small":
    #                 print("buka buka small")
    #                 rotated_x, rotated_y = self.page_height+(370*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "slightly":
    #                 rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "longer":
    #                 rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "maybe":
    #                 rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "nope large":
    #                 rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "nope very large":
    #                 rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
    #             else:
    #                 rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position

    #             angle = -90
    #         elif rotation_angle == 180:
    #             rotated_x = page.rect.width * self.zoom_factor - x_position
    #             rotated_y = page.rect.height * self.zoom_factor - y_position
    #             angle = 180
    #         elif rotation_angle == 270:  # Rotate text **counterclockwise**
    #             if is_small_page == "yes":
    #                 rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
    #             elif is_small_page == "very small":
    #                 rotated_x, rotated_y = y_position, self.page_width-(80*self.zoom_factor) - x_position
    #             elif is_small_page == "smaller":
    #                 rotated_x, rotated_y = y_position, self.page_width-(-550*self.zoom_factor) - x_position
    #             elif is_small_page == "small":
    #                 rotated_x, rotated_y = y_position, self.page_width-(370*self.zoom_factor) - x_position
    #             elif is_small_page == "slightly":
    #                 rotated_x, rotated_y = y_position, self.page_width-(1050*self.zoom_factor) - x_position
    #             elif is_small_page == "longer":
    #                 rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position 
    #             elif is_small_page == "maybe":
    #                 rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position 
    #             elif is_small_page == "nope large":
    #                 rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
    #             elif is_small_page == "nope very large":
    #                 rotated_x, rotated_y = y_position, self.page_width-(4300*self.zoom_factor) - x_position
    #             else:
    #                 rotated_x, rotated_y = y_position, self.page_width-(2000*self.zoom_factor) - x_position
    #             angle = -270
    #         else:
    #             rotated_x = x_position
    #             rotated_y = y_position
    #             angle = 0

    #         text_container = self.canvas.create_text(
    #             rotated_x, rotated_y,
    #             text=text,
    #             font=("Arial", int(font_size)),
    #             fill=fill_color,
    #             width=max_width,
    #             tags="plain_text_annotation",
    #             anchor="nw"
    #         )
    #         self.canvas.itemconfig(text_container, angle=angle)
    #         self.canvas.tag_bind(text_container, "<Button-1>", self.on_text_press)
    #         self.canvas.tag_bind(text_container, "<B1-Motion>", self.on_text_drag)
    #         self.canvas.tag_bind(text_container, "<ButtonRelease-1>", self.on_text_release)

    #         bbox = self.canvas.bbox(text_container)
    #         annotation_data["canvas_id"] = text_container
    #         annotation_data["bbox"] = bbox

    #     self.annotation_is_available = True


    # # === Dragging Behavior ===

    # def on_text_press(self, event):
    #     """Store the selected text ID and offset when clicked."""
    #     if not (event.state & 0x0001):
    #         return  # Don't activate drag if Shift is not held
    #     self.dragged_text_id = self.canvas.find_withtag("current")[0]
    #     if "plain_text_annotation" not in self.canvas.gettags(self.dragged_text_id):
    #         self.dragged_text_id = None
    #         return
    #     bbox = self.canvas.bbox(self.dragged_text_id)
    #     self.drag_offset_x = event.x - bbox[0]
    #     self.drag_offset_y = event.y - bbox[1]


    # def on_text_drag(self, event):
    #     """Drag the text annotation."""
    #     if self.dragged_text_id:
    #         new_x = self.canvas.canvasx(event.x) - self.drag_offset_x
    #         new_y = self.canvas.canvasy(event.y) - self.drag_offset_y
    #         self.canvas.coords(self.dragged_text_id, new_x, new_y)

    # def on_text_release(self, event):
    #     """Update annotation data after dragging and reflect in change history."""
    #     if not self.dragged_text_id:
    #         return
    #     for old_key in list(self.text_annotations.keys()):
    #         data = self.text_annotations[old_key]
    #         if data.get("canvas_id") == self.dragged_text_id:
    #             bbox = self.canvas.bbox(self.dragged_text_id)
    #             top_left_x, top_left_y = bbox[0], bbox[1]
    #             new_x_scaled, new_y_scaled = self.canvas_point_to_pdf_coordinates(top_left_x, top_left_y)
    #             new_key = (old_key[0], new_x_scaled, new_y_scaled)

    #             # Move the annotation entry to new key
    #             self.text_annotations[new_key] = self.text_annotations.pop(old_key)
    #             self.text_annotations[new_key]["canvas_id"] = self.dragged_text_id
    #             self.text_annotations[new_key]["bbox"] = bbox  # <-- THIS LINE FIXES THE ISSUE

    #             # Update change history positions
    #             for history in [self.change_history, self.undo_change_history]:
    #                 for i, entry in enumerate(history):
    #                     if (entry[0] == "add_text" and entry[1] == old_key[0] and
    #                         abs(entry[2] - old_key[1]) < 1e-3 and abs(entry[3] - old_key[2]) < 1e-3):
    #                         history[i] = ("add_text", old_key[0], new_x_scaled, new_y_scaled, entry[4])
    #                         break
    #             break
    #     self.dragged_text_id = None

    def on_add_text_click(self, event):
        """Handle adding text overlay at the clicked position with strict boundary enforcement."""
        if not self.pdf_document or not self.add_text_mode:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return
        text = self.ask_for_note_text(x, y, "Add Text")
        if not text:
            self.text_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        x_scaled, y_scaled = self.canvas_point_to_pdf_coordinates(x, y)
        self.text_button.configure(fg_color="#00498f", hover_color="#023261")
        page = self.pdf_document[self.current_page]
        page_width_scaled = page.rect.width
        max_text_width = min(page_width_scaled - x_scaled - 20, page_width_scaled * 0.4)
        
        # Store current rotation at time of insertion (like image function)
        current_rotation = page.rotation
        
        self.annotation_data = {
            "text": text,
            "font_size": 16,
            "max_width": max_text_width,
            "base_x": x_scaled,  # Store base coordinates
            "base_y": y_scaled,
            "insertion_rotation": current_rotation  # Store rotation at insertion time
        }
        self.text_annotations[(self.current_page, x_scaled, y_scaled)] = self.annotation_data
        self.change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))
        self.undo_change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))
        self.render_page(self.current_page)
        self.add_text_mode = False
        self.canvas.unbind("<Button-1>")
        self.annotation_is_available = True
        self.annotation_listed.append("text")
        self.text_button.configure(fg_color="#00498f", hover_color="#023261")

    def canvas_point_to_pdf_coordinates(self, canvas_x, canvas_y):
        """Convert a single canvas point to PDF coordinates WITHOUT rotation compensation."""
        # Remove rotation logic - just convert canvas to PDF coordinates directly
        pdf_x = canvas_x / self.zoom_factor
        pdf_y = canvas_y / self.zoom_factor
        return pdf_x, pdf_y

    def redraw_text_annotations(self):
        """Redraw text annotations with consistent rotation logic like images."""
        self.canvas.delete("plain_text_annotation")
        if not self.pdf_document:
            return
        
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        fill_color = "black" if not self.is_inverted else "white"
        page_width = self.page_width
        page_height = self.page_height
        
        for (page_num, x_scaled, y_scaled), annotation_data in list(self.text_annotations.items()):
            if page_num != self.current_page:
                continue
            
            base_font_size = 16
            if isinstance(annotation_data, str):
                # Convert old format to new format
                annotation_data = {
                    "text": annotation_data,
                    "max_width": page.rect.width * 0.4,
                    "font_size": base_font_size,
                    "base_x": x_scaled,
                    "base_y": y_scaled,
                    "insertion_rotation": 0  # Default for old annotations
                }
                # Update the stored annotation
                self.text_annotations[(page_num, x_scaled, y_scaled)] = annotation_data
            
            text = annotation_data["text"]
            font_size = annotation_data["font_size"]
            
            # Get base coordinates and insertion rotation
            base_x = annotation_data.get("base_x", x_scaled)
            base_y = annotation_data.get("base_y", y_scaled)
            insertion_rotation = annotation_data.get("insertion_rotation", 0)
            
            # Calculate rotation difference
            rotation_diff = (current_rotation - insertion_rotation) % 360
            
            # Scale base coordinates
            scaled_x = base_x * self.zoom_factor
            scaled_y = base_y * self.zoom_factor
            max_width = annotation_data["max_width"] * self.zoom_factor
            
            # Apply rotation transformation (similar to image function)
            if rotation_diff == 0:
                display_x = scaled_x
                display_y = scaled_y
                text_rotation = 0
            else:
                # Apply rotation using the same logic as images
                rotated_x, rotated_y = self.apply_text_rotation_to_point(
                    scaled_x, scaled_y, page_width, page_height, rotation_diff, insertion_rotation)
                display_x = rotated_x
                display_y = rotated_y
                text_rotation = -rotation_diff  # Negative for canvas rotation
            
            # Create text with proper rotation
            text_container = self.canvas.create_text(
                display_x, display_y,
                text=text,
                font=("Arial", int(font_size)),
                fill=fill_color,
                width=max_width,
                tags="plain_text_annotation",
                anchor="nw")
            
            # Apply rotation to text
            if text_rotation != 0:
                self.canvas.itemconfig(text_container, angle=text_rotation)
            
            # Bind events
            self.canvas.tag_bind(text_container, "<Button-1>", self.on_text_press)
            self.canvas.tag_bind(text_container, "<B1-Motion>", self.on_text_drag)
            self.canvas.tag_bind(text_container, "<ButtonRelease-1>", self.on_text_release)
            
            # Store canvas info
            bbox = self.canvas.bbox(text_container)
            annotation_data["canvas_id"] = text_container
            annotation_data["bbox"] = bbox
        
        self.annotation_is_available = True

    def apply_text_rotation_to_point(self, x, y, page_width, page_height, rotation_angle, insertion_rotation):
        """Apply rotation transformation to text point (similar to image rotation)."""
        if rotation_angle == 0:
            return x, y
        
        center_x = page_width / 2
        center_y = page_height / 2
        
        # Translate to origin
        tx = x - center_x
        ty = y - center_y
        
        # Apply rotation
        if rotation_angle == 90:
            rotated_x = -ty
            rotated_y = tx
            # Apply similar offset adjustments as images if needed
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x += (380 * self.zoom_factor)
                rotated_y += (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x += (-380 * self.zoom_factor)
                rotated_y += (-380 * self.zoom_factor)
        elif rotation_angle == 180:
            rotated_x = -tx
            rotated_y = -ty
        elif rotation_angle == 270:
            rotated_x = ty
            rotated_y = -tx
            # Apply similar offset adjustments as images if needed
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x -= (380 * self.zoom_factor)
                rotated_y -= (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x -= (-380 * self.zoom_factor)
                rotated_y -= (-380 * self.zoom_factor)
        else:
            rotated_x = tx
            rotated_y = ty
        
        # Translate back
        final_x = rotated_x + center_x
        final_y = rotated_y + center_y
        
        return final_x, final_y

    def on_text_press(self, event):
        """Store the selected text ID and offset when clicked."""
        if not (event.state & 0x0001):
            return
        self.dragged_text_id = self.canvas.find_withtag("current")[0]
        if "plain_text_annotation" not in self.canvas.gettags(self.dragged_text_id):
            self.dragged_text_id = None
            return
        bbox = self.canvas.bbox(self.dragged_text_id)
        self.drag_offset_x = event.x - bbox[0]
        self.drag_offset_y = event.y - bbox[1]

    def on_text_drag(self, event):
        """Drag the text annotation."""
        if self.dragged_text_id:
            new_x = self.canvas.canvasx(event.x) - self.drag_offset_x
            new_y = self.canvas.canvasy(event.y) - self.drag_offset_y
            self.canvas.coords(self.dragged_text_id, new_x, new_y)

    def on_text_release(self, event):
        """Update annotation data after dragging and reflect in change history."""
        if not self.dragged_text_id:
            return
        
        for old_key in list(self.text_annotations.keys()):
            data = self.text_annotations[old_key]
            if data.get("canvas_id") == self.dragged_text_id:
                bbox = self.canvas.bbox(self.dragged_text_id)
                top_left_x, top_left_y = bbox[0], bbox[1]
                
                # Convert back to base PDF coordinates (without rotation)
                new_x_scaled, new_y_scaled = self.canvas_point_to_pdf_coordinates(top_left_x, top_left_y)
                
                # Update the base coordinates
                data["base_x"] = new_x_scaled
                data["base_y"] = new_y_scaled
                
                # Create new key and update dictionary
                new_key = (old_key[0], new_x_scaled, new_y_scaled)
                self.text_annotations[new_key] = self.text_annotations.pop(old_key)
                self.text_annotations[new_key]["canvas_id"] = self.dragged_text_id
                self.text_annotations[new_key]["bbox"] = bbox
                
                # Update history
                for history in [self.change_history, self.undo_change_history]:
                    for i, entry in enumerate(history):
                        if (entry[0] == "add_text" and entry[1] == old_key[0] and
                            abs(entry[2] - old_key[1]) < 1e-3 and abs(entry[3] - old_key[2]) < 1e-3):
                            history[i] = ("add_text", old_key[0], new_x_scaled, new_y_scaled, entry[4])
                            break
                break
        
        self.dragged_text_id = None

    def add_text_with_background(self):
        """Enable text-adding mode for text with a background."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.add_text_bg_mode == True:
            self.add_text_bg_mode = False
            self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.text_bg_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools() 
        self.deactivate_colour(self.text_bg_button)
        self.canvas.bind("<Button-1>", self.on_add_text_with_bg_click)
        self.add_text_bg_mode = True

    def on_add_text_with_bg_click(self, event):
        """Handle adding text with background overlay at the clicked position."""
        if not self.pdf_document or not self.add_text_bg_mode:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return
        text = self.ask_for_note_text(x, y, "Add Text with Background")
        if not text:
            self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        
        wrapped_lines = []
        for line in text.splitlines():
            wrapped_lines.extend(textwrap.wrap(line, width=30) or [""])  # Ensure empty lines preserved
        wrapped_text = "\n".join(wrapped_lines)
        
        # Convert canvas coordinates to PDF coordinates WITHOUT rotation
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        
        # Store current rotation at time of insertion (like image and text functions)
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        
        self.text_annotations_bg[(self.current_page, x_scaled, y_scaled)] = {
            "text": wrapped_text,
            "base_x": x_scaled,  # Store base coordinates
            "base_y": y_scaled,
            "insertion_rotation": current_rotation  # Store rotation at insertion time
        }
        
        self.change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, wrapped_text))
        self.undo_change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, wrapped_text))
        self.render_page(self.current_page)
        self.add_text_bg_mode = False
        self.canvas.unbind("<Button-1>")
        self.annotation_is_available = True
        self.annotation_listed.append("text_bg")
        self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")

    def on_text_bg_press(self, event):
        """Handle mouse press on text with background."""
        if not (event.state & 0x0001):
            return
        clicked_item = self.canvas.find_closest(event.x, event.y)[0]
        item_tags = self.canvas.gettags(clicked_item)
        if "text_annotation" in item_tags or "text_annotation_bg" in item_tags:
            for key, annotation in self.text_annotations_bg.items():
                if annotation.get("canvas_id") == clicked_item and key[0] == self.current_page:
                    self.dragged_text_bg_key = key
                    self.dragged_text_bg_id = clicked_item
                    self.text_bg_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
                    return "break"
            
            self.dragged_text_bg_key = None
            self.dragged_text_bg_id = None
            self.text_bg_drag_start = None
        else:
            self.dragged_text_bg_key = None
            self.dragged_text_bg_id = None
            self.text_bg_drag_start = None

    def on_text_bg_drag(self, event):
        """Handle dragging of text with background."""
        if self.dragged_text_bg_key and self.text_bg_drag_start:
            x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            dx = x - self.text_bg_drag_start[0]
            dy = y - self.text_bg_drag_start[1]
            self.deactivate_tools()
            self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")

            annotation_data = self.text_annotations_bg.get(self.dragged_text_bg_key)
            if annotation_data:
                text_id = annotation_data.get("canvas_id")
                bg_id = annotation_data.get("bg_rect_id")
                if text_id and bg_id:
                    self.canvas.move(text_id, dx, dy)
                    self.canvas.move(bg_id, dx, dy)
            
            self.text_bg_drag_start = (x, y)
            return "break"

    def on_text_bg_release(self, event):
        """Update annotation data after dragging and reflect in change history."""
        if not self.dragged_text_bg_id:
            return
        
        for old_key in list(self.text_annotations_bg.keys()):
            data = self.text_annotations_bg[old_key]
            if data.get("canvas_id") == self.dragged_text_bg_id:
                bbox = self.canvas.bbox(self.dragged_text_bg_id)
                top_left_x, top_left_y = bbox[0], bbox[1]
                
                # Convert back to base PDF coordinates (without rotation)
                new_x_scaled = round(top_left_x / self.zoom_factor, 4)
                new_y_scaled = round(top_left_y / self.zoom_factor, 4)
                
                # Update the base coordinates
                data["base_x"] = new_x_scaled
                data["base_y"] = new_y_scaled
                
                # Create new key and update dictionary
                new_key = (old_key[0], new_x_scaled, new_y_scaled)
                self.text_annotations_bg[new_key] = self.text_annotations_bg.pop(old_key)
                self.text_annotations_bg[new_key]["canvas_id"] = self.dragged_text_bg_id
                self.text_annotations_bg[new_key]["bbox"] = bbox
                
                # Update history
                for history in [self.change_history, self.undo_change_history]:
                    for i, entry in enumerate(history):
                        if (entry[0] == "add_text_bg" and entry[1] == old_key[0] and
                            abs(entry[2] - old_key[1]) < 1e-3 and abs(entry[3] - old_key[2]) < 1e-3):
                            history[i] = ("add_text_bg", old_key[0], new_x_scaled, new_y_scaled, entry[4])
                            break
                break
        
        self.dragged_text_bg_key = None
        self.dragged_text_bg_id = None
        self.text_bg_drag_start = None

    def redraw_text_with_background(self):
        """Redraw text with background annotations using consistent rotation logic."""
        self.canvas.delete("text_annotation_bg")
        self.canvas.delete("text_annotation")  # Also delete text items
        if not self.pdf_document:
            return
        
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        fill_color = "black" if not self.is_inverted else "white"
        page_width = self.page_width
        page_height = self.page_height
        
        for (page_num, x_scaled, y_scaled), annotation_data in self.text_annotations_bg.items():
            if page_num != self.current_page:
                continue
            
            # Handle old format annotations
            if isinstance(annotation_data, dict) and "base_x" not in annotation_data:
                # Convert old format to new format
                annotation_data.update({
                    "base_x": x_scaled,
                    "base_y": y_scaled,
                    "insertion_rotation": 0  # Default for old annotations
                })
                # Update the stored annotation
                self.text_annotations_bg[(page_num, x_scaled, y_scaled)] = annotation_data
            
            text = annotation_data["text"]
            
            # Get base coordinates and insertion rotation
            base_x = annotation_data.get("base_x", x_scaled)
            base_y = annotation_data.get("base_y", y_scaled)
            insertion_rotation = annotation_data.get("insertion_rotation", 0)
            
            # Calculate rotation difference
            rotation_diff = (current_rotation - insertion_rotation) % 360
            
            # Scale base coordinates
            x_position = base_x * self.zoom_factor
            y_position = base_y * self.zoom_factor
            
            fontsize = 16
            text_lines = text.split("\n")
            max_line_length = max(len(line) for line in text_lines) if text_lines else 0
            actual_text_width = max_line_length * fontsize * 0.6
            text_height = fontsize * 1.2 * len(text_lines)
            side_padding = 5
            bottom_padding = 8
            container_width = actual_text_width + (side_padding * 2)
            
            # Apply rotation transformation (similar to other text functions)
            if rotation_diff == 0:
                display_x = x_position
                display_y = y_position
                text_rotation = 0
                # Rectangle coordinates for no rotation
                rect_x1 = display_x - side_padding
                rect_y1 = display_y - side_padding
                rect_x2 = display_x + container_width + side_padding
                rect_y2 = display_y + text_height + bottom_padding
            else:
                # Apply rotation using similar logic as other text functions
                rotated_x, rotated_y = self.apply_text_bg_rotation_to_point(
                    x_position, y_position, page_width, page_height, rotation_diff, insertion_rotation)
                display_x = rotated_x
                display_y = rotated_y
                text_rotation = -rotation_diff  # Negative for canvas rotation
                
                # Calculate rectangle coordinates based on rotation
                if rotation_diff == 90:
                    rect_x1 = display_x - text_height - side_padding
                    rect_y1 = display_y - side_padding
                    rect_x2 = display_x + side_padding
                    rect_y2 = display_y + container_width + bottom_padding
                elif rotation_diff == 180:
                    rect_x1 = display_x - container_width - side_padding
                    rect_y1 = display_y - text_height - side_padding
                    rect_x2 = display_x + side_padding
                    rect_y2 = display_y + bottom_padding
                elif rotation_diff == 270:
                    rect_x1 = display_x - side_padding
                    rect_y1 = display_y - container_width - side_padding
                    rect_x2 = display_x + text_height + side_padding
                    rect_y2 = display_y + bottom_padding
                else:
                    rect_x1 = display_x - side_padding
                    rect_y1 = display_y - side_padding
                    rect_x2 = display_x + container_width + side_padding
                    rect_y2 = display_y + text_height + bottom_padding
            
            # Create background rectangle
            bg_rect_id = self.canvas.create_rectangle(
                rect_x1, rect_y1, rect_x2, rect_y2,
                fill="cyan",
                outline="cyan",
                tags="text_annotation_bg")
            
            # Create text
            text_id = self.canvas.create_text(
                display_x, display_y,
                text=text,
                font=("Arial", int(fontsize)),
                fill=fill_color,
                tags="text_annotation",
                anchor="nw")
            
            # Apply rotation to text
            if text_rotation != 0:
                self.canvas.itemconfig(text_id, angle=text_rotation)
            
            # Store canvas info
            bbox = self.canvas.bbox(text_id)
            annotation_data["canvas_id"] = text_id
            annotation_data["bg_rect_id"] = bg_rect_id
            annotation_data["bbox"] = bbox
            
            # Bind events to both text and background
            self.canvas.tag_bind(text_id, "<Button-1>", self.on_text_bg_press)
            self.canvas.tag_bind(text_id, "<B1-Motion>", self.on_text_bg_drag)
            self.canvas.tag_bind(text_id, "<ButtonRelease-1>", self.on_text_bg_release)
            self.canvas.tag_bind(bg_rect_id, "<Button-1>", self.on_text_bg_press)
            self.canvas.tag_bind(bg_rect_id, "<B1-Motion>", self.on_text_bg_drag)
            self.canvas.tag_bind(bg_rect_id, "<ButtonRelease-1>", self.on_text_bg_release)
        
        self.annotation_is_available = True

    def apply_text_bg_rotation_to_point(self, x, y, page_width, page_height, rotation_angle, insertion_rotation):
        """Apply rotation transformation to text with background point (similar to other text rotation)."""
        if rotation_angle == 0:
            return x, y
        
        center_x = page_width / 2
        center_y = page_height / 2
        
        # Translate to origin
        tx = x - center_x
        ty = y - center_y
        
        # Apply rotation
        if rotation_angle == 90:
            rotated_x = -ty
            rotated_y = tx
            # Apply similar offset adjustments as other text functions if needed
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x += (380 * self.zoom_factor)
                rotated_y += (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x += (-380 * self.zoom_factor)
                rotated_y += (-380 * self.zoom_factor)
        elif rotation_angle == 180:
            rotated_x = -tx
            rotated_y = -ty
        elif rotation_angle == 270:
            rotated_x = ty
            rotated_y = -tx
            # Apply similar offset adjustments as other text functions if needed
            if insertion_rotation == 0 or insertion_rotation == 180:
                rotated_x -= (380 * self.zoom_factor)
                rotated_y -= (380 * self.zoom_factor)
            elif insertion_rotation == 90 or insertion_rotation == 270:
                rotated_x -= (-380 * self.zoom_factor)
                rotated_y -= (-380 * self.zoom_factor)
        else:
            rotated_x = tx
            rotated_y = ty
        
        # Translate back
        final_x = rotated_x + center_x
        final_y = rotated_y + center_y
        
        return final_x, final_y

    # def on_add_text_with_bg_click(self, event):
    #     if not self.pdf_document or not self.add_text_bg_mode:
    #         return
    #     x = self.canvas.canvasx(event.x)
    #     y = self.canvas.canvasy(event.y)
    #     if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
    #         return
    #     text = self.ask_for_note_text(x, y, "Add Text with Background")
    #     if not text:
    #         self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")
    #         return
    #     wrapped_lines = []
    #     for line in text.splitlines():
    #         wrapped_lines.extend(textwrap.wrap(line, width=30) or [""])  # Ensure empty lines preserved
    #         self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")
    #     wrapped_text = "\n".join(wrapped_lines)
    #     x_scaled = x / self.zoom_factor
    #     y_scaled = y / self.zoom_factor
    #     self.text_annotations_bg[(self.current_page, x_scaled, y_scaled)] = {
    #         "text": wrapped_text}
    #     self.change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, wrapped_text))
    #     self.undo_change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, wrapped_text))
    #     self.render_page(self.current_page)
    #     self.add_text_bg_mode = False
    #     self.canvas.unbind("<Button-1>")
    #     self.annotation_is_available = True
    #     self.annotation_listed.append("text_bg")
    #     self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")

    # # Text with background drag functionality
    # def on_text_bg_press(self, event):
    #     """Handle mouse press on text with background."""
    #     if not (event.state & 0x0001):
    #         return
    #     clicked_item = self.canvas.find_closest(event.x, event.y)[0]
    #     item_tags = self.canvas.gettags(clicked_item)
        
    #     if "text_annotation" in item_tags or "text_annotation_bg" in item_tags:
    #         # Find the text annotation that was clicked
    #         for key, annotation in self.text_annotations_bg.items():
    #             if annotation.get("canvas_id") == clicked_item and key[0] == self.current_page:
    #                 self.dragged_text_bg_key = key
    #                 self.dragged_text_bg_id = clicked_item
    #                 self.text_bg_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
    #                 return "break"
            
    #         self.dragged_text_bg_key = None
    #         self.dragged_text_bg_id = None
    #         self.text_bg_drag_start = None
    #     else:
    #         self.dragged_text_bg_key = None
    #         self.dragged_text_bg_id = None
    #         self.text_bg_drag_start = None

    # def on_text_bg_drag(self, event):
    #     """Handle dragging of text with background."""
    #     if self.dragged_text_bg_key and self.text_bg_drag_start:
    #         x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
    #         dx = x - self.text_bg_drag_start[0]
    #         dy = y - self.text_bg_drag_start[1]
    #         self.deactivate_tools()
    #         self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")

    #         annotation_data = self.text_annotations_bg.get(self.dragged_text_bg_key)
    #         if annotation_data:
    #             text_id = annotation_data.get("canvas_id")
    #             bg_id = annotation_data.get("bg_rect_id")
    #             if text_id and bg_id:
    #                 self.canvas.move(text_id, dx, dy)
    #                 self.canvas.move(bg_id, dx, dy)
            
    #         self.text_bg_drag_start = (x, y)
    #         return "break"
        
    # def on_text_bg_release(self, event):
    #     """Update annotation data after dragging and reflect in change history."""
    #     if not self.dragged_text_bg_id:
    #         return

    #     for old_key in list(self.text_annotations_bg.keys()):
    #         data = self.text_annotations_bg[old_key]
    #         if data.get("canvas_id") == self.dragged_text_bg_id:
    #             bbox = self.canvas.bbox(self.dragged_text_bg_id)
    #             top_left_x, top_left_y = bbox[0], bbox[1]
    #             new_x_scaled = round(top_left_x / self.zoom_factor, 4)
    #             new_y_scaled = round(top_left_y / self.zoom_factor, 4)
    #             new_key = (old_key[0], new_x_scaled, new_y_scaled)

    #             # Move annotation to new key
    #             self.text_annotations_bg[new_key] = self.text_annotations_bg.pop(old_key)
    #             self.text_annotations_bg[new_key]["canvas_id"] = self.dragged_text_bg_id
    #             self.text_annotations_bg[new_key]["bbox"] = bbox  # <- Fix

    #             # Update both change_history and undo_change_history
    #             for history in [self.change_history, self.undo_change_history]:
    #                 for i, entry in enumerate(history):
    #                     if (entry[0] == "add_text_bg" and entry[1] == old_key[0] and
    #                         abs(entry[2] - old_key[1]) < 1e-3 and abs(entry[3] - old_key[2]) < 1e-3):
    #                         history[i] = ("add_text_bg", old_key[0], new_x_scaled, new_y_scaled, entry[4])
    #                         break
    #             break

    #     self.dragged_text_bg_key = None
    #     self.dragged_text_bg_id = None
    #     self.text_bg_drag_start = None


    # def redraw_text_with_background(self):
    #     self.canvas.delete("text_annotation_bg")
    #     self.canvas.delete("text_annotation")  # Also delete text items
    #     if not self.pdf_document:
    #         return
    #     page = self.pdf_document[self.current_page]
    #     rotation_angle = page.rotation
    #     fill_color = "black" if not self.is_inverted else "white"
        
    #     for (page_num, x_scaled, y_scaled), annotation_data in self.text_annotations_bg.items():
    #         if page_num != self.current_page:
    #             continue
    #         text = annotation_data["text"]
    #         x_position = x_scaled * self.zoom_factor
    #         y_position = y_scaled * self.zoom_factor
    #         page_width = page.rect.width * self.zoom_factor
    #         page_height = page.rect.height * self.zoom_factor
    #         fontsize = 16
    #         text_lines = text.split("\n")
    #         max_line_length = max(len(line) for line in text_lines) if text_lines else 0
    #         actual_text_width = max_line_length * fontsize * 0.6
    #         text_height = fontsize * 1.2 * len(text_lines)
    #         side_padding = 5
    #         bottom_padding = 8
    #         container_width = actual_text_width + (side_padding * 2)
            
    #         if rotation_angle == 90:
    #             if is_small_page == "yes":
    #                 rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "very small":
    #                 rotated_x, rotated_y = self.page_height+(80*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "smaller":
    #                 rotated_x, rotated_y = self.page_height+(-550*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "small":
    #                 rotated_x, rotated_y = self.page_height+(370*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "slightly":
    #                 rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "longer":
    #                 rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "maybe":
    #                 rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "nope large":
    #                 rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
    #             elif is_small_page == "nope very large":
    #                 rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
    #             else:
    #                 rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position
    #             rect_x1 = rotated_x - text_height - side_padding
    #             rect_y1 = rotated_y - side_padding
    #             rect_x2 = rotated_x + side_padding
    #             rect_y2 = rotated_y + container_width + bottom_padding
    #             angle = -90
    #         elif rotation_angle == 180:
    #             rotated_x = page_width - x_position
    #             rotated_y = page_height - y_position
    #             rect_x1 = rotated_x - container_width - side_padding
    #             rect_y1 = rotated_y - text_height - side_padding
    #             rect_x2 = rotated_x + side_padding
    #             rect_y2 = rotated_y + bottom_padding
    #             angle = 180
    #         elif rotation_angle == 270:
    #             if is_small_page == "yes":
    #                 rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
    #             elif is_small_page == "very small":
    #                 rotated_x, rotated_y = y_position, self.page_width-(80*self.zoom_factor) - x_position
    #             elif is_small_page == "smaller":
    #                 rotated_x, rotated_y = y_position, self.page_width-(-550*self.zoom_factor) - x_position
    #             elif is_small_page == "small":
    #                 rotated_x, rotated_y = y_position, self.page_width-(370*self.zoom_factor) - x_position
    #             elif is_small_page == "slightly":
    #                 rotated_x, rotated_y = y_position, self.page_width-(1050*self.zoom_factor) - x_position
    #             elif is_small_page == "longer":
    #                 rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position
    #             elif is_small_page == "maybe":
    #                 rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
    #             elif is_small_page == "nope large":
    #                 rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
    #             elif is_small_page == "nope very large":
    #                 rotated_x, rotated_y = y_position, self.page_width-(4300*self.zoom_factor) - x_position
    #             else:
    #                 rotated_x, rotated_y = y_position, self.page_width-(2000*self.zoom_factor) - x_position
    #             rect_x1 = rotated_x - side_padding
    #             rect_y1 = rotated_y - container_width - side_padding
    #             rect_x2 = rotated_x + text_height + side_padding
    #             rect_y2 = rotated_y + bottom_padding
    #             angle = -270
    #         else:  # rotation_angle == 0
    #             rotated_x = x_position
    #             rotated_y = y_position
    #             rect_x1 = rotated_x - side_padding
    #             rect_y1 = rotated_y - side_padding
    #             rect_x2 = rotated_x + container_width + side_padding
    #             rect_y2 = rotated_y + text_height + bottom_padding
    #             angle = 0
            
    #         # Create background rectangle
    #         bg_rect_id = self.canvas.create_rectangle(
    #             rect_x1, rect_y1, rect_x2, rect_y2,
    #             fill="cyan",
    #             outline="cyan",
    #             tags="text_annotation_bg"
    #         )
            
    #         # Create text
    #         text_id = self.canvas.create_text(
    #             rotated_x, rotated_y,
    #             text=text,
    #             font=("Arial", int(fontsize)),
    #             fill=fill_color,
    #             tags="text_annotation",
    #             anchor="nw"
    #         )
    #         self.canvas.itemconfig(text_id, angle=angle)
    #         bbox = self.canvas.bbox(text_id)
            
    #         # Store canvas IDs and bbox
    #         annotation_data["canvas_id"] = text_id
    #         annotation_data["bg_rect_id"] = bg_rect_id
    #         annotation_data["bbox"] = bbox
            
    #         # Bind drag events to both text and background
    #         self.canvas.tag_bind(text_id, "<Button-1>", self.on_text_bg_press)
    #         self.canvas.tag_bind(text_id, "<B1-Motion>", self.on_text_bg_drag)
    #         self.canvas.tag_bind(text_id, "<ButtonRelease-1>", self.on_text_bg_release)
            
    #         self.canvas.tag_bind(bg_rect_id, "<Button-1>", self.on_text_bg_press)
    #         self.canvas.tag_bind(bg_rect_id, "<B1-Motion>", self.on_text_bg_drag)
    #         self.canvas.tag_bind(bg_rect_id, "<ButtonRelease-1>", self.on_text_bg_release)
        
    #     self.annotation_is_available = True

    def activate_line_tool(self):
        """Activate the straight line drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_line:
            self.deactivate_tools()
            self.active_line = False
            self.line_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_line = True
        self.deactivate_colour(self.line_button,"active_line")
        self.line_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools()
        self.is_drawing_line = True
        self.canvas.bind("<Button-1>", self.start_line)
        self.canvas.bind("<B1-Motion>", self.draw_line_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_line)

    def activate_arrow_tool(self):
        """Activate the arrow drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_arrow:
            self.deactivate_tools()
            self.active_arrow = False
            self.arrow_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_arrow = True
        self.deactivate_colour(self.arrow_button,"active_arrow")
        self.arrow_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools()
        self.is_drawing_arrow = True
        self.canvas.bind("<Button-1>", self.start_line)
        self.canvas.bind("<B1-Motion>", self.draw_line_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_arrow)

    def deactivate_tools(self):
        """Deactivate all tools."""
        self.is_drawing_line = False
        self.is_drawing_arrow = False
        self.is_drawing_hollow_rect = False
        self.is_drawing_filled_rect = False
        self.current_rectangle = None
        self.current_line = None
        self.deactivate_selection_mode()
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    def start_line(self, event):
        """Start drawing a line or arrow."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        if self.current_line:
            self.canvas.delete(self.current_line)
        self.current_line = None

    def draw_line_preview(self, event):
        """Show a preview of the line or arrow while dragging."""
        if self.current_line:
            self.canvas.delete(self.current_line)
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        if self.is_drawing_line:
            self.current_line = self.canvas.create_line(
                self.start_x, self.start_y, end_x, end_y,
                fill="red", width=4, tags="annotation_preview")
        elif self.is_drawing_arrow:
            self.current_line = self.canvas.create_line(
                self.start_x, self.start_y, end_x, end_y,
                fill="red", width=4, arrow=ctk.LAST, 
                arrowshape=(16, 20, 6), tags="annotation_preview")

    def canvas_line_to_pdf_coordinates(self, canvas_x1, canvas_y1, canvas_x2, canvas_y2):
        """Convert canvas coordinates to PDF coordinates accounting for rotation."""
        page = self.pdf_document[self.current_page]
        rotation = page.rotation
        original_rect = page.rect
        page_width = original_rect.width
        page_height = original_rect.height

        cx1 = canvas_x1 / self.zoom_factor
        cy1 = canvas_y1 / self.zoom_factor
        cx2 = canvas_x2 / self.zoom_factor
        cy2 = canvas_y2 / self.zoom_factor

        if rotation == 0:
            x1, y1, x2, y2 = cx1, cy1, cx2, cy2
        elif rotation == 90:
            x1, y1 = cy1, page_width - cx1
            x2, y2 = cy2, page_width - cx2
        elif rotation == 180:
            x1, y1 = page_width - cx1, page_height - cy1
            x2, y2 = page_width - cx2, page_height - cy2
        elif rotation == 270:
            x1, y1 = page_height - cy1, cx1
            x2, y2 = page_height - cy2, cx2
        
        # FIXED: Return coordinates in original order to preserve arrow direction
        return (x1, y1, x2, y2)

    def pdf_line_to_canvas_coordinates(self, pdf_x1, pdf_y1, pdf_x2, pdf_y2, rotation):
        """Convert PDF coordinates to canvas coordinates accounting for rotation."""
        page = self.pdf_document[self.current_page]
        page_width = page.rect.width
        page_height = page.rect.height
        if rotation == 0:
            cx1, cy1, cx2, cy2 = pdf_x1, pdf_y1, pdf_x2, pdf_y2
        elif rotation == 90:
            cx1, cy1 = page_height - pdf_y1, pdf_x1
            cx2, cy2 = page_height - pdf_y2, pdf_x2
        elif rotation == 180:
            cx1, cy1 = page_width - pdf_x1, page_height - pdf_y1
            cx2, cy2 = page_width - pdf_x2, page_height - pdf_y2
        elif rotation == 270:
            cx1, cy1 = pdf_y1, page_width - pdf_x1
            cx2, cy2 = pdf_y2, page_width - pdf_x2
        canvas_x1 = cx1 * self.zoom_factor
        canvas_y1 = cy1 * self.zoom_factor
        canvas_x2 = cx2 * self.zoom_factor
        canvas_y2 = cy2 * self.zoom_factor

        # FIXED: Return coordinates in original order to preserve arrow direction
        return (canvas_x1, canvas_y1, canvas_x2, canvas_y2)


    def finish_line(self, event):
        """Finish drawing the line and add it to annotations."""
        if self.current_line:
            self.canvas.delete(self.current_line)
        
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        line_id = self.canvas.create_line(
            self.start_x, self.start_y, end_x, end_y,
            fill="red", width=4, tags="annotation")
        pdf_coords = self.canvas_line_to_pdf_coordinates(self.start_x, self.start_y, end_x, end_y)
        line_data = {
            'type': 'line',
            'page': self.current_page,
            'x1': pdf_coords[0],
            'y1': pdf_coords[1],
            'x2': pdf_coords[2],
            'y2': pdf_coords[3],
            'id': line_id,
            'color': "red"
        }
        print("line_datac----- ",line_data)
        self.lines.append(line_data)
        self.annotations.append(line_data)
        self.draw_lines_first_time = True
        print("line_data",line_data)
        self.change_history.append(('add_annotation', line_data))
        self.undo_change_history.append(('add_annotation', line_data))
        self.annotation_is_available = True
        self.annotation_listed.append("line")
        
        # Bind drag events to the line
        self.canvas.tag_bind(line_id, "<Button-1>", self.on_line_press)
        self.canvas.tag_bind(line_id, "<B1-Motion>", self.on_line_drag)
        self.canvas.tag_bind(line_id, "<ButtonRelease-1>", self.on_line_release)

    def finish_arrow(self, event):
        """Finish drawing the arrow and add it to annotations."""
        if self.current_line:
            self.canvas.delete(self.current_line)
        
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        arrow_id = self.canvas.create_line(
            self.start_x, self.start_y, end_x, end_y,
            fill="red", width=4, arrow=ctk.LAST, 
            arrowshape=(16, 20, 6), tags="annotation")
        pdf_coords = self.canvas_line_to_pdf_coordinates(self.start_x, self.start_y, end_x, end_y)
        arrow_data = {
            'type': 'arrow',
            'page': self.current_page,
            'x1': pdf_coords[0],
            'y1': pdf_coords[1],
            'x2': pdf_coords[2],
            'y2': pdf_coords[3],
            'id': arrow_id,
            'color': "red"
        }
        print("arrow_datac----- ",arrow_data)
        self.draw_arrows_first_time = True
        self.arrows.append(arrow_data)
        self.annotations.append(arrow_data)
        print("arrow_data",arrow_data)
        self.change_history.append(('add_annotation', arrow_data))
        self.undo_change_history.append(('add_annotation', arrow_data))
        self.annotation_is_available = True
        self.annotation_listed.append("arrow")
        
        # Bind drag events to the arrow
        self.canvas.tag_bind(arrow_id, "<Button-1>", self.on_line_press)
        self.canvas.tag_bind(arrow_id, "<B1-Motion>", self.on_line_drag)
        self.canvas.tag_bind(arrow_id, "<ButtonRelease-1>", self.on_line_release)

    def on_line_press(self, event):
        """Handle mouse press on line or arrow."""
        if not (event.state & 0x0001):
            return
        clicked_item = self.canvas.find_closest(event.x, event.y)[0]
        item_tags = self.canvas.gettags(clicked_item)
        if "annotation" in item_tags or "line" in item_tags or "arrow" in item_tags:
            for line in self.lines:
                if line.get("id") == clicked_item and line["page"] == self.current_page:
                    self.dragged_line_id = clicked_item
                    self.line_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
                    # Store the original coordinates before dragging starts
                    self.line_start_coords = {
                        'x1': line['x1'],
                        'y1': line['y1'],
                        'x2': line['x2'],
                        'y2': line['y2']
                    }
                    # Reset total drag accumulator
                    self.line_total_drag_dx = 0
                    self.line_total_drag_dy = 0
                    return "break"
            for arrow in self.arrows:
                if arrow.get("id") == clicked_item and arrow["page"] == self.current_page:
                    self.dragged_line_id = clicked_item
                    self.line_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
                    # Store the original coordinates before dragging starts
                    self.line_start_coords = {
                        'x1': arrow['x1'],
                        'y1': arrow['y1'],
                        'x2': arrow['x2'],
                        'y2': arrow['y2']
                    }
                    # Reset total drag accumulator
                    self.line_total_drag_dx = 0
                    self.line_total_drag_dy = 0
                    return "break"

    def on_line_drag(self, event):
        """Handle dragging of line or arrow."""
        if self.dragged_line_id and self.line_drag_start:
            x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            dx = x - self.line_drag_start[0]
            dy = y - self.line_drag_start[1]
            self.canvas.move(self.dragged_line_id, dx, dy)
            
            # Accumulate total movement in PDF coordinates
            self.line_total_drag_dx += dx / self.zoom_factor
            self.line_total_drag_dy += dy / self.zoom_factor
            
            self.deactivate_tools()
            self.active_line = False
            self.active_arrow = False
            self.line_button.configure(fg_color="#00498f", hover_color="#023261")
            self.arrow_button.configure(fg_color="#00498f", hover_color="#023261")
            self.line_drag_start = (x, y)
            print("Dragging line/arrow:", self.dragged_line_id, "to", x, y)
            return "break"

    def on_line_release(self, event):
        """Update stored annotation data after dragging."""
        if not self.dragged_line_id or not hasattr(self, 'line_start_coords'):
            return
        
        # Use the accumulated total drag displacement
        total_dx = self.line_total_drag_dx
        total_dy = self.line_total_drag_dy
        
        if total_dx == 0 and total_dy == 0:
            print("No movement recorded.")
            # Clean up and return
            self.dragged_line_id = None
            self.line_drag_start = None
            if hasattr(self, 'line_start_coords'):
                delattr(self, 'line_start_coords')
            self.line_total_drag_dx = 0
            self.line_total_drag_dy = 0
            return
        
        # Calculate new absolute coordinates using original position + total displacement
        new_x1 = self.line_start_coords['x1'] + total_dx
        new_y1 = self.line_start_coords['y1'] + total_dy
        new_x2 = self.line_start_coords['x2'] + total_dx
        new_y2 = self.line_start_coords['y2'] + total_dy
        
        # Update the line data
        for i, line in enumerate(self.lines):
            if line["id"] == self.dragged_line_id:
                old_data = dict(line)
                self.lines[i]["x1"] = new_x1
                self.lines[i]["y1"] = new_y1
                self.lines[i]["x2"] = new_x2
                self.lines[i]["y2"] = new_y2
                self.change_history.append(('move_annotation', old_data, dict(self.lines[i])))
                self.undo_change_history.append(('move_annotation', old_data, dict(self.lines[i])))
                print("Updated line ID", self.dragged_line_id, "to", self.lines[i])
                break
        
        # Update the arrow data
        for i, arrow in enumerate(self.arrows):
            if arrow["id"] == self.dragged_line_id:
                old_data = dict(arrow)
                self.arrows[i]["x1"] = new_x1
                self.arrows[i]["y1"] = new_y1
                self.arrows[i]["x2"] = new_x2
                self.arrows[i]["y2"] = new_y2
                self.change_history.append(('move_annotation', old_data, dict(self.arrows[i])))
                self.undo_change_history.append(('move_annotation', old_data, dict(self.arrows[i])))
                print("Updated arrow ID", self.dragged_line_id, "to", self.arrows[i])
                break
        
        # Update the annotations list
        for i, annotation in enumerate(self.annotations):
            if annotation.get("id") == self.dragged_line_id:
                self.annotations[i]["x1"] = new_x1
                self.annotations[i]["y1"] = new_y1
                self.annotations[i]["x2"] = new_x2
                self.annotations[i]["y2"] = new_y2
                print("Updated annotation ID", self.dragged_line_id, "to", self.annotations[i])
                break

        # Clean up
        self.dragged_line_id = None
        self.line_drag_start = None
        if hasattr(self, 'line_start_coords'):
            delattr(self, 'line_start_coords')
        self.line_total_drag_dx = 0
        self.line_total_drag_dy = 0
        return "break"


    def activate_hollow_rectangle_tool(self):
        """Activate the hollow rectangle drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_hollowrectangle:
            self.deactivate_tools()
            self.active_hollowrectangle = False
            self.hollow_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_hollowrectangle = True
        self.deactivate_colour(self.hollow_rectangle_button,"active_hollowrectangle")
        self.hollow_rectangle_button.configure(fg_color="#d17a24", hover_color="#b56e26")
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
        if self.active_filledrectangle:
            self.deactivate_tools()
            self.active_filledrectangle = False
            self.filled_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_filledrectangle = True
        self.deactivate_colour(self.filled_rectangle_button,"active_filledrectangle")
        self.filled_rectangle_button.configure(fg_color="#d17a24", hover_color="#b56e26")
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
        page = self.pdf_document[self.current_page]
        print("self.page_rotation-",page.rotation)
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        outline_color = "red"
        fill_color = "" if self.is_drawing_hollow_rect else "red"
        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
            outline=outline_color, fill=fill_color, width=4, tags="annotation_preview")

    def draw_rectangle_preview(self, event):
        """Show a preview of the rectangle while dragging."""
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        outline_color = "red"
        fill_color = "" if self.is_drawing_hollow_rect else "red"
        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, end_x, end_y,
            outline=outline_color, fill=fill_color, width=4, tags="annotation_preview")

    def finish_hollow_rectangle(self, event):
        """Finish drawing the hollow rectangle and add it to annotations."""
        self.finish_rectangle(event, filled=False)

    def finish_filled_rectangle(self, event):
        """Finish drawing the filled rectangle and add it to annotations."""
        self.finish_rectangle(event, filled=True)
        
    def finish_rectangle(self, event, filled):
        """Finish drawing a rectangle and add it to annotations."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        
        outline_color = "red"
        fill_color = "" if not filled else "red"
        border_width = 4 if not filled else 3
        
        rect_id = self.canvas.create_rectangle(
            x1, y1, x2, y2,
            outline=outline_color, fill=fill_color, width=border_width, tags="annotation")
        
        # Convert canvas coordinates to PDF coordinates considering current rotation
        pdf_coords = self.canvas_to_pdf_coordinates(x1, y1, x2, y2)
        
        rect_data = {
            'type': 'rectangle',
            'page': self.current_page,
            'x1': pdf_coords[0],
            'y1': pdf_coords[1],
            'x2': pdf_coords[2],
            'y2': pdf_coords[3],
            'filled': filled,
            'id': rect_id,
            'color': "red",
            'rotation_when_created': self.pdf_document[self.current_page].rotation
        }
        
        self.rectangles.append(rect_data)
        self.annotations.append(rect_data)
        self.change_history.append(('add_annotation', rect_data))
        self.undo_change_history.append(('add_annotation', rect_data))
        self.annotation_is_available = True
        self.annotation_listed.append("rectangle")
        
        self.canvas.tag_bind(rect_id, "<Button-1>", self.on_rectangle_press)
        self.canvas.tag_bind(rect_id, "<B1-Motion>", self.on_rectangle_drag)
        self.canvas.tag_bind(rect_id, "<ButtonRelease-1>", self.on_rectangle_release)

    def canvas_to_pdf_coordinates(self, canvas_x1, canvas_y1, canvas_x2, canvas_y2):
        """Convert canvas coordinates to PDF coordinates accounting for rotation."""
        page = self.pdf_document[self.current_page]
        rotation = page.rotation
        original_rect = page.rect
        page_width = original_rect.width
        page_height = original_rect.height

        # Convert canvas to unrotated PDF space
        cx1 = canvas_x1 / self.zoom_factor
        cy1 = canvas_y1 / self.zoom_factor
        cx2 = canvas_x2 / self.zoom_factor
        cy2 = canvas_y2 / self.zoom_factor

        if rotation == 0:
            x1, y1, x2, y2 = cx1, cy1, cx2, cy2
        elif rotation == 90:
            x1, y1 = cy1, page_width - cx1
            x2, y2 = cy2, page_width - cx2
        elif rotation == 180:
            x1, y1 = page_width - cx1, page_height - cy1
            x2, y2 = page_width - cx2, page_height - cy2
        elif rotation == 270:
            x1, y1 = page_height - cy1, cx1
            x2, y2 = page_height - cy2, cx2

        return (min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2))


    def pdf_to_canvas_coordinates(self, pdf_x1, pdf_y1, pdf_x2, pdf_y2, rotation):
        """Convert PDF coordinates to canvas coordinates accounting for rotation."""
        page = self.pdf_document[self.current_page]
        page_width = page.rect.width
        page_height = page.rect.height

        if rotation == 0:
            cx1, cy1, cx2, cy2 = pdf_x1, pdf_y1, pdf_x2, pdf_y2
        elif rotation == 90:
            cx1, cy1 = page_height - pdf_y1, pdf_x1
            cx2, cy2 = page_height - pdf_y2, pdf_x2
        elif rotation == 180:
            cx1, cy1 = page_width - pdf_x1, page_height - pdf_y1
            cx2, cy2 = page_width - pdf_x2, page_height - pdf_y2
        elif rotation == 270:
            cx1, cy1 = pdf_y1, page_width - pdf_x1
            cx2, cy2 = pdf_y2, page_width - pdf_x2

        # Scale to canvas
        canvas_x1 = cx1 * self.zoom_factor
        canvas_y1 = cy1 * self.zoom_factor
        canvas_x2 = cx2 * self.zoom_factor
        canvas_y2 = cy2 * self.zoom_factor

        return (min(canvas_x1, canvas_x2), min(canvas_y1, canvas_y2),
                max(canvas_x1, canvas_x2), max(canvas_y1, canvas_y2))


    def on_rectangle_press(self, event):
        """Handle mouse press on rectangle."""
        # Get the clicked item
        if not (event.state & 0x0001):
            return
        clicked_item = self.canvas.find_closest(event.x, event.y)[0]
        
        # Check if the clicked item is actually a rectangle annotation
        item_tags = self.canvas.gettags(clicked_item)
        if "annotation" in item_tags or "red_rectangle" in item_tags:
            # Verify it's actually a rectangle from our annotations
            for rect in self.rectangles:
                if rect.get("id") == clicked_item and rect["page"] == self.current_page:
                    self.dragged_rectangle_id = clicked_item
                    self.rect_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
                    # Prevent the event from propagating to the canvas (which would start page dragging)
                    return "break"
            
            # If we found an annotation tag but no matching rectangle, clear any drag state
            self.dragged_rectangle_id = None
            self.rect_drag_start = None
        else:
            # Not clicking on a rectangle, clear drag state
            self.dragged_rectangle_id = None
            self.rect_drag_start = None

    def on_rectangle_drag(self, event):
        """Handle dragging of rectangle."""
        if self.dragged_rectangle_id and self.rect_drag_start:
            x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            dx = x - self.rect_drag_start[0]
            dy = y - self.rect_drag_start[1]
            
            # Deactivate rectangle tools when dragging
            self.deactivate_tools()
            self.active_hollowrectangle = False
            self.active_filledrectangle = False
            self.filled_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
            self.hollow_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
            
            self.canvas.move(self.dragged_rectangle_id, dx, dy)
            self.rect_drag_start = (x, y)
            
            # Prevent event propagation to avoid page dragging
            return "break"


    def on_rectangle_release(self, event):
        """Update stored annotation data after dragging."""
        if not self.dragged_rectangle_id:
            return
        
        bbox = self.canvas.bbox(self.dragged_rectangle_id)
        if not bbox:
            self.dragged_rectangle_id = None
            self.rect_drag_start = None
            return
        
        # Convert canvas coordinates back to PDF coordinates
        pdf_coords = self.canvas_to_pdf_coordinates(bbox[0], bbox[1], bbox[2], bbox[3])
        
        for rect in self.rectangles:
            if rect["id"] == self.dragged_rectangle_id and rect["page"] == self.current_page:
                old_data = dict(rect)  # Store old data for history
                rect.update({
                    "x1": pdf_coords[0], "y1": pdf_coords[1],
                    "x2": pdf_coords[2], "y2": pdf_coords[3]
                })
                self.change_history.append(('move_annotation', old_data, dict(rect)))
                self.undo_change_history.append(('move_annotation', old_data, dict(rect)))
                break
        
        for annotation in self.annotations:
            if isinstance(annotation, dict) and annotation.get("id") == self.dragged_rectangle_id and annotation["page"] == self.current_page:
                annotation.update({
                    "x1": pdf_coords[0], "y1": pdf_coords[1],
                    "x2": pdf_coords[2], "y2": pdf_coords[3]
                })
                break
        
        self.dragged_rectangle_id = None
        self.rect_drag_start = None
        return "break"

    
    def activate_hollow_ellipse(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_hollowellipse:
            self.deactivate_tools()
            self.active_hollowellipse = False
            self.hollow_ellipse_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_hollowellipse = True
        self.ellipse_mode = "hollow"
        self.deactivate_colour(self.hollow_ellipse_button,"active_hollowellipse")
        self.hollow_ellipse_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.canvas.bind("<ButtonPress-1>", self.start_ellipse)
        self.canvas.bind("<B1-Motion>", self.draw_ellipse)
        self.canvas.bind("<ButtonRelease-1>", self.finalize_ellipse)
    
    def activate_filled_ellipse(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_filledellipse:
            self.deactivate_tools()
            self.active_filledellipse = False
            self.filled_ellipse_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_filledellipse = True
        self.ellipse_mode = "filled"
        self.deactivate_colour(self.filled_ellipse_button,"active_filledellipse")
        self.filled_ellipse_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.canvas.bind("<ButtonPress-1>", self.start_ellipse)
        self.canvas.bind("<B1-Motion>", self.draw_ellipse)
        self.canvas.bind("<ButtonRelease-1>", self.finalize_ellipse)
    
    def start_ellipse(self, event):
        """Start drawing an ellipse."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.current_ellipse = None

    def draw_ellipse(self, event):
        """Draw preview of ellipse as the user drags."""
        if self.current_ellipse:
            self.canvas.delete(self.current_ellipse)

        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)

        outline = "orange"
        fill = "" if self.ellipse_mode == "hollow" else "orange"

        self.current_ellipse = self.canvas.create_oval(
            self.start_x, self.start_y, end_x, end_y,
            outline=outline, width=4, fill=fill, tags=("annotation_preview", "ellipse_preview")
        )

    def finalize_ellipse(self, event):
        """Finalize the ellipse and save coordinates for both redraw modes."""
        if not self.current_ellipse:
            return

        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)

        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)

        # Convert to PDF coordinates
        pdf_coords = self.canvas_to_pdf_coordinates(x1, y1, x2, y2)
        pdf_x1, pdf_y1, pdf_x2, pdf_y2 = pdf_coords

        # Draw final ellipse on canvas
        fill = "" if self.ellipse_mode == "hollow" else "orange"
        ellipse_id = self.canvas.create_oval(
            x1, y1, x2, y2,
            outline="orange",
            fill=fill,
            width=4 if self.ellipse_mode == "hollow" else 3,
            tags=("annotation", "ellipse")
        )


        # # Store tuple-based annotation (for redraw_ellipses_90 compatibility)
        tuple_data = (
            "ellipse",
            pdf_x1, pdf_y1,
            pdf_x2, pdf_y2,
            ellipse_id,
            self.ellipse_mode,
            self.current_page
        )
        self.annotations.append(tuple_data)

        # Track for undo/redo
        self.change_history.append(('add_annotation', tuple_data))
        self.undo_change_history.append(('add_annotation', tuple_data))
        self.annotation_listed.append("ellipse")

        # Bind drag events
        self.canvas.tag_bind(ellipse_id, "<Button-1>", self.on_ellipse_press)
        self.canvas.tag_bind(ellipse_id, "<B1-Motion>", self.on_ellipse_drag)
        self.canvas.tag_bind(ellipse_id, "<ButtonRelease-1>", self.on_ellipse_release)

        # Cleanup preview
        self.canvas.delete(self.current_ellipse)
        self.current_ellipse = None

        
    def on_ellipse_press(self, event):
        """Start dragging an ellipse."""
        if not (event.state & 0x0001):
            return
        clicked_item = self.canvas.find_closest(event.x, event.y)[0]
        tags = self.canvas.gettags(clicked_item)
        if "ellipse" in tags or "annotation" in tags:
            self.dragged_ellipse_id = clicked_item
            self.ellipse_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
            return "break"
        else:
            self.dragged_ellipse_id = None
            self.ellipse_drag_start = None

    def on_ellipse_drag(self, event):
        """Drag the ellipse."""
        if self.dragged_ellipse_id and self.ellipse_drag_start:
            self.deactivate_tools()
            self.active_hollowellipse = False
            self.active_filledellipse = False
            self.filled_ellipse_button.configure(fg_color="#00498f", hover_color="#023261")
            self.hollow_ellipse_button.configure(fg_color="#00498f", hover_color="#023261")
            x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            dx = x - self.ellipse_drag_start[0]
            dy = y - self.ellipse_drag_start[1]
            self.canvas.move(self.dragged_ellipse_id, dx, dy)
            self.ellipse_drag_start = (x, y)
            return "break"

    def on_ellipse_release(self, event):
        """Update stored ellipse annotation after dragging."""
        if not self.dragged_ellipse_id:
            return

        bbox = self.canvas.bbox(self.dragged_ellipse_id)
        if not bbox:
            self.dragged_ellipse_id = None
            self.ellipse_drag_start = None
            return
        new_x1, new_y1, new_x2, new_y2 = [v / self.zoom_factor for v in bbox]

        for i, ann in enumerate(self.annotations):
            if isinstance(ann, tuple) and ann[0] == "ellipse" and ann[5] == self.dragged_ellipse_id and ann[7] == self.current_page:
                old_annotation = ann
                updated_annotation = ("ellipse", new_x1, new_y1, new_x2, new_y2, self.dragged_ellipse_id, ann[6], ann[7])
                self.annotations[i] = updated_annotation
                self.change_history.append(("move_annotation", old_annotation, updated_annotation))
                self.undo_change_history.append(("move_annotation", old_annotation, updated_annotation))
                break
        self.dragged_ellipse_id = None
        self.ellipse_drag_start = None
        return "break"


    def deactivate_selection_mode(self):
        """Clean up after selection mode to avoid binding conflicts."""
        # Restore original bindings instead of just unbinding
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<Motion>", self.on_mouse_hover)
        
        # Clear any existing zoom rectangle
        if hasattr(self, 'zoom_rectangle') and self.zoom_rectangle:
            self.canvas.delete(self.zoom_rectangle)
            self.zoom_rectangle = None
        
        self.is_zooming_area = False


    def activate_selection_mode(self):
        """Activate the zoom area tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.selectzoom_button.configure(fg_color="#d17a24",hover_color="#b56e26")
        self.deactivate_colour(self.selectzoom_button)
        # Properly deactivate all tools first
        self.deactivate_tools()
        
        # Reset the zoom rectangle reference
        self.zoom_rectangle = None
        self.is_zooming_area = True
        
        # Apply new bindings
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
        if not hasattr(self, 'zoom_rectangle') or self.zoom_rectangle is None:
            return
        
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        
        # Don't proceed with very small selections
        if (x2 - x1) < 5 or (y2 - y1) < 5:
            self.deactivate_selection_mode()
            return
            
        x1_pdf, y1_pdf = x1 / self.zoom_factor, y1 / self.zoom_factor
        x2_pdf, y2_pdf = x2 / self.zoom_factor, y2 / self.zoom_factor
        selected_width = x2_pdf - x1_pdf
        selected_height = y2_pdf - y1_pdf
        
        if selected_width <= 0 or selected_height <= 0:
            self.deactivate_selection_mode()
            return  # Prevent invalid selections
            
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        zoom_x = canvas_width / selected_width
        zoom_y = canvas_height / selected_height
        new_zoom_factor = min(zoom_x, zoom_y)
        new_zoom_factor = max(0.1, min(new_zoom_factor, 10))
        
        center_x_pdf = (x1_pdf + x2_pdf) / 2
        center_y_pdf = (y1_pdf + y2_pdf) / 2
        self.zoom_factor = new_zoom_factor
        
        # Delete zoom rectangle before rendering to avoid artifacts
        self.canvas.delete(self.zoom_rectangle)
        self.zoom_rectangle = None

        expected_width = int(self.page_width * self.zoom_factor)
        expected_height = int(self.page_height * self.zoom_factor)
        expected_pixels = expected_width * expected_height

        MAX_PIXELS = 178956970  # PIL default safety limit

        if expected_pixels > MAX_PIXELS:
            messagebox.showerror("Zoom Error", "Pixel size has increased beyond the safe threshold.")
            self.deactivate_selection_mode()
            self.selectzoom_button.configure(fg_color="#00498f",hover_color="#023261")
            return
        
        self.render_page(self.current_page)
        
        # Calculate scrolling position to center the zoomed area
        scroll_x = ((center_x_pdf * new_zoom_factor) - (canvas_width / 2)) / self.page_width
        scroll_y = ((center_y_pdf * new_zoom_factor) - (canvas_height / 2)) / self.page_height
        scroll_x = max(0, min(scroll_x, 1))
        scroll_y = max(0, min(scroll_y, 1))
        
        self.canvas.xview_moveto(scroll_x)
        self.canvas.yview_moveto(scroll_y)
        
        # Properly deactivate the selection mode to restore normal functionality
        self.deactivate_selection_mode()
        self.selectzoom_button.configure(fg_color="#00498f",hover_color="#023261")


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


    def activate_black_rectangle_tool(self):
        """Activate the filled rectangle drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.active_redact:
            self.deactivate_tools()
            self.active_redact = False
            self.redact_button.configure(fg_color="#00498f", hover_color="#023261")
            return
        self.active_redact = True
        self.deactivate_colour(self.redact_button,"active_redact")
        self.redact_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools()
        self.is_drawing_filled_rect = True
        self.is_drawing_hollow_rect = False
        self.highlight_mode = False
        self.canvas.bind("<Button-1>", self.start_blackrectangle_drawing)
        self.canvas.bind("<B1-Motion>", self.draw_blackrectangle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_blackfilled_rectangle)

    def start_blackrectangle_drawing(self, event):
        """Start drawing a rectangle (for hollow/filled tools)."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        outline_color = "black"
        fill_color = "" if self.is_drawing_hollow_rect else "black"
        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
            outline=outline_color, fill=fill_color, width=3, tags="annotation_preview")

    def draw_blackrectangle_preview(self, event):
        """Show a preview of the rectangle while dragging."""
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        outline_color = "black"
        fill_color = "" if self.is_drawing_hollow_rect else "black"
        self.current_rectangle = self.canvas.create_rectangle(
            self.start_x, self.start_y, end_x, end_y,
            outline=outline_color, fill=fill_color, width=3, tags="annotation_preview")

    def finish_blackfilled_rectangle(self, event):
        """Finish drawing the filled rectangle and add it to annotations."""
        self.finish_blackrectangle(event, filled=True)

# ------------------------------------------------------------------------------------------------------------------------------------------------     
    
    def finish_blackrectangle(self, event, filled):
        """Finish drawing rectangle and add to both local and API lists."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        outline_color = "black"
        fill_color = "black" if filled else ""
        rect_id = self.canvas.create_rectangle(
            x1, y1, x2, y2,
            outline=outline_color, fill=fill_color, width=3, tags="annotation"
        )
        zoom = self.zoom_factor
        pdf_coords = self.canvas_to_pdf_coordinates(x1, y1, x2, y2)
        current_rotation = self.pdf_document[self.current_page].rotation
        rect_data = {
            'type': 'rectangle',
            'page': self.current_page,
            'x1': pdf_coords[0],
            'y1': pdf_coords[1],
            'x2': pdf_coords[2],
            'y2': pdf_coords[3],
            'filled': filled,
            'id': rect_id,
            'color': "black",
            'source': 'local',  # Mark as locally drawn
        }
        
        # Add to local lists (for undo functionality)
        print("rect_data---",rect_data)
        self.redact_rectangles.append(rect_data)
        self.redact_annotations.append(rect_data)
        
        # Also add to API lists (for toggle functionality)
        self.add_pagesize[rect_id] = (self.page_width_redact, self.page_height_recdact )
        self.redact_api_rectangles.append(rect_data)
        self.redact_api_annotations.append(rect_data)
        print("self.add_pagesize---",self.add_pagesize)
                
        self.change_redact_history.append(('add_annotation', rect_data))
        self.change_api_redact_history.append(('add_annotation', rect_data))
        self.annotation_is_available = True


    def enable_undo_blackrect(self):
        """Enable deletion mode for locally drawn annotations only."""
        if self.activedeleteredact_button:
            self.activedeleteredact_button = False
            self.deleteredact_button.configure(fg_color="#00498f",hover_color="#023261")
            self.canvas.unbind("<Button-1>")  # Unbind the delete event
            return
        self.activedeleteredact_button = True
        self.deactivate_tools()
        self.deleteredact_button.configure(fg_color="#d17a24",hover_color="#b56e26")
        self.deactivate_colour(self.deleteredact_button,"activedeleteredact_button")
        self.canvas.bind("<Button-1>", self.undo_blackrect)

    def undo_blackrect(self, event):
        """Delete only locally drawn rectangles, not API-fetched ones."""
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        zoom = self.zoom_factor
        page = self.pdf_document[self.current_page]
        current_rotation = page.rotation
        
        print("self.redact_rectangles---", self.redact_rectangles)
        
        # Only check locally drawn rectangles (redact_rectangles), not API ones
        for rect in reversed(self.redact_rectangles):  # Reverse to get top-most first
            if rect['page'] != self.current_page:
                continue
                
            # Get PDF coordinates from the rectangle
            pdf_x1 = rect['x1']
            pdf_y1 = rect['y1']
            pdf_x2 = rect['x2']
            pdf_y2 = rect['y2']
            
            # Convert PDF coordinates to current canvas coordinates using rotation
            canvas_coords = self.pdf_to_canvas_coordinates(pdf_x1, pdf_y1, pdf_x2, pdf_y2, current_rotation)
            canvas_x1, canvas_y1, canvas_x2, canvas_y2 = canvas_coords
            
            # Apply offset for rotations (same as in redraw_rectangles_90)
            offset = 750 * self.zoom_factor
            if current_rotation == 90:
                canvas_x1 += offset
                canvas_x2 += offset
            elif current_rotation == 270:
                canvas_y1 -= offset
                canvas_y2 -= offset
            
            # Create bounding box for hit testing
            min_x = min(canvas_x1, canvas_x2)
            max_x = max(canvas_x1, canvas_x2)
            min_y = min(canvas_y1, canvas_y2)
            max_y = max(canvas_y1, canvas_y2)
            
            # Add some tolerance for easier clicking (5 pixels)
            tolerance = 5
            min_x -= tolerance
            max_x += tolerance
            min_y -= tolerance
            max_y += tolerance
            
            # Check if click is within the rectangle bounds
            if min_x <= x <= max_x and min_y <= y <= max_y:
                # Delete from canvas
                self.canvas.delete(rect['id'])
                
                # Delete from PDF - use original PDF coordinates
                page_obj = self.pdf_document.load_page(self.current_page)
                rect_pdf = fitz.Rect(pdf_x1, pdf_y1, pdf_x2, pdf_y2)
                
                # Find and delete the annotation from PDF
                for annot in page_obj.annots():
                    # Compare rectangles with some tolerance due to floating point precision
                    annot_rect = annot.rect
                    if (abs(annot_rect.x0 - rect_pdf.x0) < 1 and 
                        abs(annot_rect.y0 - rect_pdf.y0) < 1 and
                        abs(annot_rect.x1 - rect_pdf.x1) < 1 and 
                        abs(annot_rect.y1 - rect_pdf.y1) < 1):
                        annot.delete()
                        break
                
                # Remove from local lists
                self.redact_rectangles.remove(rect)
                if rect in self.redact_annotations:
                    self.redact_annotations.remove(rect)
                
                # Also remove from API lists since locally drawn rectangles are added there too
                if rect in self.redact_api_rectangles:
                    self.redact_api_rectangles.remove(rect)
                    self.add_pagesize.pop(rect['id'], None)
                if rect in self.redact_api_annotations:
                    self.redact_api_annotations.remove(rect)
                
                print("self.add_pagesize.pop(rect)-", self.add_pagesize)
                
                # Re-render the page to reflect changes
                self.render_page(self.current_page)
                
                # Add to change history
                self.change_redact_history.append(('delete_annotation', rect))
                
                # Update annotation availability flag
                self.annotation_is_available = bool(self.redact_annotations + self.redact_api_annotations)
                
                break

    # def undo_blackrect(self, event):
    #     """Delete only locally drawn rectangles, not API-fetched ones."""
    #     x = self.canvas.canvasx(event.x)
    #     y = self.canvas.canvasy(event.y)
    #     zoom = self.zoom_factor
    #     print("self.redact_rectangles---",self.redact_rectangles)
        
    #     # Only check locally drawn rectangles (redact_rectangles), not API ones
    #     for rect in reversed(self.redact_rectangles):  # Reverse to get top-most first
    #         if rect['page'] != self.current_page:
    #             continue
    #         x1, y1 = rect['x1'] * zoom, rect['y1'] * zoom
    #         x2, y2 = rect['x2'] * zoom, rect['y2'] * zoom
    #         if x1 <= x <= x2 and y1 <= y <= y2:
    #             # Delete from canvas
    #             self.canvas.delete(rect['id'])
                
    #             # Delete from PDF
    #             page = self.pdf_document.load_page(self.current_page)
    #             rect_pdf = fitz.Rect(rect['x1'], rect['y1'], rect['x2'], rect['y2'])
    #             for annot in page.annots():
    #                 if annot.rect == rect_pdf:
    #                     annot.delete()
    #                     break
                
    #             # Remove from local lists
    #             self.redact_rectangles.remove(rect)
    #             if rect in self.redact_annotations:
    #                 self.redact_annotations.remove(rect)
                
    #             # Also remove from API lists since locally drawn rectangles are added there too
    #             if rect in self.redact_api_rectangles:
    #                 self.redact_api_rectangles.remove(rect)
    #                 self.add_pagesize.pop(rect['id'], None)
    #             if rect in self.redact_api_annotations:
    #                 self.redact_api_annotations.remove(rect)
    #             print("self.add_pagesize.pop(rect)-",self.add_pagesize)
    #             self.render_page(self.current_page)  # Re-render the page to reflect changes
    #             self.change_redact_history.append(('delete_annotation', rect))
    #             self.annotation_is_available = bool(self.redact_annotations + self.redact_api_annotations)
    #             break


# ----------------------------------------------------------------------------------------------------------------------------------------------------------
    # best one for now for local db
    
    # def redraw_black_rectangles_from_db(self):
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return

    #     try:
    #         sql_query = "SELECT coordinate, pagesize, zoomsize FROM redact_info WHERE doc_id = %s"
    #         mycursor.execute(sql_query, (str(self.doc_id),))
    #         rows = mycursor.fetchall()
    #         print("rows from db---",rows)
    #         for coord_str, saved_pagesize_str, saved_zoom in rows:
    #             print("coord_str---", coord_str)
    #             coord = eval(coord_str)  # Consider using json.loads for safety
    #             print("coord after eval---", coord)
    #             saved_pagesize = eval(saved_pagesize_str)
    #             print("saved_pagesize---", saved_pagesize)

    #             if coord['page'] != self.current_page:
    #                 continue

    #             if saved_pagesize[0] != self.page_width:
    #                 pagewidther = self.page_width
    #                 pageheighter = self.page_height
    #             else:
    #                 pagewidther = saved_pagesize[0]
    #                 pageheighter = saved_pagesize[1]

    #             # Scale coordinates
    #             scale_x = self.page_width / pagewidther
    #             scale_y = self.page_height / pageheighter

    #             x1 = coord['x1'] * scale_x * self.zoom_factor
    #             y1 = coord['y1'] * scale_y * self.zoom_factor
    #             x2 = coord['x2'] * scale_x * self.zoom_factor
    #             y2 = coord['y2'] * scale_y * self.zoom_factor

    #             # Draw on canvas only (not embedded into the PDF)
    #             rect_id = self.canvas.create_rectangle(
    #                 x1, y1, x2, y2,
    #                 outline="black", fill="black" if coord['filled'] else "", width=3, tags="annotation"
    #             )

    #             # Track it for undo/redo
    #             rect_data = {
    #                 'type': 'rectangle', 'page': self.current_page,
    #                 'x1': x1 / self.zoom_factor, 'y1': y1 / self.zoom_factor,
    #                 'x2': x2 / self.zoom_factor, 'y2': y2 / self.zoom_factor,
    #                 'filled': coord['filled'], 'id': rect_id, 'color': "black"
    #             }
    #             self.redact_rectangles.append(rect_data)
    #             self.redact_annotations.append(rect_data)

    #     except Exception as e:
    #         print(f"Error fetching or redrawing black rectangles from DB: {e}")

## -------------------------------------------------------------------------------------------------------------------------------------------------------

    # def redraw_black_rectangles_from_api(self):
    #     """Load and draw all rectangles from API for all pages."""
    #     if not self.pdf_document:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
        
    #     try:
    #         url = f"https://idms-dev.blockchaincloudapps.com/api/v1/get-pdf-viewer-redact-info?temp_id={self.temp_id}"
    #         # url = f"http://172.20.1.239:5000/api/v1/get-pdf-viewer-redact-info?temp_id={self.temp_id}"
    #         print("redact url---", url)
    #         headers = {'Content-Type': 'application/json'}
    #         response = requests.get(url, headers=headers, timeout=10)
            
    #         if response.status_code != 200:
    #             print("Failed to fetch redaction data:", response.text)
    #             return
                
    #         response_data = response.json()
    #         # print("redactions from api---", response_data)
    #         result = [(item["coordinate"], item["page_size"], item["zoom_size"]) for item in response_data["data"]]
    #         # print("result from api---", result)
            
    #         # Clear existing API rectangles to avoid duplicates
    #         self.redact_api_rectangles.clear()
    #         self.redact_api_annotations.clear()
            
    #         for coord_str, saved_pagesize_str, saved_zoom in result:
    #             # print("coord_str---", coord_str)
    #             coord = eval(coord_str)  # Consider using json.loads for safety
    #             # print("coord after eval---", coord)
    #             saved_pagesize = eval(saved_pagesize_str)
    #             # print("saved_pagesize---", saved_pagesize)
                
    #             page_num = coord['page']
                
    #             # Initialize page in dictionary if not exists
    #             if page_num not in self.all_page_rectangles:
    #                 self.all_page_rectangles[page_num] = []
                
    #             # Get page dimensions for scaling
    #             page = self.pdf_document.load_page(page_num)
    #             page_width, page_height = page.rect.width, page.rect.height
                
    #             if saved_pagesize[0] != page_width:
    #                 pagewidther = page_width
    #                 pageheighter = page_height
    #             else:
    #                 pagewidther = saved_pagesize[0]
    #                 pageheighter = saved_pagesize[1]
                    
    #             scale_x = page_width / pagewidther
    #             scale_y = page_height / pageheighter
                
    #             # Store rectangle data for this page
    #             rect_data = {
    #                 'type': 'rectangle', 
    #                 'page': page_num,
    #                 'x1': coord['x1'] * scale_x, 
    #                 'y1': coord['y1'] * scale_y,
    #                 'x2': coord['x2'] * scale_x, 
    #                 'y2': coord['y2'] * scale_y,
    #                 'filled': coord['filled'], 
    #                 'color': "black",
    #                 'source': 'api',
    #                 'canvas_id': None  # Will be set when drawn on canvas
    #             }
                
    #             self.all_page_rectangles[page_num].append(rect_data)
    #             self.redact_api_annotations.append(rect_data)
            
    #         # Draw rectangles for current page only
    #         self._draw_rectangles_for_current_page()
            
    #     except Exception as e:
    #         print(f"Error fetching redaction data from API: {e}")

#----------------------------------------------currently was using this one -------------------------------------------------------------
    def redraw_black_rectangles_from_api(self):
        """Load and draw all rectangles from API for all pages."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        try:
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            print("self.temp_id-----------------------------------------------------------------------------",self.temp_id)
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            url = f"https://idms-dev.blockchaincloudapps.com/api/v1/get-pdf-viewer-redact-info?temp_id={self.temp_id}"
            # url = f"http://172.20.1.60:5000/api/v1/get-pdf-viewer-redact-info?temp_id={self.temp_id}"
            headers = {
                            'Authorization': 'Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJmcmVzaCI6ZmFsc2UsImlhdCI6MTc1NTY2NzY3NywianRpIjoiMWViZThiODAtZTJiZS00MmZkLWIxZWMtNmU2MmI4NWFlOTNkIiwidHlwZSI6ImFjY2VzcyIsInN1YiI6ImRob25pIiwibmJmIjoxNzU1NjY3Njc3LCJjc3JmIjoiZGIxN2UzNzYtOGVlYi00YmI1LTk0MTctZWMyMWJmMjQ1YzgxIiwiZXhwIjoxNzU1NjY4NTc3fQ.oXKx53IBNUtYP575pm53b7WyR8RJXB5jxt1amUdG_wk',
                            'Content-Type': 'application/json'
                        }
            response = requests.get(url, headers=headers, timeout=10)
            if response.status_code != 200:
                print("Failed to fetch redaction data:", response.text)
                return
            response_data = response.json()
            print("redactions from api---", response_data["data"])
            result = [(item["coordinate"], item["page_size"], item["zoom_size"], item["rotation_degree"]) for item in response_data["data"]]
            print("result from api---", result)
            # Clear existing data
            self.redact_api_rectangles.clear()
            self.redact_api_annotations.clear()
            self.all_page_rectangles = {}  # Dictionary to store rectangles by page number
            
            for coord_str, saved_pagesize_str, saved_zoom, rotated_degree in result:
                coord = eval(coord_str)  # Consider using json.loads for safety
                saved_pagesize = eval(saved_pagesize_str)
                page_num = coord['page']
                self.rotated_from_api = eval(rotated_degree)
                if page_num not in self.all_page_rectangles:
                    self.all_page_rectangles[page_num] = []
                page = self.pdf_document.load_page(page_num)
                page_width, page_height = page.rect.width, page.rect.height
                if saved_pagesize[0] != page_width:
                    pagewidther = page_width
                    pageheighter = page_height
                else:
                    pagewidther = saved_pagesize[0]
                    pageheighter = saved_pagesize[1]
                scale_x = page_width / pagewidther
                scale_y = page_height / pageheighter
                rect_data = {
                    'type': 'rectangle', 
                    'page': page_num,
                    'x1': coord['x1'] * scale_x, 
                    'y1': coord['y1'] * scale_y,
                    'x2': coord['x2'] * scale_x, 
                    'y2': coord['y2'] * scale_y,
                    'filled': coord['filled'], 
                    'color': "black",
                    'source': 'api',
                    'canvas_id': None  # Will be set when drawn on canvas
                }
                self.all_page_rectangles[page_num].append(rect_data)
                self.redact_api_annotations.append(rect_data)
            
            # Always draw rectangles after loading (default behavior)
            self._draw_rectangles_for_current_page()
                
        except Exception as e:
            print(f"Error fetching redaction data from API: {e}")

    def _draw_rectangles_for_current_page(self):
        """Draw rectangles for the current page with rotation support."""
        if self.current_page is None or not hasattr(self, 'all_page_rectangles'):
            return

        # Clear existing annotation rectangles
        self.canvas.delete("annotation")

        # Only draw if redact is visible
        if not getattr(self, 'redact_visible', True):
            return
        
        rotation_angle = self.pdf_document[self.current_page].rotation
        page_width, page_height = self.page_width, self.page_height

        if self.current_page in self.all_page_rectangles:
            for rect_data in self.all_page_rectangles[self.current_page]:
                rect_rotate = rect_data['rotated'] if 'rotated' in rect_data else rotation_angle
                x1 = rect_data['x1'] * self.zoom_factor
                y1 = rect_data['y1'] * self.zoom_factor
                x2 = rect_data['x2'] * self.zoom_factor
                y2 = rect_data['y2'] * self.zoom_factor

                fill_color = "black" if rect_data.get('filled') else ""
                kwargs = {
                    "outline": "black",
                    "fill": fill_color,
                    "width": 3,
                    "tags": "annotation"
                }

                if rotation_angle == 0:
                    rect_id = self.canvas.create_rectangle(x1, y1, x2, y2, **kwargs)
                else:
                    corners = [(x1, y1), (x2, y1), (x2, y2), (x1, y2)]
                    rotated = []
                    for x, y in corners:
                        rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
                        rotated.extend([rx, ry])
                    rect_id = self.canvas.create_polygon(rotated, **kwargs)

                rect_data['canvas_id'] = rect_id
# ---------------------------------------------------------------------------------------------------------------------------------------------------------------------

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
                is_small_page = "nope very large"
            else:
                is_small_page = "no"
            print("is_small_page----",is_small_page)
            self.current_page += 1
            self.render_page(self.current_page)
            self.update_thumbnail_selection(self.current_page)
            self.update_page_display()

if __name__ == "__main__":
    handler = ProtocolHandler()
    if not handler.verify_registration():
        try:
            success, message = handler.register()
            print(message if success else f"Warning: {message}")
        except Exception as e:
            print(f"Failed to register protocol handler: {e}")

    root = ctk.CTk()
    app = StickyNotesPDFApp(root)
    root.mainloop()





