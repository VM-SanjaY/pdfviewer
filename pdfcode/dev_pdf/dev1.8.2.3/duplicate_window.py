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
import time
import uuid
import json
from datetime import date, datetime
import tkinter as tk
import cairosvg
import fitz
import textwrap
from shapely.geometry import Point, Polygon
from PIL import Image, ImageTk, ImageOps, ImageSequence
import requests
from urllib.parse import urlparse, unquote, parse_qs, urlunparse, urlencode
import socket
import threading
import sys
import customtkinter as ctk
from tkinter import filedialog, messagebox
import mysql.connector
from dotenv import load_dotenv

# to get the environment variables for exe
base_dir = getattr(sys, '_MEIPASS', os.path.abspath(os.path.dirname(__file__)))
env_path = os.path.join(base_dir, '.env')

# ✅ Load .env from the correct location
load_dotenv(env_path)


# host = os.getenv("MYSQL_HOST")
# user = os.getenv("MYSQL_USER")
# password = os.getenv("MYSQL_PASSWORD")
# database = os.getenv("MYSQL_DATABASE")

# mydb = mysql.connector.connect(
#     host="127.0.0.1",
#     user="root",
#     password="root",
#     database="redact_viewer"
# )

# mycursor = mydb.cursor()

class DuplicateStickyNotesPDFApp:
    def __init__(self, root, fileurl):
        server_url = fileurl.split(".com")[0]
        part1, part2 = self.split_url(fileurl)
        params = parse_qs(part2.lstrip("?"))
        self.is_freeze = params.get("is_freeze", [""])[0]
        self.lasttime_freeze = params.get("is_freeze", [""])[0]
        self.view_redact = params.get("view_redact", [""])[0]
        self.root = root
        # Set minimum size for the window to prevent excessive shrinking
        self.file_name_is = "attachment_file.pdf"
        # icon for the window title
        self.root.iconbitmap(self.set_window_icon(os.path.join('assets', 'Atic.png')))
        self.zoom_factor = 1.0
        self.freeeze_count = 0
        self.highlight_rectangles = {}
        self.display_name = ""
        self.active_highlight = False
        self.redact_visible = False
        self.active_stickynote = False
        self.active_hollowrectangle = False
        self.active_filledrectangle = False
        self.active_hollowellipse = False
        self.active_filledellipse = False
        self.active_freehandline = False
        self.active_hollowpolgon = False
        self.active_filledpolygon = False
        self.active_deleteannotation = False
        self.activedeleteredact_button = False
        self.active_line = False
        self.active_arrow = False
        self.active_redact = False
        self.file_date_time = ""
        self.time_redact_used = 0
        self.rendered_page_count = 0
        self.lock_screen = "no"
        self.stickynotezoomy = 1.0
        self.annotation_is_available = False
        self.redact_is_available = False
        self.page_rotation = 0
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.is_drawing_line = False
        self.is_drawing_arrow = False
        self.is_drawing_hollow_rect = False  # For hollow rectangle tool
        self.is_drawing_filled_rect = False
        self.is_drawing_hollow_circle = False  # Initialize the attribute
        self.is_drawing_filled_circle = False  # Initialize for filled circle too
        self.last_x, self.last_y = None, None
        self.current_line = None
        self.current_rectangle = None
        self.dragged_line_id = None
        self.line_drag_start = None
        self.rect_drag_start = None
        self.active_highlight = False
        self.dragged_sticky_note = None
        self.sticky_note_drag_start = None
        self.line_total_drag_dx = 0
        self.line_total_drag_dy = 0
        self.dragged_text_bg_key = None
        self.dragged_text_bg_id = None  
        self.text_bg_drag_start = None
        self.dragged_ellipse_id = None
        self.ellipse_drag_start = None
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
        # Track scroll position and reset attempts
        self.last_scroll_position = 0
        self._scroll_reset_job = None
        self._selection_attempts = 0
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
        # api to save the annotated and redact file
        # recieving the url from the protocol handler
        # server_url = "http://172.20.1.218:3001/api/v1"
        self.server_url = server_url+r".com/api/v1/uploads/file-annotations"
        self.logger_recorder = "https://idms-dev.blockchaincloudapps.com/api/v1/insert-pdf-viewer-audit"     
        print("server url-----------------------------------------------------------------------------------------------",self.server_url)

        if self.is_freeze == "true":
            self.root.after(0, lambda: self.root.title(f"Secondary IDMS Viewer - {self.display_name} {self.file_date_time} - View Only Mode" ))
        else:
            self.root.after(0, lambda: self.root.title(f"Secondary IDMS Viewer - {self.display_name} {self.file_date_time}"))
        self.handle_url(fileurl)

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
        toolbar_container = ctk.CTkFrame(self.root)
        toolbar_container.pack(fill=ctk.X, pady=8)
        if self.is_freeze == "false":
            toolbar_canvas = ctk.CTkCanvas(toolbar_container, height=80, highlightthickness=0)
        else:
            toolbar_canvas = ctk.CTkCanvas(toolbar_container, height=40, highlightthickness=0)
        toolbar_canvas.pack(side=ctk.TOP, fill=ctk.X, expand=True)
        
        # Create scrollbar but don't pack it initially
        toolbar_scrollbar = ctk.CTkScrollbar(toolbar_container, orientation="horizontal", command=toolbar_canvas.xview)
        toolbar_canvas.configure(xscrollcommand=toolbar_scrollbar.set)
        
        toolbar = ctk.CTkFrame(toolbar_canvas)
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
        toolbar.configure(width=min_toolbar_width)
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
                width=60
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
            if self.view_redact == "true":
                if self.lock_screen == "no":
                    button_configs = [
                        {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Annotations","instance_var":"Lock_button"},
                        {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area","instance_var":"selectzoom_button"},
                        # {"image": self.icons['eye'], "command": self.show_annotated_file, "tooltip": "Show Annotated File"},
                        {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Document"},
                        {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                        {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                        # {"image": self.icons['zoom_area'], "command": self.toggle_zoom_in_area_mode, "tooltip": "Zoom Area"},
                        {"image": self.icons['highlight'], "command": self.enable_highlight_mode, "tooltip": "Highlight","instance_var":"highlight_button"},
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
                        # {"image": self.icons['save_pdf'], "command": self.save_pdf_type2, "tooltip": "Save PDF"},
                        # Buttons with instance variables
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
                        # {"image": self.icons['redact'], "command": self.toggle_redaction_mode, "tooltip": "Add Redaction"},
                        # {"image": self.icons['removeredact'], "command": self.remove_black_boxes, "tooltip": "Remove Redaction"},
                        {"image": self.icons['redact'], "command": self.activate_black_rectangle_tool, "tooltip": "Add Redaction", "instance_var": "redact_button"},
                        {"image": self.icons['removeredact'], "command": self.enable_undo_blackrect, "tooltip": "Delete Redaction","instance_var":"deleteredact_button"},
                        {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
                        # {"image": self.icons['redact'], "command": self.redraw_black_rectangles_from_db, "tooltip": "redraw from db"},
                        # {"image": self.icons['redact'], "command": self.redraw_black_rectangles_from_api, "tooltip": "redraw from api"},
                    ]
                else:
                    button_configs = [
                        {"image": self.icons['unlock'], "command": self.lock_function, "tooltip": "Unlock Annotations","instance_var":"Lock_button"},
                        {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                        {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                        {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                        {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                        {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                        {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                        {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                        {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                    ]
            else:
                if self.lock_screen == "no":
                    button_configs = [
                        {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Annotations","instance_var":"Lock_button"},
                        {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area","instance_var":"selectzoom_button"},
                        # {"image": self.icons['eye'], "command": self.show_annotated_file, "tooltip": "Show Annotated File"},
                        {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Document"},
                        {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                        {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                        # {"image": self.icons['zoom_area'], "command": self.toggle_zoom_in_area_mode, "tooltip": "Zoom Area"},
                        {"image": self.icons['highlight'], "command": self.enable_highlight_mode, "tooltip": "Highlight","instance_var":"highlight_button"},
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
                        # {"image": self.icons['save_pdf'], "command": self.save_pdf_type2, "tooltip": "Save PDF"},
                        # Buttons with instance variables
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
                        # {"image": self.icons['redact'], "command": self.toggle_redaction_mode, "tooltip": "Add Redaction"},
                        # {"image": self.icons['removeredact'], "command": self.remove_black_boxes, "tooltip": "Remove Redaction"},
                        {"image": self.icons['redact'], "command": self.activate_black_rectangle_tool, "tooltip": "Add Redaction", "instance_var": "redact_button"},
                        {"image": self.icons['removeredact'], "command": self.enable_undo_blackrect, "tooltip": "Delete Redaction","instance_var":"deleteredact_button"},
                        {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
                        # {"image": self.icons['redact'], "command": self.redraw_black_rectangles_from_db, "tooltip": "redraw from db"},
                        # {"image": self.icons['redact'], "command": self.redraw_black_rectangles_from_api, "tooltip": "Show Redact"},
                        {"image": self.icons['show'], "command": self.toggle_redact_display, "tooltip": "Show / hide Redact","instance_var":"redacttoggle_button"},
                    ]
                else:
                    button_configs = [
                        {"image": self.icons['unlock'], "command": self.lock_function, "tooltip": "Unlock Annotations","instance_var":"Lock_button"},
                        {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
                        {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
                        {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
                        {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
                        {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
                        {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
                        {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
                        {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
                    ]
        else:
            button_configs = [
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
        rows_container = ctk.CTkFrame(toolbar)
        rows_container.pack(side=ctk.TOP, fill=ctk.BOTH)
        current_row = ctk.CTkFrame(rows_container)
        current_row.pack(side=ctk.TOP, fill=ctk.X)
        buttons_in_row = 0
        # Add buttons with row wrapping
        for config in button_configs:
            if buttons_in_row >= 23:  # Start a new row when we hit 23 buttons
                current_row = ctk.CTkFrame(rows_container)
                current_row.pack(side=ctk.TOP, fill=ctk.X)
                buttons_in_row = 0
            
            button = create_button(
                current_row,
                image=config["image"],
                command=config["command"],
                tooltip_text=config["tooltip"])
            
            buttons_in_row += 1
            
            if "instance_var" in config:
                setattr(self, config["instance_var"], button)
        # button frame         
        nav_frame = ctk.CTkFrame(current_row, height=25)  # Place inside current_frame    
        nav_frame.pack(side=ctk.LEFT, pady=0, padx=5)  # Align with buttons

        # navigation buttons
        prev_button = ctk.CTkButton(nav_frame, text="<<<", command=self.prev_page, width=30, fg_color="transparent", text_color="black")
        prev_button.pack(side=ctk.LEFT, padx=0)
        # button for page jump
        self.page_entry = ctk.CTkEntry(nav_frame, width=45, justify="center", height=20)
        self.page_entry.pack(side=ctk.LEFT, padx=0)
        self.page_entry.insert(0, "1")
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
            self.h_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="horizontal", command=self.canvas.xview)
            self.v_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="vertical", command=self.canvas.yview)
            self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
            self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
            self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
            self.canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
            # mouse wheel event for pdf render window for scrolling the pdf render
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
            self.account_name = params.get("account_name", [""])[0]
            self.timer_id = params.get("timer_id", [""])[0]
            self.doc_id = params.get("doc_id", [""])[0]
            self.user_id = params.get("user_id", [""])[0]
            self.current_is_freeze = params.get("is_freeze", [""])[0]
            self.display_name = params.get("display_name", [""])[0]
            self.timer_id = params.get("timer_id", [""])[0]
            self.is_freeze = params.get("is_freeze", [""])[0]
            self.temp_id = params.get("temp_id", [""])[0]
            self.file_date_time = params.get("date_time", [""])[0]
            self.view_redact = params.get("view_redact", [""])[0]
            self.pagenumber_url = int(params.get("page_number", [1])[0])
            self.pdf_file_url = part1
            self.show_loader()
            # Load PDF in background to avoid UI blocking
            threading.Thread(target=self.load_pdf_and_finalize, args=(url, start_time), daemon=True).start()
        except Exception as e:
            print(f"Failed to load PDF in handle_url: {e}")

    def load_pdf_and_finalize(self, url, start_time):
        try:
            def finalize_after_load():
                end_time = time.time()
                self.rendered_time_cal = f"{end_time - start_time:.2f} sec"
                print(f"Secondary viewer loaded in {self.rendered_time_cal}")
                if self.is_freeze == "true":
                    self.root.after(0, lambda: self.root.title(f"Secondary Viewer v1.8.2.2 - {self.display_name} {self.file_date_time}  - View only mode"))
                else:
                    self.root.after(0, lambda: self.root.title(f"Secondary Viewer v1.8.2.2 - {self.display_name} {self.file_date_time}"))
                self.hide_loader()
            self.load_pdf(url, on_complete=finalize_after_load)

        except Exception as e:
            print(f"Error in load_pdf_and_finalize: {e}")
    

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
        
        # Create canvas for animation with parent's background
        canvas_size = 150
        
        # Get the parent's background color to simulate transparency
        parent_bg = self.root.cget('bg')
        
        self.loader_canvas = tk.Canvas(
            self.root, 
            width=canvas_size, 
            height=canvas_size,
            bg="lightgray",  # Use parent's background color
            highlightthickness=0,
            relief='flat',
            borderwidth=0
        )
        self.loader_canvas.place(relx=0.5, rely=0.5, anchor="center")
        
        # Animation parameters
        self.angle = 0
        self.circle_radius = 50  # Radius of the circular path
        self.dot_radius = 8      # Size of the moving dot
        center_x = canvas_size // 2
        center_y = canvas_size // 2
        
        def animate():
            # Clear canvas
            self.loader_canvas.delete("all")
            
            # Calculate position of the circling dot
            x = center_x + self.circle_radius * math.cos(math.radians(self.angle))
            y = center_y + self.circle_radius * math.sin(math.radians(self.angle))
            
            # Draw the main circle path (optional - shows the track)
            self.loader_canvas.create_oval(
                center_x - self.circle_radius, center_y - self.circle_radius,
                center_x + self.circle_radius, center_y + self.circle_radius,
                outline='lightblue', width=2
            )
            
            # Draw the moving blue dot
            self.loader_canvas.create_oval(
                x - self.dot_radius, y - self.dot_radius,
                x + self.dot_radius, y + self.dot_radius,
                fill='blue', outline='darkblue', width=2
            )
            
            # Add a subtle shadow/trail effect
            for i in range(1, 4):
                trail_angle = self.angle - i * 15
                trail_x = center_x + self.circle_radius * math.cos(math.radians(trail_angle))
                trail_y = center_y + self.circle_radius * math.sin(math.radians(trail_angle))
                alpha = 1 - (i * 0.3)  # Fade effect
                trail_color = f'#{int(135*alpha):02x}{int(206*alpha):02x}{int(235*alpha):02x}'
                
                self.loader_canvas.create_oval(
                    trail_x - (self.dot_radius - i), trail_y - (self.dot_radius - i),
                    trail_x + (self.dot_radius - i), trail_y + (self.dot_radius - i),
                    fill=trail_color, outline=''
                )
            
            # Update angle for next frame
            self.angle = (self.angle + 8) % 360  # 8 degrees per frame
            
            # Schedule next frame
            self.loader_animation = self.root.after(50, animate)  # 50ms = ~20 FPS
        
        animate()


    def hide_loader(self):
        """Hide the loader animation."""
        if hasattr(self, 'loader_animation'):
            self.root.after_cancel(self.loader_animation)
        if hasattr(self, 'loader_canvas'):
            self.loader_canvas.destroy()

    def toggle_redact_display(self):
        """Toggle visibility of all redaction rectangles across all pages."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
            
        if not hasattr(self, 'redact_visible'):
            self.redact_visible = False
        
        if not getattr(self, 'thumbnails_ready', False):
            messagebox.showwarning("Wait", "Please wait thumbnail is loading....", parent=self.root)
            return
            
        if self.redact_visible:
            # Hide redactions
            self.redacttoggle_button.configure(
                image=self.icons['show'],
                fg_color="#00498f",
                hover_color="#023261"
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
                image=self.icons['hide'],
                fg_color="#d17a24", 
                hover_color="#b56e26"
            )
            
            # Re-render thumbnails with rectangles
            self.render_thumbnails()


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
        self.redactions.clear()
        self.line_total_drag_dx = 0
        self.line_total_drag_dy = 0
        self.dragged_rectangle_id = None
        self.thumbnails_ready = False
        self.rect_drag_start = None
        self.dragged_line_id = None
        self.line_drag_start = None
        self.dragged_ellipse_id = None
        self.ellipse_drag_start = None
        self.redo_redactions.clear()
        self.image_overlays.clear()
        self.text_annotations.clear()
        self.text_annotations_bg.clear()
        self.page_drawings.clear()
        self.polygons.clear()
        self.rendered_page_count = 0
        self.is_drawing_hollow_rect = False
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
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")], parent=self.root)
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
                    self.hide_loader()
                    return

                if len(self.pdf_document) == 0:
                    raise ValueError("The PDF has no pages.")

                self.current_page = int(self.pagenumber_url) - 1 if self.pagenumber_url is not None else 0
                self.pagenumber_url = None
                self.page_drawings.clear()
                self.is_inverted = False

                first_page = self.pdf_document[self.current_page]
                self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
                print(f"Page size: width {self.page_width} x hight {self.page_height}")
                global is_small_page
                if self.page_width < 1000:
                    is_small_page = "yes"
                elif 2000 < self.page_width < 3000 and self.page_height > 2800:
                    is_small_page = "longer"
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
                if self.view_redact == "true":
                    print("View Redact is enabled, loading redacted annotations.")
                    self.redraw_black_rectangles_from_api()
                self.root.after(0, self.hide_loader)
                self.root.after(0, self._timed_render_thumbnails)
                self.root.after(100, lambda: self.ensure_thumbnail_selection(self.current_page))
                self.update_page_display()
                self._process_file_url(file_path)
                if on_complete:
                    self.root.after(0, on_complete)
            except Exception as e:
                print(f"Failed to load PDF: {e}")
                self.hide_loader()
                messagebox.showerror("Error", f"Failed to load PDF: 400 Bad URL Request", parent=self.root)
                self.pdf_document = None
                self.current_page = None

        threading.Thread(target=task).start()

##########################################################################################################################################################################################

    def render_thumbnails(self):
        if not self.pdf_document:
            print("No PDF document loaded for thumbnails.")
            return
        for widget in self.inner_thumbnail_frame.winfo_children():
            widget.destroy()
        self.thumbnails.clear()
        self.thumbnail_cache.clear()
        self.thumbnails_ready = False
        global thumb_color
        thumb_color = []
        thumbnail_width = 100
        thumbnail_height = 150
        total_pages = len(self.pdf_document)
        
        def load_thumbnails_worker():
            for page_number in range(total_pages):
                if page_number in self.thumbnail_cache:
                    continue
                try:
                    page = self.pdf_document.load_page(page_number)
                    pix = page.get_pixmap(matrix=fitz.Matrix(0.5, 0.5))
                    img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                    
                    # Add redaction rectangles to thumbnail if they exist and redact is visible
                    try:
                        if (hasattr(self, 'all_page_rectangles') and 
                            page_number in self.all_page_rectangles and 
                            self.all_page_rectangles[page_number]):
                            img = self._add_rectangles_to_thumbnail(img, page_number, pix.width, pix.height)
                    except:
                        if (hasattr(self, 'redact_visible') and self.redact_visible and 
                            hasattr(self, 'all_page_rectangles') and page_number in self.all_page_rectangles):
                            img = self._add_rectangles_to_thumbnail(img, page_number, pix.width, pix.height)
                    
                    img.thumbnail((thumbnail_width, thumbnail_height), Image.LANCZOS)
                    photo = ImageTk.PhotoImage(img)
                    self.thumbnail_cache[page_number] = photo
                    self.inner_thumbnail_frame.after(0, lambda pn=page_number, ph=photo: add_thumbnail(pn, ph))
                except Exception as e:
                    print(f"Error rendering thumbnail for page {page_number}: {e}")
            self.inner_thumbnail_frame.after(500, self.update_scroll_region)
            self.inner_thumbnail_frame.after(600, lambda: self.thumbnail_canvas.yview_moveto(0))
            self.inner_thumbnail_frame.after(700, lambda: self.update_thumbnail_selection(self.current_page))
            self.inner_thumbnail_frame.after(800, lambda: setattr(self, 'thumbnails_ready', True))
        
        def add_thumbnail(page_number, photo):
            label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
            label.image = photo
            label.page_number = page_number  # Store the page number directly on the label
            if total_pages > 50:
                row = page_number // 2
                col = page_number % 2
                label.grid(row=row, column=col, padx=5, pady=5, sticky="w")
            else:
                label.pack(pady=5, padx=45)
            label.bind("<Button-1>", self.create_page_selection_handler(page_number))
            self.thumbnails.append(label)
            thumb_color.append(label)

        threading.Thread(target=load_thumbnails_worker, daemon=True).start()
        

    def _add_rectangles_to_thumbnail(self, img, page_number, pix_width, pix_height):
        """Add redaction rectangles to thumbnail image."""
        from PIL import ImageDraw
        
        if page_number not in self.all_page_rectangles:
            return img
        
        # Convert to RGB if not already
        if img.mode != 'RGB':
            img = img.convert('RGB')
        
        draw = ImageDraw.Draw(img)
        
        # Get the original page dimensions
        page = self.pdf_document.load_page(page_number)
        page_width, page_height = page.rect.width, page.rect.height
        
        # Calculate scale factors for thumbnail
        scale_x = pix_width / page_width
        scale_y = pix_height / page_height
        
        for rect_data in self.all_page_rectangles[page_number]:
            # Scale rectangle coordinates to thumbnail size
            x1 = int(rect_data['x1'] * scale_x)
            y1 = int(rect_data['y1'] * scale_y)
            x2 = int(rect_data['x2'] * scale_x)
            y2 = int(rect_data['y2'] * scale_y)
            
            # Draw rectangle on thumbnail
            if rect_data['filled']:
                draw.rectangle([x1, y1, x2, y2], fill='black', outline='black', width=1)
            else:
                draw.rectangle([x1, y1, x2, y2], outline='black', width=1)
        
        return img
    
# ###########################################################################################################################################################################################
    def create_page_selection_handler(self, page_number):
        """Return a handler function to navigate to the selected page."""
        def handler(event):
            print(f"Thumbnail {page_number} clicked. Current page before: {self.current_page}")  # Debug log
            self.select_page(page_number)
            print(f"Current page after: {self.current_page}")  # Debug log
        return handler

    def update_thumbnail_selection(self, page_number):
        """Update the highlight of the selected thumbnail and ensure it's visible in the scroll view."""
        print(f"Updating thumbnail selection to page {page_number}")  # Debug log
        
        # Reset all thumbnails to default appearance
        for i, label in enumerate(thumb_color):
            label.configure(
                text=f"Page {i + 1}",  # Use index instead of thumb_color.index()
                text_color="black",
                fg_color="transparent",
                corner_radius=0
            )
            if hasattr(label, "original_image"):
                label.configure(image=label.original_image)
        
        # Highlight the selected thumbnail
        if 0 <= page_number < len(thumb_color):
            selected_label = thumb_color[page_number]
            selected_label.configure(
                text="Selected Page", 
                text_color="red",    
                fg_color="#c41818", 
                corner_radius=4, 
                compound="center"
            )
            self.inner_thumbnail_frame.update_idletasks()
            self.selected_label_info = selected_label
            self.root.after(100, lambda: self.scroll_to_thumbnail(selected_label, page_number))


    def select_page(self, page_number):
        """Handle thumbnail click event to switch pages."""
        print(f"select_page called with page_number: {page_number}")  # Debug log
        
        if 0 <= page_number < len(self.pdf_document):
            print(f"Valid page number. Setting current_page from {self.current_page} to {page_number}")
            self.current_page = page_number
            
            # Clear any existing page drawings for the new page
            if hasattr(self, 'page_drawings'):
                # Keep only drawings for the current page
                # self.page_drawings = [d for d in self.page_drawings if d.get('page') == page_number]
                if isinstance(self.page_drawings, list):
                    self.current_page_drawings = [d for d in self.page_drawings if isinstance(d, dict) and d.get('page') == page_number]

            
            # Render the selected page
            self.render_page(self.current_page)
            self.update_page_display()
            self.update_thumbnail_selection(page_number)
            
            print(f"Page selection completed. Current page is now: {self.current_page}")
        else:
            print(f"Invalid page number: {page_number}. Total pages: {len(self.pdf_document)}")


    def lock_function(self):
        
        self.lock_screen = "yes" if self.lock_screen == "no" else "no"

        current_page_number = self.current_page
        current_pdf = self.pdf_document

        # Destroy all widgets safely
        for widget in self.root.winfo_children():
            widget.destroy()

        # Reset widget references before re-creating
        self.canvas = None
        self.thumbnail_canvas = None
        self.thumbnail_frame = None
        self.inner_thumbnail_frame = None
        self.thumbnail_labels = []
        self.thumbnails = []
        self.thumbnail_cache = {}

        # Re-create all widgets
        self.create_widgets()
        if self.lock_screen == "yes":
            self.Lock_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        else:
            self.Lock_button.configure(fg_color="#00498f",hover_color="#023261")

        # Restore the PDF and page view
        if current_pdf and current_page_number is not None:
            self.pdf_document = current_pdf
            self.current_page = current_page_number

            self.render_page(self.current_page)

            # Delay thumbnail rendering slightly to ensure canvas is ready
            self.root.after(150, self.render_thumbnails)

            self.update_page_display()
            self.root.after(1000, lambda: self.update_thumbnail_selection(self.current_page))

            self.canvas.config(cursor="arrow")
            self.canvas.bind("<Motion>", self.on_mouse_hover)
            self.page_entry.delete(0, "end")
            self.page_entry.insert(0, str(self.current_page + 1))
            self.page_total_label.configure(text=f"/ {len(self.pdf_document)}")


    # increase the page size by .2 ever time.
    def zoom_in(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
        self.zoom_factor += 0.2
        self.redraw_blackrectangles(rotation_angle)
        self.render_page(self.current_page)
    # decrease the page size by .2 ever time.    
    def zoom_out(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        if self.zoom_factor > 0.4:
            self.zoom_factor -= 0.2
            self.redraw_blackrectangles(rotation_angle)
            self.render_page(self.current_page)
    # to render the page in perfect fit in width or height to see all the content
    def best_fit(self):
        """Adjust the zoom level to fit the entire PDF page within the canvas."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()

        page = self.pdf_document.load_page(self.current_page)
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
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
                messagebox.showerror("Error", "Invalid page number.", parent=self.root)
        except ValueError:
            messagebox.showerror("Error", "Enter a valid page number.", parent=self.root)

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
        fraction = max(0.0, min(1.0, fraction - offset))
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
        
        # If the position has changed significantly, reset it to our target
        if abs(current_position - target_position) > 0.05:  # Allow small variations
            self.thumbnail_canvas.yview_moveto(target_position)
            
            # Schedule another check to make sure it sticks
            self._scroll_reset_job = self.root.after(200, lambda: self._ensure_scroll_position(target_position))
        else:
            self._scroll_reset_job = None


    # to remove all the changes by reloading the url again
    def refresh(self):
        """
        Prompts the user to save the file and reloads the PDF if confirmed.
        If the user declines, nothing happens.
        """
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        # self.thumbnails_rendered = False

        url = "https://idms-backend.blockchaincloudapps.com/api/v1/folder/pdf-viewer/"+self.doc_id
        response = requests.request("GET", url)
        json_data = response.json()
        annotations_path = json_data["data"]["annotations_document_path"]
        print("annotations_path------------------",annotations_path)
        base_url = self.load_pdf_url.split("documents/")[0] + "documents/"
        query_string = self.load_pdf_url.split("?")[1]
        # Construct the new URL
        new_url = f"{base_url}{annotations_path}?{query_string}"
        response = messagebox.askyesnocancel("Confirm", "Would you like to save the file before refreshing? Any unsaved changes will be permanently lost.", parent=self.root)
        if response is None:
            return
        elif response:
            try:
                self.save_pdf()
                self.load_pdf(new_url, on_complete=None)
            except Exception as e:
                print(f"Error saving PDF before refresh: {e}")
        else:
            # User clicked 'No', just refresh without saving
            self.load_pdf(new_url, on_complete=None)

    # to show the width in perfect width to see all the content as per window width
    def best_width(self):
        """Adjust the zoom level to fit the entire PDF page to the canvas width."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return

        canvas_width = self.canvas.winfo_width()
        page = self.pdf_document.load_page(self.current_page)
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
        page_width = page.rect.width

        self.zoom_factor = canvas_width / page_width
        self.render_page(self.current_page)

    # to show the height in perfect height to see all the content as per window height
    def best_height(self):
        """Adjust the zoom level to fit the entire PDF page to the canvas height."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return

        canvas_height = self.canvas.winfo_height()
        page = self.pdf_document.load_page(self.current_page)
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
        page_height = page.rect.height

        self.zoom_factor = canvas_height / page_height
        self.render_page(self.current_page)

    def render_page(self, page_number):
        """Render a PDF page to the canvas with the current zoom factor."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
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
        # if hasattr(self, 'redact_visible') and self.redact_visible:
        #     self._draw_rectangles_for_current_page()
        # Draw rectangles for current page if redact is visible
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

    def redraw_image_overlays(self, page_number):
        """Redraw image overlays for the current page with proper scaling and rotation."""
        if not hasattr(self, "image_overlays"):
            self.image_overlays = []
            return
        self.canvas.delete("image_overlay")
        self.tk_images = {}  # Reset the tk_images dictionary
        
        rotation_angle = 0
        if self.pdf_document:
            page = self.pdf_document[page_number]
            rotation_angle = page.rotation
        
        page_width = self.page_width
        page_height = self.page_height
        
        current_page_overlays = [overlay for overlay in self.image_overlays if overlay["page"] == page_number]
        
        for overlay in current_page_overlays:
            try:
                # Get base coordinates and dimensions (unscaled)
                base_x = overlay["base_x"]
                base_y = overlay["base_y"]
                base_width = overlay["base_width"]
                base_height = overlay["base_height"]
                
                # Apply zoom scaling
                scaled_x = base_x * self.zoom_factor
                scaled_y = base_y * self.zoom_factor
                scaled_width = base_width * self.zoom_factor
                scaled_height = base_height * self.zoom_factor
                
                # Apply rotation transformation
                # For proper positioning, we need to rotate coordinates based on rotation angle
                if rotation_angle == 0:
                    rotated_x, rotated_y = scaled_x, scaled_y
                    display_width, display_height = scaled_width, scaled_height
                else:
                    # For rotations, we need to handle the center point of the image
                    # Calculate the position from the center of the original image
                    center_x_orig = scaled_x + (scaled_width / 2)
                    center_y_orig = scaled_y + (scaled_height / 2)
                    
                    # Use rotate_point to get the rotated position
                    rotated_center_x, rotated_center_y = self.rotate_point(
                        center_x_orig, center_y_orig, 
                        page_width, page_height, 
                        rotation_angle)
                    
                    # Swap dimensions for 90° and 270° rotations
                    if rotation_angle in [90, 270]:
                        display_width, display_height = scaled_height, scaled_width
                    else:
                        display_width, display_height = scaled_width, scaled_height
                    
                    # Calculate the top-left corner from the center point
                    rotated_x = rotated_center_x - (display_width / 2)
                    rotated_y = rotated_center_y - (display_height / 2)
                
                # Update overlay with new coordinates
                overlay["x"] = rotated_x
                overlay["y"] = rotated_y
                overlay["width"] = display_width
                overlay["height"] = display_height
                
                # Load and prepare the image
                img = Image.open(overlay["image_path"])
                
                # Rotate the image if needed
                if rotation_angle != 0:
                    pil_rotation = {
                        90: 270,  # PIL uses counter-clockwise rotation
                        180: 180,
                        270: 90
                    }.get(rotation_angle, 0)
                    img = img.rotate(pil_rotation, expand=True)
                
                # Resize the image
                img = img.resize((int(display_width), int(display_height)), Image.LANCZOS)
                
                # Convert to Tkinter PhotoImage
                tk_img = ImageTk.PhotoImage(img)
                self.tk_images[overlay["id"]] = tk_img
                
                # Create the image on canvas
                canvas_id = self.canvas.create_image(
                    rotated_x, rotated_y,
                    image=tk_img,
                    anchor="nw",
                    tags=("image_overlay", overlay["id"]))
                    
                overlay["canvas_id"] = canvas_id
                
            except Exception as e:
                print(f"Failed to redraw image overlay: {e}")

    def redraw_all_annotations(self):
        """Redraw all annotations on the current page with proper rotation"""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation  # Get current page rotation
        
        self.redraw_lines(rotation_angle)
        self.redraw_arrows(rotation_angle)
        self.redraw_rectangles(rotation_angle)
        self.redraw_blackrectangles(rotation_angle)
        self.redraw_apiblackrectangles(rotation_angle)
        self.redraw_ellipses(rotation_angle)


    def redraw_lines(self, rotation_angle=0):
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
        self.canvas.delete("apirectangle")
        page_width, page_height = self.page_width, self.page_height
        
        for annotation in self.redact_api_rectangles:
            print("annotation ------------------",annotation)
            if annotation['page'] == self.current_page:
                # Apply zoom factor to coordinates
                x1 = annotation['x1'] * self.zoom_factor
                y1 = annotation['y1'] * self.zoom_factor
                x2 = annotation['x2'] * self.zoom_factor
                y2 = annotation['y2'] * self.zoom_factor
                
                # For rectangles, we need to rotate all four corners
                corners = [
                    (x1, y1),
                    (x2, y1),
                    (x2, y2),
                    (x1, y2)
                ]
                
                # Rotate each corner
                rotated_corners = []
                for x, y in corners:
                    rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
                    rotated_corners.extend([rx, ry])
                
                outline_color = annotation['color']
                fill_color = "" if not annotation['filled'] else annotation['color']
                
                # Draw as polygon instead of rectangle to handle rotation
                self.canvas.create_polygon(
                    rotated_corners,
                    outline=outline_color, fill=fill_color, 
                    width=3, tags=("annotation", "apirectangle"))

    def redraw_blackrectangles(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation"""
        self.canvas.delete("rectangle")
        page_width, page_height = self.page_width, self.page_height
        
        for annotation in self.redact_rectangles:
            print("annotation ------------------",annotation)
            if annotation['page'] == self.current_page:
                # Apply zoom factor to coordinates
                x1 = annotation['x1'] * self.zoom_factor
                y1 = annotation['y1'] * self.zoom_factor
                x2 = annotation['x2'] * self.zoom_factor
                y2 = annotation['y2'] * self.zoom_factor
                
                # For rectangles, we need to rotate all four corners
                corners = [
                    (x1, y1),
                    (x2, y1),
                    (x2, y2),
                    (x1, y2)
                ]
                
                # Rotate each corner
                rotated_corners = []
                for x, y in corners:
                    rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
                    rotated_corners.extend([rx, ry])
                
                outline_color = annotation['color']
                fill_color = "" if not annotation['filled'] else annotation['color']
                
                # Draw as polygon instead of rectangle to handle rotation
                self.canvas.create_polygon(
                    rotated_corners,
                    outline=outline_color, fill=fill_color, 
                    width=3, tags=("annotation", "rectangle"))

    def redraw_rectangles(self, rotation_angle=0):
        """Redraw all rectangle annotations for the current page with rotation"""
        self.canvas.delete("red_rectangle")
        page_width, page_height = self.page_width, self.page_height
        print("self.rectangles------------------", self.rectangles)
        
        for annotation in self.rectangles:
            print("annotation ------------------", annotation)
            if annotation['page'] == self.current_page:
                x1 = annotation['x1'] * self.zoom_factor
                y1 = annotation['y1'] * self.zoom_factor
                x2 = annotation['x2'] * self.zoom_factor
                y2 = annotation['y2'] * self.zoom_factor
                
                if rotation_angle == 0:
                    # No rotation - use rectangle for better performance and interaction
                    outline_color = annotation['color']
                    fill_color = "" if not annotation['filled'] else annotation['color']
                    
                    rect_id = self.canvas.create_rectangle(
                        x1, y1, x2, y2,
                        outline=outline_color, fill=fill_color, 
                        width=4, tags=("annotation", "red_rectangle"))
                    
                    # Update the stored ID and bind events
                    annotation['id'] = rect_id
                    self.canvas.tag_bind(rect_id, "<Button-1>", self.on_rectangle_press)
                    self.canvas.tag_bind(rect_id, "<B1-Motion>", self.on_rectangle_drag)
                    self.canvas.tag_bind(rect_id, "<ButtonRelease-1>", self.on_rectangle_release)
                else:
                    # With rotation - use polygon
                    corners = [
                        (x1, y1),
                        (x2, y1),
                        (x2, y2),
                        (x1, y2)]
                    
                    rotated_corners = []
                    for x, y in corners:
                        rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
                        rotated_corners.extend([rx, ry])
                    
                    outline_color = annotation['color']
                    fill_color = "" if not annotation['filled'] else annotation['color']
                    border_width = 4 if not annotation['filled'] else 3
                    rect_id = self.canvas.create_polygon(
                        rotated_corners,
                        outline=outline_color, fill=fill_color, 
                        width=border_width, tags=("annotation", "red_rectangle"))
                    
                    # Update the stored ID and bind events
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
        
        for annotation in ellipse_annotations:
            _, x1, y1, x2, y2, _, mode,numb = annotation
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
                
                # Calculate the four corners of the bounding box
                corners = [
                    (x1, y1),  # Top-left
                    (x2, y1),  # Top-right
                    (x2, y2),  # Bottom-right
                    (x1, y2)   # Bottom-left
                ]
                
                # Rotate each corner
                rotated_corners = []
                for corner_x, corner_y in corners:
                    rx, ry = self.rotate_point(corner_x, corner_y, 
                                            self.page_width, self.page_height, 
                                            rotation_angle)
                    rotated_corners.append((rx, ry))
                
                # Find bounding box of rotated corners
                rotated_x_coords = [p[0] for p in rotated_corners]
                rotated_y_coords = [p[1] for p in rotated_corners]
                rotated_x1 = min(rotated_x_coords)
                rotated_y1 = min(rotated_y_coords)
                rotated_x2 = max(rotated_x_coords)
                rotated_y2 = max(rotated_y_coords)
                
                # Generate ellipse points
                num_points = 72
                points = []
                
                # Calculate center and radii of the original ellipse
                cx = (x1 + x2) / 2
                cy = (y1 + y2) / 2
                rx = abs(x2 - x1) / 2
                ry = abs(y2 - y1) / 2
                
                # Generate points around the ellipse and rotate each point
                for i in range(num_points):
                    angle = 2 * math.pi * i / num_points
                    point_x = cx + rx * math.cos(angle)
                    point_y = cy + ry * math.sin(angle)
                    
                    # Rotate this point according to page rotation
                    rotated_point_x, rotated_point_y = self.rotate_point(
                        point_x, point_y, 
                        self.page_width, self.page_height, 
                        rotation_angle
                    )
                    points.extend([rotated_point_x, rotated_point_y])
                
                fill = "" if mode == "hollow" else "orange"
                ellipse_id = self.canvas.create_polygon(
                    points,
                    outline="orange", width=3, fill=fill,
                    smooth=True, tags=("ellipse", "annotation"))
                self.canvas.tag_bind(ellipse_id, "<Button-1>", self.on_ellipse_press)
                self.canvas.tag_bind(ellipse_id, "<B1-Motion>", self.on_ellipse_drag)
                self.canvas.tag_bind(ellipse_id, "<ButtonRelease-1>", self.on_ellipse_release)
                for i, ann in enumerate(self.annotations):
                    if isinstance(ann, tuple) and ann[0] == 'ellipse' and ann[5] == annotation[5] and ann[7] == self.current_page:
                        self.annotations[i] = (ann[0], ann[1], ann[2], ann[3], ann[4], ellipse_id, ann[6], ann[7])
                        break
                for j, hist in enumerate(self.change_history):
                    if hist[0] == "ellipse" and hist[5] == annotation[5]:
                        self.change_history[j] = ("ellipse", annotation[1], annotation[2], annotation[3], annotation[4], ellipse_id, annotation[6])
                                


    def rotate_point(self, x, y, page_width, page_height, rotation_angle):
        """Rotate a point (x, y) based on the given rotation angle."""
        if rotation_angle == 90:
            if is_small_page == "yes":
                rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y, x
            elif is_small_page == "slightly":
                rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y, x
            elif is_small_page == "maybe":
                rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y, x
            elif is_small_page == "longer":
                print("rhdttjfykfkyf buka buka")
                rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y, x
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
            elif is_small_page == "slightly":
                rotated_x, rotated_y =y, self.page_width-(1050*self.zoom_factor) - x
            elif is_small_page == "longer":
                rotated_x, rotated_y = y, self.page_width-(720*self.zoom_factor) - x
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

    def redraw_polygons(self):
        """Redraw all polygons, adjusting for zoom and rotation properly."""
        if not self.pdf_document or self.current_page is None:
            return

        self.canvas.delete("polygon")
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation  # Get current page rotation

        if self.current_page not in self.page_drawings:
            return

        page_width, page_height = self.page_width, self.page_height  # Get current page dimensions

        for mode, points, polygon_id in self.page_drawings[self.current_page]:
            scaled_points = [coord * self.zoom_factor for coord in points]

            rotated_points = []
            for i in range(0, len(scaled_points), 2):
                x, y = scaled_points[i], scaled_points[i + 1]
                new_x, new_y = self.rotate_point(x, y, page_width, page_height, rotation_angle)
                rotated_points.extend([new_x, new_y])

            polygon_id = self.canvas.create_polygon(
                rotated_points,
                fill="blue" if mode == "filled" else "",
                outline="blue" if mode == "filled" else "red",
                width=4,
                tags=("polygon",),
            )

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
                    elif is_small_page == "slightly":
                        rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
                    elif is_small_page == "longer":
                        rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
                    elif is_small_page == "nope large":
                        rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
                    elif is_small_page == "nope very large":
                        rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
                    else:
                        rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position
                elif rotation_angle == 180:
                    rotated_x = page_width - x_position
                    rotated_y = page_height - y_position
                elif rotation_angle == 270:
                    if is_small_page == "yes":
                        rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
                    elif is_small_page == "slightly":
                        rotated_x, rotated_y =y_position, self.page_width-(1050*self.zoom_factor) - x_position
                    elif is_small_page == "longer":
                        rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
                    elif is_small_page == "nope large":
                        rotated_x, rotated_y = y_position, self.page_height-(1000*self.zoom_factor)- x_position
                    elif is_small_page == "nope very large":
                        rotated_x, rotated_y = y_position, self.page_height-(4300*self.zoom_factor)- x_position
                    else:
                        rotated_x, rotated_y = y_position, self.page_height-(2000*self.zoom_factor) - x_position
           
                else:  # 0 degrees
                    rotated_x = x_position
                    rotated_y = y_position

                canvas_id = self.canvas.create_image(
                    rotated_x, rotated_y,
                    image=self.icons['thumb_pin'],
                    anchor="center",
                    tags="sticky_note"
                )
                self.sticky_note_ids[(page_num, x_scaled, y_scaled)] = canvas_id
                self.canvas.tag_bind(canvas_id, "<ButtonPress-1>", self.on_sticky_note_press)
                self.canvas.tag_bind(canvas_id, "<B1-Motion>", self.on_sticky_note_drag)
                self.canvas.tag_bind(canvas_id, "<ButtonRelease-1>", self.on_sticky_note_release)
        self.annotation_is_available = True
        self.root.update_idletasks()

    def on_sticky_note_press(self, event):
        self.sticky_note_drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
        self.dragged_sticky_note = self.canvas.find_withtag("current")[0]

    def on_sticky_note_drag(self, event):
        if self.dragged_sticky_note is not None and self.sticky_note_drag_start:
            x_start, y_start = self.sticky_note_drag_start
            x_current = self.canvas.canvasx(event.x)
            y_current = self.canvas.canvasy(event.y)
            dx = x_current - x_start
            dy = y_current - y_start
            self.canvas.move(self.dragged_sticky_note, dx, dy)
            self.sticky_note_drag_start = (x_current, y_current)

    def on_sticky_note_release(self, event):
        if self.dragged_sticky_note is None:
            return
        new_bbox = self.canvas.bbox(self.dragged_sticky_note)
        if not new_bbox:
            return
        x_center = (new_bbox[0] + new_bbox[2]) / 2
        y_center = (new_bbox[1] + new_bbox[3]) / 2
        x_scaled = x_center / self.zoom_factor
        y_scaled = y_center / self.zoom_factor

        # Find the old key (sticky note position) by matching the dragged canvas ID
        old_key = None
        for key, cid in self.sticky_note_ids.items():
            if cid == self.dragged_sticky_note:
                old_key = key
                break

        if old_key:
            text = self.sticky_notes.pop(old_key)
            self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = text
            self.sticky_note_ids.pop(old_key)
            self.sticky_note_ids[(self.current_page, x_scaled, y_scaled)] = self.dragged_sticky_note

        self.dragged_sticky_note = None
        self.sticky_note_drag_start = None

  
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

        self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
        print("Sticky note added at:", x_scaled, y_scaled)
        print("Sticky notes:----",self.change_history)
        # Safely retrieve the icon for sticky notes
        self.annotation_is_available = True
        sticky_icon = self.icons.get("thumb_pin")
        if sticky_icon:
            # self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
            canvas_id = self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
            self.sticky_note_ids[(self.current_page, x_scaled, y_scaled)] = canvas_id
            self.canvas.tag_bind(canvas_id, "<ButtonPress-1>", self.on_sticky_note_press)
            self.canvas.tag_bind(canvas_id, "<B1-Motion>", self.on_sticky_note_drag)
            self.canvas.tag_bind(canvas_id, "<ButtonRelease-1>", self.on_sticky_note_release)
        else:
            print("Warning: 'sticky_note' icon not found.")  # Refresh to apply the changes
        self.sticky_note_button.configure(fg_color="#00498f",hover_color="#023261")
        self.annotation_listed.append("sticky_note")

    def ask_for_note_text(self, x, y, title):
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

        # Set focus after the dialog is fully loaded
        dialog.after(100, text_box.focus_set)

        note_text_var = ctk.StringVar()

        def on_ok_click():
            note_text = text_box.get("1.0", "end").strip()
            if note_text:
                note_text_var.set(note_text)
                dialog.destroy()
            else:
                messagebox.showerror("Empty Note", "You must enter some text to save the sticky note.", parent=self.root)

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
    
    def delete_annotation_at_point(self, event):
        click_x = self.canvas.canvasx(event.x) / self.zoom_factor
        click_y = self.canvas.canvasy(event.y) / self.zoom_factor
        click_point = fitz.Point(click_x, click_y)
        click_poly = Point(click_x, click_y)
        page = self.pdf_document[self.current_page]
        

        # --- Step 1: Delete PDF annotations (highlight, text, sticky note, etc.) ---
        annot = page.first_annot
        print("annotation------------------",annot)
        print("click_point------------------",click_point)
        print("click_poly------------------",click_poly)
        print("change_history------------------",self.change_history)
        print("self.polygon_cord---------------------------------------",self.polygon_cord)
        print("self.annotation_listed---------------------------------------",self.annotation_listed)
        

        while annot:
            rect = annot.rect
            if rect.contains(click_point):
                annot_type = annot.type[0]

                # Delete PDF-based annotation
                page.delete_annot(annot)

                # Remove from history for highlight, text, text_bg, sticky_note
                self.change_history = [
                    entry for entry in self.change_history
                    if not (
                        entry[0] in ("highlight", "add_text", "add_text_bg", "sticky_note")
                        and entry[1] == self.current_page
                    )
                ]
                self.render_page(self.current_page)
                return
            annot = annot.next

        # Handle deleting sticky note
        for (page_num, x_scaled, y_scaled), note_text in list(self.sticky_notes.items()):
            if page_num == self.current_page:
                icon_x = x_scaled * self.zoom_factor
                icon_y = y_scaled * self.zoom_factor
                page = self.pdf_document[self.current_page]
                rotation_angle = page.rotation
                page_width = page.rect.width * self.zoom_factor
                page_height = page.rect.height * self.zoom_factor
                if rotation_angle == 90:
                    if is_small_page == "yes":
                        rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - icon_y, icon_x
                    elif is_small_page == "slightly":
                        rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - icon_y, icon_x
                    elif is_small_page == "longer":
                        rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - icon_y, icon_x
                    elif is_small_page == "maybe":
                        rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - icon_y, icon_x
                    elif is_small_page == "nope large":
                        rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - icon_y, icon_x
                    elif is_small_page == "nope very large":
                        rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - icon_y, icon_x
                    else:
                        rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - icon_y, icon_x
                elif rotation_angle == 180:
                    rotated_x = page_width - icon_x
                    rotated_y = page_height - icon_y
                elif rotation_angle == 270:
                    if is_small_page == "yes":
                        rotated_x, rotated_y = icon_y, self.page_width-(180*self.zoom_factor) - icon_x
                    elif is_small_page == "slightly":
                        rotated_x, rotated_y = icon_y, self.page_width-(1050*self.zoom_factor) - icon_x
                    elif is_small_page == "longer":
                        rotated_x, rotated_y = icon_y, self.page_width-(720*self.zoom_factor) - icon_x 
                    elif is_small_page == "maybe":
                       rotated_x, rotated_y = icon_y, self.page_width-(750*self.zoom_factor) - icon_x 
                    elif is_small_page == "nope large":
                        rotated_x, rotated_y = icon_y, self.page_width-(1000*self.zoom_factor) - icon_x
                    elif is_small_page == "nope very large":
                        rotated_x, rotated_y = icon_y, self.page_width-(4300*self.zoom_factor) - icon_x
                    else:
                        rotated_x, rotated_y = icon_y, self.page_height-(2000*self.zoom_factor) - icon_x
                else:
                    rotated_x = icon_x
                    rotated_y = icon_y

                click_distance = ((event.x - rotated_x)**2 + (event.y - rotated_y)**2) ** 0.5
                if click_distance <= 15:  # Assuming ~30px diameter clickable area
                    del self.sticky_notes[(page_num, x_scaled, y_scaled)]
                    self.change_history = [
                        entry for entry in self.change_history
                        if not (entry[0] == "sticky_note" and entry[1] == self.current_page and
                                entry[2] == x_scaled and entry[3] == y_scaled)
                    ]
                    self.render_page(self.current_page)
                    return

        # --- Step 2: Canvas-based items ---
        for entry in reversed(self.change_history):
            action_type = entry[0]
            # Polygon
            if action_type == "polygon":
                for poly_data in self.polygon_cord:             
                    poly_page = poly_data[0]
                    poly_id = poly_data[1]
                    polygon_dia = poly_data[2]
                    print("polygon_dia ------------------",polygon_dia)
                    polygon_points = list(zip(polygon_dia[::2], polygon_dia[1::2]))
                    polygon = Polygon(polygon_points)
                    is_inside = polygon.contains(click_poly)
                    if poly_page == self.current_page:
                        if is_inside:
                            print("action_type ------------------",action_type)
                            _, page, prev_state, polygon_id = entry
                            for i, (mode, points, pid) in enumerate(self.page_drawings[page]):
                                if pid == poly_id:
                                    if prev_state is None:
                                        # Undo polygon creation (remove it)
                                        self.canvas.delete(poly_id)
                                        del self.page_drawings[page][i]
                                        for x in self.polygon_cord:
                                            if x[0] == self.current_page:
                                                if x[1] == poly_id:
                                                    self.polygon_cord.remove(x)
                                                    break
                                    else:
                                        # Restore previous state (undo move/reshape)
                                        self.page_drawings[page][i] = (mode, prev_state, poly_id)
                                        self.canvas.coords(poly_id, prev_state)
                                    break
                            self.render_page(self.current_page)

            # Freehand
            if action_type == "freehand":
                _, _, line_id, _ = entry
                bbox = self.canvas.bbox(line_id)
                if bbox and bbox[0] <= click_x * self.zoom_factor <= bbox[2] and bbox[1] <= click_y * self.zoom_factor <= bbox[3]:
                    self.canvas.delete(line_id)
                    self.change_history.remove(entry)
                    self.render_page(self.current_page)
                    return
                
            # Rectangle, Line and Arrow
            elif action_type == "add_annotation":
                annotation_data = entry[1]
                annotation_type = annotation_data.get("type")
                canvas_id = annotation_data.get("id")
                if annotation_type in ("rectangle", "line", "arrow"):
                    x1 = annotation_data.get("x1")
                    y1 = annotation_data.get("y1")
                    x2 = annotation_data.get("x2")
                    y2 = annotation_data.get("y2")
                    if x1 is not None and y1 is not None and x2 is not None and y2 is not None:
                        # Convert to canvas coordinates
                        x1_scaled = x1 * self.zoom_factor
                        y1_scaled = y1 * self.zoom_factor
                        x2_scaled = x2 * self.zoom_factor
                        y2_scaled = y2 * self.zoom_factor
                        min_x = min(x1_scaled, x2_scaled)
                        max_x = max(x1_scaled, x2_scaled)
                        min_y = min(y1_scaled, y2_scaled)
                        max_y = max(y1_scaled, y2_scaled)
                        if min_x <= event.x <= max_x and min_y <= event.y <= max_y:
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

            # Ellipse
            elif action_type == "ellipse":
                if len(entry) >= 7:
                    _, x1, y1, x2, y2, ellipse_id, _ = entry
                    if self.is_point_inside_ellipse(click_x, click_y, x1, y1, x2, y2):
                        self.canvas.delete(ellipse_id)
                        self.annotations = [
                            a for a in self.annotations
                            if not (isinstance(a, tuple) and a[0] == "ellipse" and len(a) > 5 and a[5] == ellipse_id)
                            # if not (isinstance(a, tuple) and a[0] == "ellipse" and a[5] == ellipse_id)
                        ]
                        self.change_history.remove(entry)
                        self.render_page(self.current_page)
                        return
            # Ellipse when moved
            elif action_type == "move_annotation":
                if len(entry) >= 3:
                    old_ann, new_ann = entry[1], entry[2]
                    if isinstance(new_ann, tuple) and new_ann[0] == "ellipse" and len(new_ann) >= 6:
                        x1, y1, x2, y2 = new_ann[1], new_ann[2], new_ann[3], new_ann[4]
                        ellipse_id = new_ann[5]
                        if self.is_point_inside_ellipse(click_x, click_y, x1, y1, x2, y2):
                            self.canvas.delete(ellipse_id)
                            self.annotations = [
                                a for a in self.annotations
                                if not (isinstance(a, tuple) and a[0] == "ellipse" and len(a) > 5 and a[5] == ellipse_id)
                                # if not (isinstance(a, tuple) and a[0] == "ellipse" and a[5] == ellipse_id)
                            ]
                            # Also remove original and move entry
                            self.change_history = [
                                e for e in self.change_history
                                if not (
                                    (e[0] == "ellipse" and len(e) > 5 and e[5] == ellipse_id) or
                                    (e[0] == "move_annotation" and len(e) > 2 and e[2][5] == ellipse_id)
                                )
                            ]
                            self.render_page(self.current_page)
                            return
            # Image overlay
            elif action_type == "image_overlay":
                _, page_no, overlay_info = entry
                if page_no == self.current_page and "canvas_id" in overlay_info:
                    coords = self.canvas.bbox(overlay_info["canvas_id"])
                    if coords and coords[0] <= click_x * self.zoom_factor <= coords[2] and coords[1] <= click_y * self.zoom_factor <= coords[3]:
                        self.canvas.delete(overlay_info["canvas_id"])
                        if hasattr(self, "tk_images") and overlay_info["id"] in self.tk_images:
                            del self.tk_images[overlay_info["id"]]
                        self.image_overlays = [i for i in self.image_overlays if i["id"] != overlay_info["id"]]
                        self.change_history.remove(entry)
                        self.render_page(self.current_page)
                        return

            # Text and Text with Background
            elif action_type in ("add_text", "add_text_bg"):
                _, page, old_x, old_y, text = entry
                if page == self.current_page:
                    annotation_dict = self.text_annotations if action_type == "add_text" else self.text_annotations_bg

                    # Try to find closest matching key with tolerance
                    matched_key = None
                    for key in annotation_dict:
                        if key[0] == page and abs(key[1] - old_x) < 1e-2 and abs(key[2] - old_y) < 1e-2:
                            matched_key = key
                            break

                    if matched_key and isinstance(annotation_dict[matched_key], dict):
                        bbox = annotation_dict[matched_key].get("bbox")
                        canvas_id = annotation_dict[matched_key].get("canvas_id")
                        bg_id = annotation_dict[matched_key].get("bg_rect_id")

                        if bbox:
                            x1, y1, x2, y2 = bbox
                            click_px = click_x * self.zoom_factor
                            click_py = click_y * self.zoom_factor
                            if x1 <= click_px <= x2 and y1 <= click_py <= y2:
                                if canvas_id:
                                    self.canvas.delete(canvas_id)
                                if bg_id:
                                    self.canvas.delete(bg_id)
                                del annotation_dict[matched_key]

                                # Also delete from PDF if needed
                                page_obj = self.pdf_document[page]
                                annot = page_obj.first_annot
                                while annot:
                                    if annot.info and annot.info.get("contents") == text:
                                        page_obj.delete_annot(annot)
                                        break
                                    annot = annot.next

                                self.change_history.remove(entry)
                                self.render_page(self.current_page)
                                return


    def enable_delete_highlight_mode(self):
        self.deactivate_tools()
        self.canvas.bind("<Button-1>", self.delete_highlight_at_point)

    def delete_highlight_at_point(self, event):
        click_x = self.canvas.canvasx(event.x) / self.zoom_factor
        click_y = self.canvas.canvasy(event.y) / self.zoom_factor
        click_point = fitz.Point(click_x, click_y)

        page = self.pdf_document[self.current_page]
        annot = page.first_annot
        while annot:
            if annot.type[0] == 8:  # Highlight annotation
                if annot.rect.contains(click_point):
                    # Optional: also match by 'id' and remove from change_history
                    page.delete_annot(annot)
                    self.render_page(self.current_page)
                    return
            annot = annot.next


    def undo_change(self):
        print("Undoing the last change...",self.change_history)
        if not self.change_history:
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
            if self.annotation_listed[-1]=="highlight":
                self.annotation_listed.pop()
        
        elif action_type == "freehand":
            _, page, line_id, _ = last_action
            # Remove from the canvas
            self.canvas.delete(line_id)
            # Remove from history
            self.change_history = [entry for entry in self.change_history if entry[2] != line_id]
            # Redraw remaining freehand drawings to refresh the canvas
            self.redraw_freehand_drawings()
            self.render_page(self.current_page)
            if self.annotation_listed[-1]=="freehand":
                self.annotation_listed.pop()
        
        elif action_type == "add_annotation":
            # New code for undoing line, arrow, rectangle, and ellipse annotations
            annotation_data = last_action[1]
            annotation_type = annotation_data.get('type')
            
            # Remove from canvas
            if 'id' in annotation_data:
                self.canvas.delete(annotation_data['id'])
            
            # Remove from appropriate list
            if annotation_type == 'line':
                self.lines = [line for line in self.lines if line != annotation_data]
                if self.annotation_listed[-1]=="line":
                    self.annotation_listed.pop()
            elif annotation_type == 'arrow':
                self.arrows = [arrow for arrow in self.arrows if arrow != annotation_data]
                if self.annotation_listed[-1]=="arrow":
                    self.annotation_listed.pop()
            elif annotation_type == 'rectangle':
                self.rectangles = [rect for rect in self.rectangles if rect != annotation_data]
                if self.annotation_listed[-1]=="rectangle":
                    self.annotation_listed.pop()
            # Remove from annotations list
            self.annotations = [ann for ann in self.annotations 
                            if not (isinstance(ann, dict) and ann.get('id') == annotation_data.get('id'))]
            self.render_page(self.current_page)

        elif action_type == "ellipse":
            # Handle ellipse annotations
            _, x1, y1, x2, y2, ellipse_id, mode = last_action
            if ellipse_id:
                self.canvas.delete(ellipse_id)
            # Remove from annotations list
            ellipse_to_remove = None
            for ann in self.annotations:
                if isinstance(ann, tuple) and ann[0] == 'ellipse' and ann[1] == x1 and ann[2] == y1 and ann[3] == x2 and ann[4] == y2:
                    ellipse_to_remove = ann
                    break
            if ellipse_to_remove:
                self.annotations.remove(ellipse_to_remove)
            if self.annotation_listed[-1]=="ellipse":
                self.annotation_listed.pop()
            self.render_page(self.current_page)

        elif action_type == "move_annotation":
            old_ann, new_ann = last_action[1], last_action[2]
            if isinstance(old_ann, tuple) and old_ann[0] == "ellipse":
                for i, ann in enumerate(self.annotations):
                    if isinstance(ann, tuple) and ann[0] == "ellipse" and ann[5] == new_ann[5] and ann[7] == self.current_page:
                        self.annotations[i] = old_ann
                        break
                self.canvas.delete(new_ann[5])
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
            if self.annotation_listed[-1]=="text_bg":
                self.annotation_listed.pop()
            elif self.annotation_listed[-1]=="text":
                self.annotation_listed.pop()

        elif action_type == "polygon":
            _, page, prev_state, polygon_id = last_action
            if page in self.page_drawings:
                for i, (mode, points, pid) in enumerate(self.page_drawings[page]):
                    if pid == polygon_id:
                        if prev_state is None:
                            # Undo polygon creation (remove it)
                            self.canvas.delete(polygon_id)
                            del self.page_drawings[page][i]
                        else:
                            # Restore previous state (undo move/reshape)
                            self.page_drawings[page][i] = (mode, prev_state, polygon_id)
                            self.canvas.coords(polygon_id, prev_state)
                        break
                self.render_page(self.current_page)
            if self.annotation_listed[-1]=="polygon":
                self.annotation_listed.pop()

        elif action_type == "sticky_note":
            _, page, x_scaled, y_scaled, _ = last_action
            if (page, x_scaled, y_scaled) in self.sticky_notes:
                del self.sticky_notes[(page, x_scaled, y_scaled)]
                if self.annotation_listed[-1]=="sticky_note":
                    self.annotation_listed.pop()
                self.render_page(self.current_page)

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

        else:
            print(f"Unknown action type: {action_type}")

    def deactivate_colour(self, valu, deact=None):
        """Deactivate the color button"""
        list_of_buttons = [self.selectzoom_button, self.highlight_button, self.sticky_note_button, 
                           self.delete_button, self.text_button, self.text_bg_button, self.draw_button, 
                           self.filled_polygon_button, self.hollow_polygon_button, self.image_button, 
                           self.line_button, self.arrow_button, self.hollow_rectangle_button, 
                           self.filled_rectangle_button, self.hollow_ellipse_button, self.filled_ellipse_button, 
                           self.redact_button,self.deleteredact_button]
        

        deactivating_function = ["active_highlight", "active_deleteannotation", "active_freehandline", "active_filledpolygon", "active_hollowpolgon", "active_line", "sticky_note_mode",
                "active_arrow", "active_hollowrectangle", "active_filledrectangle", "active_hollowellipse", "active_filledellipse", "active_redact", "activedeleteredact_button"]
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

    # def enable_highlight_mode(self):
    #     """ Activate highlight mode """
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
    #         return
    #     if self.active_highlight:
    #         self.highlight_button.configure(fg_color="#00498f",hover_color="#023261")
    #         self.canvas.unbind("<B1-Motion>")
    #         self.canvas.unbind("<ButtonRelease-1>")
    #         self.deactivate_tools()
    #         self.active_highlight = False
    #         return
    #     self.active_highlight = True   
    #     self.deactivate_tools()
    #     self.highlight_mode = True    
    #     self.highlight_button.configure(fg_color="#d17a24", hover_color="#b56e26")
    #     self.deactivate_colour(self.highlight_button,"active_highlight")
    #     self.is_drawing_hollow_rect = False
    #     self.is_drawing_filled_rect = False
    #     self.canvas.bind("<Button-1>", self.start_highlight_rectangle)
    #     self.canvas.bind("<B1-Motion>", self.draw_highlight_rectangle)
    #     self.canvas.bind("<ButtonRelease-1>", self.finalize_highlight)

    # def start_highlight_rectangle(self, event):
    #     """Start a rectangle selection for highlighting"""
    #     self.start_x = self.canvas.canvasx(event.x)
    #     self.start_y = self.canvas.canvasy(event.y)
        
    #     # Delete any existing highlight preview
    #     if self.rectangle_id:
    #         self.canvas.delete(self.rectangle_id)
        
    #     # Draw the initial rectangle immediately
    #     self.rectangle_id = self.canvas.create_rectangle(
    #         self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
    #         outline="yellow", width=2)

    # def draw_highlight_rectangle(self, event):
    #     """Draw the rectangle dynamically as the mouse is dragged."""
    #     if self.rectangle_id is None:
    #         return  # Prevents calling coords on None
        
    #     current_x = self.canvas.canvasx(event.x)
    #     current_y = self.canvas.canvasy(event.y)
    #     # Update rectangle coordinates safely
    #     self.canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)


    # def finalize_highlight(self, event):
    #     """Finalize the highlight and save it to the PDF."""
    #     if self.start_x is None or self.start_y is None:
    #         return
    #     end_x = self.canvas.canvasx(event.x) / self.zoom_factor
    #     end_y = self.canvas.canvasy(event.y) / self.zoom_factor
    #     start_x = self.start_x / self.zoom_factor
    #     start_y = self.start_y / self.zoom_factor
    #     rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
    #     page = self.pdf_document[self.current_page]
    #     rotation = page.rotation
    #     page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor
    #     if rotation == 90:
    #         rect = fitz.Rect(
    #             rect.y0,
    #             page_width - rect.x1,
    #             rect.y1,
    #             page_width - rect.x0)
    #     elif rotation == 180:
    #         rect = fitz.Rect(
    #             page_width - rect.x1,
    #             page_height - rect.y1,
    #             page_width - rect.x0,
    #             page_height - rect.y0)
    #     elif rotation == 270:
    #         rect = fitz.Rect(
    #             page_height - rect.y1,
    #             rect.x0,
    #             page_height - rect.y0,
    #             rect.x1)
    #     try:
    #         highlight = page.add_highlight_annot(rect)
    #         highlight.update()
    #         highlight.set_border(width=0, dashes=(0, 0))
    #         annot_id = highlight.info.get('id')
    #         # changes_data = ("highlight", self.current_page, annot_id)
    #         # changes_data = str(changes_data)
    #         # if annot_id:
    #         #     sql_check = """
    #         #         SELECT COUNT(*) FROM pdf_editor_details 
    #         #         WHERE folder_path = %s AND filename = %s AND changes_data = %s
    #         #     """
    #         #     mycursor.execute(sql_check, (self.doc_id, beforeexe, changes_data))
    #         #     result = mycursor.fetchone()
    #         #     if result[0] == 0:
    #         #         print(f"Added highlight with ID: {annot_id}")
    #         #         print("beforeexe----",beforeexe)
    #         #         sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
    #         #         val = (beforeexe,self.doc_id,changes_data,0)
    #         #         mycursor.execute(sql, val)
    #         #         mydb.commit()
    #         if annot_id:
    #             self.change_history.append(("highlight", self.current_page, annot_id))
    #             print("highlight added",self.change_history)
    #             self.annotation_is_available = True
    #             self.annotation_listed.append("highlight")
    #     except Exception as e:
    #         messagebox.showerror("Error", f"Failed to add highlight: please drag the area you want to highlight", parent=self.root)
    #         return    
    #     self.render_page(self.current_page)
    #     # self.highlight_button.configure(fg_color="#00498f",hover_color="#023261")
    #     # self.canvas.unbind("<B1-Motion>")
    #     # self.canvas.unbind("<ButtonRelease-1>")
    #     # self.deactivate_tools()

# ----------------------------------------------------------------------------------------------------------------------------------------------------


    def enable_highlight_mode(self):
        """ Activate highlight mode """
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        if self.active_highlight:
            self.highlight_button.configure(fg_color="#00498f",hover_color="#023261")
            self.canvas.unbind("<B1-Motion>")
            self.canvas.unbind("<ButtonRelease-1>")
            self.canvas.unbind("<Button-1>")
            self.deactivate_tools()
            self.active_highlight = False
            return
        self.active_highlight = True   
        self.deactivate_tools()
        self.highlight_mode = True    
        self.highlight_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_colour(self.highlight_button,"active_highlight")
        self.is_drawing_hollow_rect = False
        self.is_drawing_filled_rect = False
        self.moving_highlight_mode = False
        self.selected_highlight_id = None
        self.temp_highlight_rect = None
        self.canvas.bind("<Button-1>", self.on_highlight_click)
        self.canvas.bind("<B1-Motion>", self.on_highlight_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_highlight_release)

    def on_highlight_click(self, event):
        """Handle click in highlight mode"""
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        clicked_highlight = self.find_highlight_at_position(canvas_x, canvas_y)
        
        if clicked_highlight:
            self.moving_highlight_mode = True
            self.selected_highlight_id = clicked_highlight['id']
            self.original_highlight_rect = clicked_highlight['rect']
            
            # Store the original PDF coordinates (not canvas coordinates)
            rect = clicked_highlight['rect']
            self.original_pdf_rect = {
                'x0': rect.x0,
                'y0': rect.y0, 
                'x1': rect.x1,
                'y1': rect.y1
            }
            
            # Convert to canvas coordinates for display
            canvas_coords = [
                rect.x0 * self.zoom_factor,
                rect.y0 * self.zoom_factor,
                rect.x1 * self.zoom_factor,
                rect.y1 * self.zoom_factor
            ]
            
            # Store drag start position
            self.drag_start_x = canvas_x
            self.drag_start_y = canvas_y
            
            page = self.pdf_document[self.current_page]
            try:
                for annot in page.annots():
                    if annot.type[1] == 'Highlight' and annot.info.get('id') == self.selected_highlight_id:
                        page.delete_annot(annot)
                        print(f"Deleted highlight annotation with ID: {self.selected_highlight_id}")
                        break
            except Exception as e:
                print(f"Error deleting annotation: {e}")
            
            self.temp_highlight_rect = self.canvas.create_rectangle(
                canvas_coords[0], canvas_coords[1], canvas_coords[2], canvas_coords[3],
                outline="red", width=3, fill="yellow", stipple="gray50"
            )
            print(f"Starting to move highlight {self.selected_highlight_id}")
            print(f"Original PDF rect: {self.original_pdf_rect}")
        else:
            self.moving_highlight_mode = False
            self.start_highlight_rectangle(event)

    def find_highlight_at_position(self, x, y):
        """Find highlight annotation at given canvas position"""
        pdf_x = x / self.zoom_factor
        pdf_y = y / self.zoom_factor
        page = self.pdf_document[self.current_page]
        rotation = page.rotation
        page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor
        
        if rotation == 90:
            pdf_x, pdf_y = pdf_y, page_width - pdf_x
        elif rotation == 180:
            pdf_x, pdf_y = page_width - pdf_x, page_height - pdf_y
        elif rotation == 270:
            pdf_x, pdf_y = page_height - pdf_y, pdf_x
        
        for annot in page.annots():
            if annot.type[1] == 'Highlight':
                rect = annot.rect
                if (rect.x0 <= pdf_x <= rect.x1 and rect.y0 <= pdf_y <= rect.y1):
                    return {
                        'id': annot.info.get('id'),
                        'rect': rect,
                        'annotation': annot
                    }
        return None

    def on_highlight_drag(self, event):
        """Handle dragging in highlight mode"""
        if self.moving_highlight_mode and self.temp_highlight_rect and hasattr(self, 'original_pdf_rect'):
            current_x = self.canvas.canvasx(event.x)
            current_y = self.canvas.canvasy(event.y)
            
            # Calculate displacement from drag start
            dx = current_x - self.drag_start_x
            dy = current_y - self.drag_start_y
            
            # Apply displacement to original PDF coordinates and convert to canvas
            new_canvas_x1 = (self.original_pdf_rect['x0'] * self.zoom_factor) + dx
            new_canvas_y1 = (self.original_pdf_rect['y0'] * self.zoom_factor) + dy
            new_canvas_x2 = (self.original_pdf_rect['x1'] * self.zoom_factor) + dx
            new_canvas_y2 = (self.original_pdf_rect['y1'] * self.zoom_factor) + dy
            
            self.current_canvas_coords = [new_canvas_x1, new_canvas_y1, new_canvas_x2, new_canvas_y2]
            
            try:
                self.canvas.coords(self.temp_highlight_rect, new_canvas_x1, new_canvas_y1, new_canvas_x2, new_canvas_y2)
                print(f"Updated temp rect to: {self.current_canvas_coords}")
            except Exception as e:
                print(f"Error updating temp rect coords: {e}")
        else:
            self.draw_highlight_rectangle(event)

    def on_highlight_release(self, event):
        """Handle release in highlight mode"""
        if self.moving_highlight_mode and self.temp_highlight_rect:
            self.finalize_highlight_move(event)
        else:
            self.finalize_highlight(event)

    def finalize_highlight_move(self, event):
        """Finalize moving a highlight"""
        if not self.temp_highlight_rect or not hasattr(self, 'current_canvas_coords'):
            print("No temp highlight rect or coordinates to finalize")
            self.reset_highlight_move_state()
            return
        
        try:
            coords = self.current_canvas_coords
            print(f"Using stored coords: {coords}")
            if not coords or len(coords) != 4:
                print("Invalid stored coordinates")
                self.reset_highlight_move_state()
                return
        except Exception as e:
            print(f"Error getting coords: {e}")
            self.reset_highlight_move_state()
            return
        
        # Convert canvas coordinates back to PDF coordinates
        start_x = coords[0] / self.zoom_factor
        start_y = coords[1] / self.zoom_factor
        end_x = coords[2] / self.zoom_factor
        end_y = coords[3] / self.zoom_factor
        
        print(f"PDF coords: ({start_x}, {start_y}) to ({end_x}, {end_y})")
        
        rect = fitz.Rect(start_x, start_y, end_x, end_y)
        page = self.pdf_document[self.current_page]
        rotation = page.rotation
        page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor
        
        print(f"Before rotation transform: {rect}")
        
        # Apply rotation transformation
        if rotation == 90:
            rect = fitz.Rect(rect.y0, page_width - rect.x1, rect.y1, page_width - rect.x0)
        elif rotation == 180:
            rect = fitz.Rect(page_width - rect.x1, page_height - rect.y1, 
                            page_width - rect.x0, page_height - rect.y0)
        elif rotation == 270:
            rect = fitz.Rect(page_height - rect.y1, rect.x0, page_height - rect.y0, rect.x1)
        
        print(f"After rotation transform: {rect}")
        
        try:
            highlight = page.add_highlight_annot(rect)
            highlight.set_colors(stroke=[1, 1, 0])  # Yellow color
            highlight.set_opacity(0.5)  # Semi-transparent
            highlight.update()
            
            new_annot_id = highlight.info.get('id')
            if new_annot_id:
                self.change_history.append(("highlight_move", self.current_page, 
                                        self.selected_highlight_id, new_annot_id))
                print(f"Highlight moved from {self.selected_highlight_id} to {new_annot_id}")
            else:
                print("Warning: New annotation created but no ID found")
        except Exception as e:
            print(f"Error creating new highlight: {e}")
            # Restore original highlight if creation fails
            try:
                if self.original_highlight_rect:
                    restore_highlight = page.add_highlight_annot(self.original_highlight_rect)
                    restore_highlight.set_colors(stroke=[1, 1, 0])
                    restore_highlight.set_opacity(0.5)
                    restore_highlight.update()
                    print("Original highlight restored")
            except Exception as restore_error:
                print(f"Error restoring highlight: {restore_error}")
        
        self.reset_highlight_move_state()
        self.render_page(self.current_page)

    def reset_highlight_move_state(self):
        """Reset all highlight moving state variables"""
        if hasattr(self, 'temp_highlight_rect') and self.temp_highlight_rect:
            try:
                self.canvas.delete(self.temp_highlight_rect)
                print(f"Deleted temp rect: {self.temp_highlight_rect}")
            except Exception as e:
                print(f"Error deleting temp rect: {e}")
        
        self.temp_highlight_rect = None
        self.moving_highlight_mode = False
        self.selected_highlight_id = None
        
        # Clean up all state variables
        for attr in ['original_highlight_rect', 'drag_start_x', 'drag_start_y', 
                    'original_pdf_rect', 'current_canvas_coords']:
            if hasattr(self, attr):
                setattr(self, attr, None)

    def start_highlight_rectangle(self, event):
        """Start a rectangle selection for highlighting"""
        if self.moving_highlight_mode:
            return
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        if hasattr(self, 'rectangle_id') and self.rectangle_id:
            self.canvas.delete(self.rectangle_id)
        self.rectangle_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
            outline="yellow", width=2)

    def draw_highlight_rectangle(self, event):
        """Draw the rectangle dynamically as the mouse is dragged."""
        if (not hasattr(self, 'rectangle_id') or self.rectangle_id is None or 
            self.moving_highlight_mode):
            return
        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
        self.canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)

    def finalize_highlight(self, event):
        """Finalize the highlight and save it to the PDF."""
        if (not hasattr(self, 'start_x') or self.start_x is None or 
            self.start_y is None or self.moving_highlight_mode):
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
            rect = fitz.Rect(rect.y0, page_width - rect.x1, rect.y1, page_width - rect.x0)
        elif rotation == 180:
            rect = fitz.Rect(page_width - rect.x1, page_height - rect.y1, 
                            page_width - rect.x0, page_height - rect.y0)
        elif rotation == 270:
            rect = fitz.Rect(page_height - rect.y1, rect.x0, page_height - rect.y0, rect.x1)       
        try:
            highlight = page.add_highlight_annot(rect)
            highlight.update()
            annot_id = highlight.info.get('id')           
            if annot_id:
                self.change_history.append(("highlight", self.current_page, annot_id))
                print("Highlight added", self.change_history)
                self.annotation_is_available = True
                if not hasattr(self, 'annotation_listed'):
                    self.annotation_listed = []
                self.annotation_listed.append("highlight")            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to add highlight: please drag the area you want to highlight", parent=self.root)
            return     
        if hasattr(self, 'rectangle_id') and self.rectangle_id:
            self.canvas.delete(self.rectangle_id)
            self.rectangle_id = None    
        self.render_page(self.current_page)



    def on_mouse_hover(self, event):
        """Change cursor when hovering over a polygon or sticky note."""
        if not self.pdf_document or self.current_page is None:
            return
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        tooltip_shown = False
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation

        # Adjust the coordinates for zoom
        adjusted_x, adjusted_y = x / self.zoom_factor, y / self.zoom_factor

          # for drawing in self.page_drawings.get(self.current_page, []):
        for drawing in getattr(self, 'current_page_drawings', []):
            if isinstance(drawing, tuple) and len(drawing) == 3:  # Polygon (id, points, color)
                _, points, _ = drawing

                # Adjust the polygon coordinates for zoom
                zoomed_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in zip(points[::2], points[1::2])]

                if self.is_point_inside_polygon(x, y, sum(zoomed_points, ())):  # Flatten the list
                    self.canvas.config(cursor="hand2")
                    return  # Exit function early if hovering over a polygon

        # Sticky note cursor handling
        for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                page_width = page.rect.width * self.zoom_factor
                page_height = page.rect.height * self.zoom_factor

                # Handle rotation
                if rotation_angle == 90:
                    rotated_x, rotated_y = self.page_height + (180 * self.zoom_factor) - y_position, x_position
                elif rotation_angle == 180:
                    rotated_x = page_width - x_position
                    rotated_y = page_height - y_position
                elif rotation_angle == 270:
                    rotated_x, rotated_y = y_position, self.page_width - (180 * self.zoom_factor) - x_position
                else:  # 0 degrees
                    rotated_x = x_position
                    rotated_y = y_position

                if abs(x - rotated_x) < 20 and abs(y - rotated_y) < 20:  # Adjust hover sensitivity
                    if not tooltip_shown:
                        self.show_tooltip(event.x_root, event.y_root, text)
                        tooltip_shown = True
                    break

        if not tooltip_shown:
            if self.active_tooltip:
                self.active_tooltip.destroy()
                self.active_tooltip = None
            self.canvas.config(cursor="arrow")  # Ensure cursor resets correctly


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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        if self.sticky_note_mode:
            self.sticky_note_mode = False
            self.canvas.unbind("<Button-1>")
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
            messagebox.showerror("Error", "No PDF document to save.", parent=self.root)
            return

        print("self.annotation_listed",self.annotation_listed)
        print("edit_file_name-----------------",self.edit_file_name)  
        print("Serverurl--------------------------------------------------------------------------------------------------",self.server_url)
        try:
            temp_pdf = fitz.open()
            for page_num in range(len(self.pdf_document)):
                page = self.pdf_document[page_num]
                temp_pdf.insert_pdf(self.pdf_document, from_page=page_num, to_page=page_num)

            for page_num in self.page_drawings:
                if page_num < len(temp_pdf):
                    page = temp_pdf[page_num]
                    # Manually embed polygons without changing current_page
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
                # for rect in self.rectangles:
                #     print("rectangles",rect['color'])
                #     print("rectangles",rect)
                #     if rect['type'] == 'rectangle' and rect['page'] < len(temp_pdf):
                #         page = temp_pdf[rect['page']]
                        
                #         # Create a rectangle using the page's draw methods instead of annotations
                #         rect_coords = fitz.Rect(rect['x1'], rect['y1'], rect['x2'], rect['y2'])
                        
                #         # Set color based on string color (convert to RGB tuple)
                #         if rect['color'] == "red":
                #             rgb_color = (1, 0, 0)  # Red in RGB (0-1 range)
                #         else:
                #             rgb_color = (0, 0, 0)  # Default to black
                        
                #         # Draw rectangle on the page
                #         if rect['filled']:
                #             # For filled rectangle
                #             page.draw_rect(rect_coords, color=rgb_color, fill=rgb_color, width=4)
                #         else:
                #             # For hollow rectangle
                #             page.draw_rect(rect_coords, color=rgb_color, fill=None, width=6)

                for rect in self.rectangles:
                    if rect['type'] != 'rectangle' or rect['page'] >= len(temp_pdf):
                        continue
                    if rect['color'] != 'red':
                        print(f"Skipping non-red rectangle: {rect['color']}")  # Optional debug
                        continue
                    # Only proceed if the rectangle is red and within valid page range
                    page = temp_pdf[rect['page']]
                    rect_coords = fitz.Rect(rect['x1'], rect['y1'], rect['x2'], rect['y2'])
                    rgb_color = (1, 0, 0)  # Red in RGB (0-1 range)

                    if rect['filled']:
                        # Draw filled red rectangle
                        page.draw_rect(rect_coords, color=rgb_color, fill=rgb_color, width=4)
                    else:
                        # Draw hollow red rectangle
                        page.draw_rect(rect_coords, color=rgb_color, fill=None, width=6)

                # Add line annotations
                for line in self.lines:
                    if line['type'] == 'line' and line['page'] < len(temp_pdf):
                        page = temp_pdf[line['page']]
                        # Create a line using PyMuPDF
                        start_point = fitz.Point(line['x1'], line['y1'])
                        end_point = fitz.Point(line['x2'], line['y2'])
                        rgb_color = (1, 0, 0)  # Red in RGB (0-1 range)
                        page.draw_line(start_point, end_point, color=rgb_color, width=6)
                        
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
                        annot.set_border(width=6)
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
            if len(self.redact_api_rectangles) > 0:
                print("redact_api_rectangles",self.redact_api_rectangles)
                try:
                    for rect_data in self.redact_api_rectangles:
                        if rect_data['source'] == "local":
                            page_size = self.add_pagesize[rect_data['id']]
                            redact_url = "https://idms-dev.blockchaincloudapps.com/api/v1/insert-pdf-viewer-redact-info"
                            payload = json.dumps({
                                    "file_name": self.filename_pdf,
                                    "temp_id": str(self.temp_id),
                                    "doc_id": str(self.doc_id),
                                    "coordinate": str(rect_data),
                                    "page_size": str(page_size),
                                    "zoom_size": self.zoom_factor,
                                    "stored_from": "Viewer"
                                    })
                            headers = {'Content-Type': 'application/json'}
                            response = requests.request("POST", redact_url, headers=headers, data=payload)
                            print("redect_api status",response.text, response.status_code)
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
                        messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                        print("File saved successfully  _redact.pdf")
                    else:
                        messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
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
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
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
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
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
                        messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                        print("File saved successfully  _redact.pdf")
                    else:
                        messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
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
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
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
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                            print("File saved successfully  _redact.pdf")
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
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
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
                            return
                    elif "with_annotations" in self.edit_file_name:
                        print("_____-----------------------________________with_annotations.pdf")
                        edit_file_name = self.edit_file_name
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
                            return
                    elif "redact" in self.filename_pdf:
                        print("___________------------------------_________redact.pdf")
                        edit_file_name = self.edit_file_name.replace("redact", "redact_with_annotations")
                        print("redact_file_name--*****-",edit_file_name)
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
                            return
                    else:
                        print("elseee---------------------------------------------------------------")
                        edit_file_name = self.edit_file_name.replace(".pdf", "_with_annotations.pdf")
                        files = {'id': (None, self.doc_id),
                                'file': (edit_file_name, pdf_buffer, 'application/pdf')}
                        response = requests.post(self.server_url, files=files)
                        if response.status_code in [200, 201]:
                            messagebox.showinfo("Success", "File saved successfully", parent=self.root)
                        else:
                            messagebox.showerror("Error", "Failed to save the file.", parent=self.root)
                            return
                           
                else:
                    messagebox.showinfo("Info", "No Annotation made to save the file.", parent=self.root)
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

    def _embed_polygons_to_page(self, page, page_num):
        """Helper function to embed polygons to a specific page without changing self.current_page."""
        try:
            if page_num not in self.page_drawings:
                return
                
            # Delete existing polygon annotations if any
            for annot in page.annots():
                if annot.info.get("title") == "polygon_annotation":
                    annot.delete()
                    
            for drawing in self.page_drawings[page_num]:
                if len(drawing) != 3:
                    continue
                    
                mode, points, polygon_id = drawing
                
                # Skip if this polygon should be ignored
                if hasattr(self, 'embedded_polygons') and page_num in self.embedded_polygons:
                    if any(p[2] == polygon_id for p in self.embedded_polygons[page_num]):
                        continue
                        
                # Convert points to pairs of coordinates
                scaled_points = [(points[i], points[i + 1]) for i in range(0, len(points), 2)]
                
                path = page.new_shape()
                # Draw lines between points to form the polygon
                for i in range(len(scaled_points)):
                    p1 = scaled_points[i]
                    p2 = scaled_points[(i + 1) % len(scaled_points)]
                    path.draw_line(p1, p2)
                    
                # Set fill or outline based on mode
                if mode == "filled":
                    path.finish(fill=(0, 0, 1), color=(0, 0, 0))
                elif mode == "hollow":
                    path.finish(color=(1, 0, 0), fill=None, width=6)
                    
                # Commit the shape to the page
                path.commit(overlay=True)
                
                # Track that we've embedded this polygon
                if not hasattr(self, 'embedded_polygons'):
                    self.embedded_polygons = {}
                if page_num not in self.embedded_polygons:
                    self.embedded_polygons[page_num] = []
                self.embedded_polygons[page_num].append(drawing)
                
        except Exception as e:
            print(f"Error embedding polygons to page {page_num}: {e}")

    def add_text_sticky_annotation(self, page, x_scaled, y_scaled, text):
        """Helper function to add text annotations properly."""
        today = date.today().strftime("%m-%d-%Y")
        base_text_size = 20  
        scaling_factor = max(page.rect.width, page.rect.height) / 1000  
        text_size = int(base_text_size * scaling_factor)
        marker_size = int(12 * scaling_factor)
        text_offset = int(15 * scaling_factor)
        padding = int(10 * scaling_factor)
        vertical_padding = int(15 * scaling_factor)
        
        marker_color = (1, 0, 0)
        page.draw_circle(center=(x_scaled, y_scaled), radius=marker_size / 2, color=marker_color, fill=marker_color)
        
        lines = self.wrap_text(f"{today}\n{text}", 50)
        max_text_width = max(len(line) for line in lines) * text_size * 0.6
        max_text_height = len(lines) * text_size * 1.5
        background_width = max_text_width + padding * 2
        background_height = max_text_height + vertical_padding * 2.5
        
        page.draw_rect(
            rect=(x_scaled, y_scaled + text_offset - vertical_padding, 
                  x_scaled + background_width, y_scaled + text_offset + background_height),
            color=(1, 1, 0), overlay=True, fill_opacity=0.9, fill=(1, 1, 0)
        )
        
        text_x = x_scaled + padding
        text_y = y_scaled + text_offset
        for i, line in enumerate(lines):
            page.insert_text(point=(text_x, text_y + (i * text_size * 1.5)), text=line, fontsize=text_size, color=(0, 0, 0))

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
        """Add plain text annotation to the PDF page."""
        try:
            text_size = 20  # Default text size
            scaling_factor = max(page.rect.width, page.rect.height) / 1000
            adjusted_text_size = int(text_size * scaling_factor)
            
            # Ensure text stays within page boundaries
            max_width = page.rect.width - x_scaled - 20  # 20-unit buffer from edge
            
            # Convert text to properly wrapped text if needed
            wrapped_text = self.wrap_text_for_saving(text, max_width, adjusted_text_size)
            
            # Add the text to the PDF
            page.insert_text(
                point=(x_scaled, y_scaled),
                text=wrapped_text,
                fontsize=adjusted_text_size,
                color=(0, 0, 0)  # Black color
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

    def add_text_with_bg_annotation(self, page, x_scaled, y_scaled, text):
        """Add text with background annotation to the PDF page."""
        text_size = 18 # Default text size
        scaling_factor = max(page.rect.width, page.rect.height) / 1000
        adjusted_text_size = int(text_size * scaling_factor)
        padding = int(15 * scaling_factor)
        
        # Calculate text dimensions for background
        lines = text.split('\n')
        max_width = max(len(line) for line in lines) * adjusted_text_size * 0.6
        text_height = len(lines) * adjusted_text_size * 1.2
        
        # Draw background rectangle
        page.draw_rect(
            rect=(x_scaled - padding, y_scaled - padding, 
                x_scaled + max_width + padding, y_scaled + text_height + padding),
            color=(0, 1, 1),  # Cyan color
            fill=(0, 1, 1),
            fill_opacity=0.9
        )   
        # Insert text on top of background
        for i, line in enumerate(lines):
            page.insert_text(
                point=(x_scaled, y_scaled + (i * adjusted_text_size * 1.2)),
                text=line,
                fontsize=adjusted_text_size,
                color=(0, 0, 0)  # Black color
            )
            
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        if self.current_page > 0:
            print(f"Page Width: {self.page_width}, Page Height: {self.page_height}")
            self.current_page -= 1
            self.render_page(self.current_page)
            self.update_thumbnail_selection(self.current_page)
            self.update_page_display()

    def next_page(self, event=None):
        """Go to the next page in the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        if self.current_page < len(self.pdf_document) - 1:
            print(f"Page Width: {self.page_width}, Page Height: {self.page_height}")
            self.current_page += 1
            self.render_page(self.current_page)
            self.update_thumbnail_selection(self.current_page)
            self.update_page_display()

    def rotate_90clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
        page.set_rotation((page.rotation + 90) % 360)
        self.render_page(self.current_page)

    def rotate_180clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
        page.set_rotation((page.rotation + 180) % 360)
        self.render_page(self.current_page)

    def rotate_270clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
        page.set_rotation((page.rotation + 270) % 360)
        self.render_page(self.current_page)

    def toggle_invert_colors(self):
        """Toggle color inversion for the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        if self.is_inverted:
            self.invert_button.configure(fg_color="#00498f",hover_color="#023261")
        else:
            self.invert_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        self.redraw_blackrectangles(rotation_angle)
        self.is_inverted = not self.is_inverted
        self.render_page(self.current_page)
        self.redraw_sticky_notes()


    def zoom_in_area(self, event):
        """Zoom into a specific area of the canvas based on mouse click."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
    #     self.deactivate_colour(self.draw_button)
    #     self.is_drawing = not self.is_drawing  # Toggle drawing mode
    #     if self.is_drawing:
    #         self.canvas.bind("<Button-1>", self.start_freehand_drawing)
    #         self.canvas.bind("<B1-Motion>", self.draw_freehand_line)
    #         self.canvas.bind("<ButtonRelease-1>", self.finish_freehand_drawing)
    #     else:
    #         self.canvas.unbind("<Button-1>")
    #         self.canvas.unbind("<B1-Motion>")
    #         self.canvas.unbind("<ButtonRelease-1>")

    def toggle_drawing(self):
        """Toggle the freehand drawing mode without embedding strokes into the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return

        if self.active_freehandline:
            self.canvas.unbind("<Button-1>")
            self.canvas.unbind("<B1-Motion>")
            self.canvas.unbind("<ButtonRelease-1>")
            self.active_freehandline = False
            self.draw_button.configure(fg_color="#00498f", hover_color="#023261")
            return

        self.active_freehandline = True
        self.draw_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_colour(self.draw_button,"active_freehandline")

        self.canvas.bind("<Button-1>", self.start_freehand_drawing)
        self.canvas.bind("<B1-Motion>", self.draw_freehand_line)
        self.canvas.bind("<ButtonRelease-1>", self.finish_freehand_drawing)


    def start_freehand_drawing(self, event):
        """Start recording a freehand drawing stroke with unscaled coordinates."""
        self.freehand_stroke = [(event.x / self.zoom_factor, event.y / self.zoom_factor)]
        self.current_line = self.canvas.create_line(
            self.freehand_stroke[0][0] * self.zoom_factor,
            self.freehand_stroke[0][1] * self.zoom_factor,
            self.freehand_stroke[0][0] * self.zoom_factor,
            self.freehand_stroke[0][1] * self.zoom_factor, 
            fill="black" if not self.is_inverted else "white", width=2
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
        # del self.freehand_stroke
        # del self.current_line
        # self.toggle_drawing()
        self.render_page(self.current_page)  # Re-render to ensure it's drawn correctly
        self.redraw_freehand_drawings()
        self.annotation_listed.append("freehand")
        # self.draw_button.configure(fg_color="#00498f",hover_color="#023261")

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
                fill_color = "black" if not self.is_inverted else "white"
                new_line_id = self.canvas.create_line(
                    *sum(scaled_points, ()),
                    fill=fill_color, width=3, tags="freehand"
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
                x, y = page_height+(180) - y, x
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
                outline="blue" if self.polygon_mode == "filled" else "red",
                tags=("polygon",)
            )

            self.page_drawings[self.current_page].append((self.polygon_mode, points, polygon_id))
            self.polygon_cord.append((self.current_page, polygon_id, points))
            self.change_history.append(("polygon", self.current_page, None, polygon_id))
            self.annotation_listed.append("polygon")
        else:
            self.start_point = None

        self.redraw_polygons()

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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        self.deactivate_tools()
        self.deactivate_colour(self.image_button)
        self.image_button.configure(fg_color="#d17a24", hover_color="#b56e26") 
        image_path = filedialog.askopenfilename(
            title="Select an Image",
            filetypes=[("Image Files", "*.png;*.jpg;*.jpeg"), ("All Files", "*.*")], parent=self.root)
            
        if not image_path:
            self.image_button.configure(fg_color="#00498f", hover_color="#023261")
            return  # User canceled the dialog       
        try:
            img = Image.open(image_path)
            img.thumbnail((200, 200), Image.LANCZOS)  # Initial size
            self.tk_image = ImageTk.PhotoImage(img)  # Convert to Tkinter-compatible format
            
            # Create the image on canvas
            self.active_image = self.canvas.create_image(
                100, 100, 
                image=self.tk_image, 
                anchor="nw", 
                tags="temp_image_overlay"
            )
            
            # Store the image data for manipulation
            self.image_data = {
                "id": f"img_{len(self.image_overlays)}",
                "image_path": image_path,
                "image_obj": img,
                "x": 100, "y": 100,
                "width": img.width, "height": img.height,
                "base_x": 100 / self.zoom_factor,  # Store unscaled coordinates
                "base_y": 100 / self.zoom_factor,
                "base_width": img.width / self.zoom_factor,
                "base_height": img.height / self.zoom_factor,
                "page": self.current_page
            }
            
            # Bind events for manipulation
            self.canvas.tag_bind(self.active_image, "<ButtonPress-1>", self.start_move)
            self.canvas.tag_bind(self.active_image, "<B1-Motion>", self.do_move)
            self.canvas.tag_bind(self.active_image, "<ButtonRelease-1>", self.finalize_move)
            self.canvas.bind_all("<MouseWheel>", self.resize_image)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load image: {str(e)}", parent=self.root)

    def start_move(self, event):
        """Start dragging the image."""
        self.image_data["start_x"] = event.x
        self.image_data["start_y"] = event.y

    def do_move(self, event):
        """Move the image as the mouse drags."""
        dx = event.x - self.image_data["start_x"]
        dy = event.y - self.image_data["start_y"]
        
        self.canvas.move(self.active_image, dx, dy)
        self.image_data["x"] += dx
        self.image_data["y"] += dy
        
        # Update base coordinates (unscaled)
        self.image_data["base_x"] = self.image_data["x"] / self.zoom_factor
        self.image_data["base_y"] = self.image_data["y"] / self.zoom_factor
        
        self.image_data["start_x"] = event.x
        self.image_data["start_y"] = event.y

    def finalize_move(self, event):
        """Finalize the image overlay position."""
        user_response = messagebox.askyesnocancel(
            "Confirm Position",
            "Are you satisfied with the current position and size of the image? To Resize hold shift and scroll", parent=self.root)
            
        if user_response is None:  # User clicked 'Cancel'
            self.canvas.delete(self.active_image)  # Remove the temporary image from canvas
            self.active_image = None
            self.image_data = None
            return
            
        if not user_response:  # User clicked 'No', allow them to move/reshape again
            return  # Do nothing, letting them continue adjusting the image
        
        self.annotation_is_available = True
        
        try:
            # Create the final overlay information
            overlay_info = {
                "id": self.image_data["id"],
                "type": "image_overlay",
                "image_path": self.image_data["image_path"],
                "x": self.image_data["x"],
                "y": self.image_data["y"],
                "width": self.image_data["width"],
                "height": self.image_data["height"],
                "base_x": self.image_data["base_x"],
                "base_y": self.image_data["base_y"],
                "base_width": self.image_data["base_width"],
                "base_height": self.image_data["base_height"],
                "page": self.current_page,
                "canvas_id": self.active_image
            }
            
            # Add to image overlays list and change history
            self.image_overlays.append(overlay_info)
            self.change_history.append(("image_overlay", self.current_page, overlay_info))
            
            # Remove the temporary image and redraw it as a permanent one
            self.canvas.delete("temp_image_overlay")
            self.redraw_image_overlays(self.current_page)
            
            # Unbind events - this prevents the image from being moved after finalization
            self.canvas.unbind_all("<MouseWheel>")
            self.active_image = None
            self.annotation_listed.append("image_overlay")
            self.image_button.configure(fg_color="#00498f", hover_color="#023261")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to add image overlay: {e}", parent=self.root)

    def resize_image(self, event):
        """Resize the image using the mouse scroll."""
        if event.state & 0x0001 == 0:
            return  # Shift not pressed; ignore scroll
            
        scale_factor = 1.1 if event.delta > 0 else 0.9
        
        # Calculate new width and height
        new_width = int(self.image_data["width"] * scale_factor)
        new_height = int(self.image_data["height"] * scale_factor)
        
        # Prevent the image from becoming too small
        if new_width < 50 or new_height < 50:
            return
            
        # Update image data
        self.image_data["width"] = new_width
        self.image_data["height"] = new_height
        self.image_data["base_width"] = new_width / self.zoom_factor
        self.image_data["base_height"] = new_height / self.zoom_factor
        
        # Resize the image
        img_resized = self.image_data["image_obj"].resize((new_width, new_height), Image.LANCZOS)
        self.tk_image = ImageTk.PhotoImage(img_resized)
        self.canvas.itemconfig(self.active_image, image=self.tk_image)

    def add_text_to_pdf(self):
        """Enable text-adding mode on the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        self.text_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools()
        self.deactivate_colour(self.text_button)
        self.canvas.bind("<Button-1>", self.on_add_text_click)
        self.add_text_mode = True


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
            return

        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        page = self.pdf_document[self.current_page]
        page_width_scaled = page.rect.width
        max_text_width = min(page_width_scaled - x_scaled - 20, page_width_scaled * 0.4)

        annotation_data = {
            "text": text,
            "font_size": 16,
            "max_width": max_text_width
        }

        self.text_annotations[(self.current_page, x_scaled, y_scaled)] = annotation_data
        self.change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))
        self.render_page(self.current_page)

        self.add_text_mode = False
        self.canvas.unbind("<Button-1>")
        self.annotation_is_available = True
        self.annotation_listed.append("text")
        self.text_button.configure(fg_color="#00498f", hover_color="#023261")


    def redraw_text_annotations(self):
        """Redraw text annotations with strict boundary enforcement."""
        self.canvas.delete("plain_text_annotation")
        if not self.pdf_document:
            return

        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        fill_color = "black" if not self.is_inverted else "white"

        for (page_num, x_scaled, y_scaled), annotation_data in list(self.text_annotations.items()):
            if page_num != self.current_page:
                continue
            base_font_size = 16
            font_size_zoom = base_font_size * self.zoom_factor
            if isinstance(annotation_data, str):
                annotation_data = {
                    "text": annotation_data,
                    "max_width": page.rect.width * 0.4,
                    "font_size": font_size_zoom
                }

            text = annotation_data["text"]
            max_width = annotation_data["max_width"] * self.zoom_factor
            font_size = annotation_data["font_size"]
            x_position = x_scaled * self.zoom_factor
            y_position = y_scaled * self.zoom_factor
            
            if rotation_angle == 90:  # Rotate text **clockwise**
                if is_small_page == "yes":
                    rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
                elif is_small_page == "slightly":
                    rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
                elif is_small_page == "longer":
                    rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
                elif is_small_page == "maybe":
                    rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
                elif is_small_page == "nope large":
                    rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
                elif is_small_page == "nope very large":
                    rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
                else:
                    rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position

                angle = -90
            elif rotation_angle == 180:
                rotated_x = page.rect.width * self.zoom_factor - x_position
                rotated_y = page.rect.height * self.zoom_factor - y_position
                angle = 180
            elif rotation_angle == 270:  # Rotate text **counterclockwise**
                if is_small_page == "yes":
                    rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
                elif is_small_page == "slightly":
                    rotated_x, rotated_y = y_position, self.page_width-(1050*self.zoom_factor) - x_position
                elif is_small_page == "longer":
                    rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position 
                elif is_small_page == "maybe":
                    rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position 
                elif is_small_page == "nope large":
                    rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
                elif is_small_page == "nope very large":
                    rotated_x, rotated_y = y_position, self.page_width-(4300*self.zoom_factor) - x_position
                else:
                    rotated_x, rotated_y = y_position, self.page_width-(2000*self.zoom_factor) - x_position
                angle = -270
            else:
                rotated_x = x_position
                rotated_y = y_position
                angle = 0

            text_container = self.canvas.create_text(
                rotated_x, rotated_y,
                text=text,
                font=("Arial", font_size),
                fill=fill_color,
                width=max_width,
                tags="plain_text_annotation",
                anchor="nw"
            )
            self.canvas.itemconfig(text_container, angle=angle)
            self.canvas.tag_bind(text_container, "<Button-1>", self.on_text_press)
            self.canvas.tag_bind(text_container, "<B1-Motion>", self.on_text_drag)
            self.canvas.tag_bind(text_container, "<ButtonRelease-1>", self.on_text_release)

            bbox = self.canvas.bbox(text_container)
            annotation_data["canvas_id"] = text_container
            annotation_data["bbox"] = bbox

        self.annotation_is_available = True


    # === Dragging Behavior ===

    def on_text_press(self, event):
        """Store the selected text ID and offset when clicked."""
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
        """Update annotation data after dragging."""
        if not self.dragged_text_id:
            return

        for key in list(self.text_annotations.keys()):
            data = self.text_annotations[key]
            if data.get("canvas_id") == self.dragged_text_id:
                bbox = self.canvas.bbox(self.dragged_text_id)
                top_left_x, top_left_y = bbox[0], bbox[1]
                new_x_scaled = top_left_x / self.zoom_factor
                new_y_scaled = top_left_y / self.zoom_factor

                new_key = (key[0], new_x_scaled, new_y_scaled)
                self.text_annotations[new_key] = self.text_annotations.pop(key)
                self.text_annotations[new_key]["canvas_id"] = self.dragged_text_id

                # ✅ Now update the change_history with the new coordinates
                for i, entry in enumerate(self.change_history):
                    if entry[0] == "add_text" and entry[1] == key[0] and abs(entry[2] - key[1]) < 1e-3 and abs(entry[3] - key[2]) < 1e-3:
                        self.change_history[i] = ("add_text", key[0], new_x_scaled, new_y_scaled, entry[4])
                        break

                break  # ✅ Only after everything is updated, break the loop

        self.dragged_text_id = None

    def add_text_with_background(self):
        """Enable text-adding mode for text with a background."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        self.text_bg_button.configure(fg_color="#d17a24", hover_color="#b56e26")
        self.deactivate_tools()
        self.deactivate_colour(self.text_bg_button)
        self.canvas.bind("<Button-1>", self.on_add_text_with_bg_click)
        self.add_text_bg_mode = True

    def on_add_text_with_bg_click(self, event):
        if not self.pdf_document or not self.add_text_bg_mode:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return
        text = self.ask_for_note_text(x, y, "Add Text with Background")
        if not text:
            return
        wrapped_lines = []
        for line in text.splitlines():
            wrapped_lines.extend(textwrap.wrap(line, width=30) or [""])  # Ensure empty lines preserved
        wrapped_text = "\n".join(wrapped_lines)
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        self.text_annotations_bg[(self.current_page, x_scaled, y_scaled)] = {
            "text": wrapped_text}
        self.change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, wrapped_text))
        self.render_page(self.current_page)
        self.add_text_bg_mode = False
        self.canvas.unbind("<Button-1>")
        self.annotation_is_available = True
        self.annotation_listed.append("text_bg")
        self.text_bg_button.configure(fg_color="#00498f", hover_color="#023261")

    # Text with background drag functionality
    def on_text_bg_press(self, event):
        """Handle mouse press on text with background."""
        clicked_item = self.canvas.find_closest(event.x, event.y)[0]
        item_tags = self.canvas.gettags(clicked_item)
        
        if "text_annotation" in item_tags or "text_annotation_bg" in item_tags:
            # Find the text annotation that was clicked
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
        """Update annotation data after dragging."""
        if not self.dragged_text_bg_id:
            return

        new_key = None  # Declare early for safe access
        for key in list(self.text_annotations_bg.keys()):
            data = self.text_annotations_bg[key]
            if data.get("canvas_id") == self.dragged_text_bg_id:
                bbox = self.canvas.bbox(self.dragged_text_bg_id)
                top_left_x, top_left_y = bbox[0], bbox[1]
                new_x_scaled = round(top_left_x / self.zoom_factor, 4)
                new_y_scaled = round(top_left_y / self.zoom_factor, 4)
                new_key = (key[0], new_x_scaled, new_y_scaled)

                # Move annotation to new key
                self.text_annotations_bg[new_key] = self.text_annotations_bg.pop(key)
                self.text_annotations_bg[new_key]["canvas_id"] = self.dragged_text_bg_id

                # Update bbox immediately
                self.text_annotations_bg[new_key]["bbox"] = bbox

                # Update history
                for i, entry in enumerate(self.change_history):
                    if entry[0] == "add_text_bg" and entry[1] == key[0] and abs(entry[2] - key[1]) < 1e-3 and abs(entry[3] - key[2]) < 1e-3:
                        self.change_history[i] = ("add_text_bg", key[0], new_x_scaled, new_y_scaled, entry[4])
                        break
                break

        # Reset dragging variables
        self.dragged_text_bg_key = None
        self.dragged_text_bg_id = None
        self.text_bg_drag_start = None



    def redraw_text_with_background(self):
        self.canvas.delete("text_annotation_bg")
        self.canvas.delete("text_annotation")  # Also delete text items
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        rotation_angle = page.rotation
        fill_color = "black" if not self.is_inverted else "white"
        
        for (page_num, x_scaled, y_scaled), annotation_data in self.text_annotations_bg.items():
            if page_num != self.current_page:
                continue
            text = annotation_data["text"]
            x_position = x_scaled * self.zoom_factor
            y_position = y_scaled * self.zoom_factor
            page_width = page.rect.width * self.zoom_factor
            page_height = page.rect.height * self.zoom_factor
            fontsize = 16
            text_lines = text.split("\n")
            max_line_length = max(len(line) for line in text_lines) if text_lines else 0
            actual_text_width = max_line_length * fontsize * 0.6
            text_height = fontsize * 1.2 * len(text_lines)
            side_padding = 5
            bottom_padding = 8
            container_width = actual_text_width + (side_padding * 2)
            
            if rotation_angle == 90:
                if is_small_page == "yes":
                    rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
                elif is_small_page == "slightly":
                    rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
                elif is_small_page == "longer":
                    rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
                elif is_small_page == "maybe":
                    rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
                elif is_small_page == "nope large":
                    rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
                elif is_small_page == "nope very large":
                    rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
                else:
                    rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position
                rect_x1 = rotated_x - text_height - side_padding
                rect_y1 = rotated_y - side_padding
                rect_x2 = rotated_x + side_padding
                rect_y2 = rotated_y + container_width + bottom_padding
                angle = -90
            elif rotation_angle == 180:
                rotated_x = page_width - x_position
                rotated_y = page_height - y_position
                rect_x1 = rotated_x - container_width - side_padding
                rect_y1 = rotated_y - text_height - side_padding
                rect_x2 = rotated_x + side_padding
                rect_y2 = rotated_y + bottom_padding
                angle = 180
            elif rotation_angle == 270:
                if is_small_page == "yes":
                    rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
                elif is_small_page == "slightly":
                    rotated_x, rotated_y = y_position, self.page_width-(1050*self.zoom_factor) - x_position
                elif is_small_page == "longer":
                    rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position
                elif is_small_page == "maybe":
                    rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
                elif is_small_page == "nope large":
                    rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
                elif is_small_page == "nope very large":
                    rotated_x, rotated_y = y_position, self.page_width-(4300*self.zoom_factor) - x_position
                else:
                    rotated_x, rotated_y = y_position, self.page_width-(2000*self.zoom_factor) - x_position
                rect_x1 = rotated_x - side_padding
                rect_y1 = rotated_y - container_width - side_padding
                rect_x2 = rotated_x + text_height + side_padding
                rect_y2 = rotated_y + bottom_padding
                angle = -270
            else:  # rotation_angle == 0
                rotated_x = x_position
                rotated_y = y_position
                rect_x1 = rotated_x - side_padding
                rect_y1 = rotated_y - side_padding
                rect_x2 = rotated_x + container_width + side_padding
                rect_y2 = rotated_y + text_height + bottom_padding
                angle = 0
            
            # Create background rectangle
            bg_rect_id = self.canvas.create_rectangle(
                rect_x1, rect_y1, rect_x2, rect_y2,
                fill="cyan",
                outline="cyan",
                tags="text_annotation_bg"
            )
            
            # Create text
            text_id = self.canvas.create_text(
                rotated_x, rotated_y,
                text=text,
                font=("Arial", fontsize),
                fill=fill_color,
                tags="text_annotation",
                anchor="nw"
            )
            self.canvas.itemconfig(text_id, angle=angle)
            bbox = self.canvas.bbox(text_id)
            
            # Store canvas IDs and bbox
            annotation_data["canvas_id"] = text_id
            annotation_data["bg_rect_id"] = bg_rect_id
            annotation_data["bbox"] = bbox
            
            # Bind drag events to both text and background
            self.canvas.tag_bind(text_id, "<Button-1>", self.on_text_bg_press)
            self.canvas.tag_bind(text_id, "<B1-Motion>", self.on_text_bg_drag)
            self.canvas.tag_bind(text_id, "<ButtonRelease-1>", self.on_text_bg_release)
            
            self.canvas.tag_bind(bg_rect_id, "<Button-1>", self.on_text_bg_press)
            self.canvas.tag_bind(bg_rect_id, "<B1-Motion>", self.on_text_bg_drag)
            self.canvas.tag_bind(bg_rect_id, "<ButtonRelease-1>", self.on_text_bg_release)
        
        self.annotation_is_available = True

    def activate_line_tool(self):
        """Activate the straight line drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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

    def finish_line(self, event):
        """Finish drawing the line and add it to annotations."""
        if self.current_line:
            self.canvas.delete(self.current_line)
        
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        line_id = self.canvas.create_line(
            self.start_x, self.start_y, end_x, end_y,
            fill="red", width=4, tags="annotation")
        line_data = {
            'type': 'line',
            'page': self.current_page,
            'x1': self.start_x / self.zoom_factor,
            'y1': self.start_y / self.zoom_factor,
            'x2': end_x / self.zoom_factor,
            'y2': end_y / self.zoom_factor,
            'id': line_id,
            'color': "red"
        }
        self.lines.append(line_data)
        self.annotations.append(line_data)
        print("line_data",line_data)
        self.change_history.append(('add_annotation', line_data))
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
        arrow_data = {
            'type': 'arrow',
            'page': self.current_page,
            'x1': self.start_x / self.zoom_factor,
            'y1': self.start_y / self.zoom_factor,
            'x2': end_x / self.zoom_factor,
            'y2': end_y / self.zoom_factor,
            'id': arrow_id,
            'color': "red"
        }
        self.arrows.append(arrow_data)
        self.annotations.append(arrow_data)
        print("arrow_data",arrow_data)
        self.change_history.append(('add_annotation', arrow_data))
        self.annotation_is_available = True
        self.annotation_listed.append("arrow")
        
        # Bind drag events to the arrow
        self.canvas.tag_bind(arrow_id, "<Button-1>", self.on_line_press)
        self.canvas.tag_bind(arrow_id, "<B1-Motion>", self.on_line_drag)
        self.canvas.tag_bind(arrow_id, "<ButtonRelease-1>", self.on_line_release)

    def on_line_press(self, event):
        """Handle mouse press on line or arrow."""
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
        
        # Ensure coordinates are properly ordered (top-left to bottom-right)
        x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
        x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        
        # Delete the preview rectangle
        if self.current_rectangle:
            self.canvas.delete(self.current_rectangle)
        
        # Create visual rectangle on canvas
        outline_color = "red"
        fill_color = "" if not filled else "red"
        border_width = 4 if not filled else 3
        rect_id = self.canvas.create_rectangle(
            x1, y1, x2, y2,
            outline=outline_color, fill=fill_color, width=border_width, tags="annotation")
        
        # Store rectangle data (in original PDF coordinates)
        rect_data = {
            'type': 'rectangle',
            'page': self.current_page,
            'x1': x1 / self.zoom_factor,
            'y1': y1 / self.zoom_factor,
            'x2': x2 / self.zoom_factor,
            'y2': y2 / self.zoom_factor,
            'filled': filled,
            'id': rect_id,
            'color': "red"
        }
        
        self.rectangles.append(rect_data)
        self.annotations.append(rect_data)
        self.change_history.append(('add_annotation', rect_data))
        self.annotation_is_available = True
        # self.deactivate_tools()
        self.annotation_listed.append("rectangle")
        self.canvas.tag_bind(rect_id, "<Button-1>", self.on_rectangle_press)
        self.canvas.tag_bind(rect_id, "<B1-Motion>", self.on_rectangle_drag)
        self.canvas.tag_bind(rect_id, "<ButtonRelease-1>", self.on_rectangle_release)
        # if filled:
        #     self.filled_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
        # else:
        #     self.hollow_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")

    def on_rectangle_press(self, event):
        """Handle mouse press on rectangle."""
        # Get the clicked item
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
            self.filled_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
            self.hollow_rectangle_button.configure(fg_color="#00498f", hover_color="#023261")
            
            self.canvas.move(self.dragged_rectangle_id, dx, dy)
            self.rect_drag_start = (x, y)
            
            # Prevent event propagation to avoid page dragging
            return "break"

    # def on_rectangle_release(self, event):
    #     """Update stored annotation data after dragging."""
    #     if not self.dragged_rectangle_id:
    #         return
            
    #     bbox = self.canvas.bbox(self.dragged_rectangle_id)
    #     if not bbox:
    #         self.dragged_rectangle_id = None
    #         self.rect_drag_start = None
    #         return
            
    #     new_x1, new_y1, new_x2, new_y2 = [v / self.zoom_factor for v in bbox]
        
    #     # Update rectangle data
    #     for rect in self.rectangles:
    #         if rect["id"] == self.dragged_rectangle_id and rect["page"] == self.current_page:
    #             old_data = dict(rect)  # Store old data for history
    #             rect.update({
    #                 "x1": new_x1, "y1": new_y1,
    #                 "x2": new_x2, "y2": new_y2
    #             })
    #             self.change_history.append(('move_annotation', old_data, dict(rect)))
    #             break
        
    #     # Update annotation data
    #     for annotation in self.annotations:
    #         if annotation.get("id") == self.dragged_rectangle_id and annotation["page"] == self.current_page:
    #             annotation.update({
    #                 "x1": new_x1, "y1": new_y1,
    #                 "x2": new_x2, "y2": new_y2
    #             })
    #             break
        
    #     # Clear drag state
    #     self.dragged_rectangle_id = None
    #     self.rect_drag_start = None
        
    #     # Prevent event propagation
    #     return "break"

    def on_rectangle_release(self, event):
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
                break

        # Safely update annotation data
        for annotation in self.annotations:
            if isinstance(annotation, dict) and annotation.get("id") == self.dragged_rectangle_id and annotation["page"] == self.current_page:
                annotation.update({
                    "x1": new_x1, "y1": new_y1,
                    "x2": new_x2, "y2": new_y2
                })
                break
        for j, hist in enumerate(self.change_history):
            if hist[0] == "ellipse" and hist[5] == self.dragged_ellipse_id:
                self.change_history[j] = ("ellipse", new_x1, new_y1, new_x2, new_y2, self.dragged_ellipse_id, ann[6])
                break

        # Clear drag state
        self.dragged_rectangle_id = None
        self.rect_drag_start = None

        return "break"


    
    def activate_hollow_ellipse(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
        # Store the actual canvas coordinates (accounting for scrolling)
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        
        # Store the unscaled coordinates by dividing by the zoom factor
        self.start_point = (canvas_x / self.zoom_factor, canvas_y / self.zoom_factor)
        self.current_ellipse = None

    def draw_ellipse(self, event):
        if not self.start_point:
            return
        
        # Get original unscaled start coordinates
        x1, y1 = self.start_point
        
        # Get current canvas coordinates and unscale them
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        x2, y2 = canvas_x / self.zoom_factor, canvas_y / self.zoom_factor
        
        # For display, scale both coordinates by zoom factor
        display_x1, display_y1 = x1 * self.zoom_factor, y1 * self.zoom_factor
        display_x2, display_y2 = x2 * self.zoom_factor, y2 * self.zoom_factor
        
        if self.current_ellipse:
            self.canvas.delete(self.current_ellipse)
        
        outline = "orange"
        fill = "" if self.ellipse_mode == "hollow" else "orange"
        self.current_ellipse = self.canvas.create_oval(
            display_x1, display_y1, display_x2, display_y2, 
            outline=outline, width=4, fill=fill, tags="ellipse"
        )

    def finalize_ellipse(self, event):
        if not self.start_point or not self.current_ellipse:
            return
        x1, y1 = self.start_point
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        x2, y2 = canvas_x / self.zoom_factor, canvas_y / self.zoom_factor
        self.annotations.append(("ellipse", x1, y1, x2, y2, self.current_ellipse, self.ellipse_mode, self.current_page))
        self.change_history.append(("ellipse", x1, y1, x2, y2, self.current_ellipse, self.ellipse_mode))
        self.annotation_listed.append("ellipse")

        self.canvas.tag_bind(self.current_ellipse, "<Button-1>", self.on_ellipse_press)
        self.canvas.tag_bind(self.current_ellipse, "<B1-Motion>", self.on_ellipse_drag)
        self.canvas.tag_bind(self.current_ellipse, "<ButtonRelease-1>", self.on_ellipse_release)
        
    def on_ellipse_press(self, event):
        """Start dragging an ellipse."""
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

        # Convert back to PDF coordinates
        new_x1, new_y1, new_x2, new_y2 = [v / self.zoom_factor for v in bbox]

        for i, ann in enumerate(self.annotations):
            if isinstance(ann, tuple) and ann[0] == "ellipse" and ann[5] == self.dragged_ellipse_id and ann[7] == self.current_page:
                old_annotation = ann
                updated_annotation = ("ellipse", new_x1, new_y1, new_x2, new_y2, self.dragged_ellipse_id, ann[6], ann[7])
                
                # Update annotation list
                self.annotations[i] = updated_annotation

                # Record in history
                self.change_history.append(("move_annotation", old_annotation, updated_annotation))
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
            messagebox.showerror("Zoom Error", "Pixel size has increased beyond the safe threshold.", parent=self.root)
            self.deactivate_selection_mode()
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        if self.time_redact_used == 0:
            messagebox.showinfo("Info", "Use redact only after adding all Annotations and changes if not the redact and annotations will be created on the same file.", parent=self.root)
            response = messagebox.askyesnocancel("Confirm", "Do you want to save changes before using the redact?", parent=self.root)        
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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
        rect_data = {
            'type': 'rectangle',
            'page': self.current_page,
            'x1': x1 / zoom,
            'y1': y1 / zoom,
            'x2': x2 / zoom,
            'y2': y2 / zoom,
            'filled': filled,
            'id': rect_id,
            'color': "black",
            'source': 'local'  # Mark as locally drawn
        }
        
        # Add to local lists (for undo functionality)
        self.redact_rectangles.append(rect_data)
        self.redact_annotations.append(rect_data)
        
        # Also add to API lists (for toggle functionality)
        self.add_pagesize[rect_id] = (self.page_width, self.page_height)
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
        print("self.redact_rectangles---",self.redact_rectangles)
        
        # Only check locally drawn rectangles (redact_rectangles), not API ones
        for rect in reversed(self.redact_rectangles):  # Reverse to get top-most first
            if rect['page'] != self.current_page:
                continue
            x1, y1 = rect['x1'] * zoom, rect['y1'] * zoom
            x2, y2 = rect['x2'] * zoom, rect['y2'] * zoom
            if x1 <= x <= x2 and y1 <= y <= y2:
                # Delete from canvas
                self.canvas.delete(rect['id'])
                
                # Delete from PDF
                page = self.pdf_document.load_page(self.current_page)
                rect_pdf = fitz.Rect(rect['x1'], rect['y1'], rect['x2'], rect['y2'])
                for annot in page.annots():
                    if annot.rect == rect_pdf:
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
                print("self.add_pagesize.pop(rect)-",self.add_pagesize)
                self.render_page(self.current_page)  # Re-render the page to reflect changes
                self.change_redact_history.append(('delete_annotation', rect))
                self.annotation_is_available = bool(self.redact_annotations + self.redact_api_annotations)
                break


# ----------------------------------------------------------------------------------------------------------------------------------------------------------
    # best one for now for local db
    
    # def redraw_black_rectangles_from_db(self):
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
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

    def redraw_black_rectangles_from_api(self):
        """Load and draw all rectangles from API for all pages."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
            return
        
        try:
            url = f"https://idms-dev.blockchaincloudapps.com/api/v1/get-pdf-viewer-redact-info?temp_id={self.temp_id}"
            print("redact url---", url)
            headers = {'Content-Type': 'application/json'}
            response = requests.get(url, headers=headers, timeout=10)
            
            if response.status_code != 200:
                print("Failed to fetch redaction data:", response.text)
                return
                
            response_data = response.json()
            print("redactions from api---", response_data)
            result = [(item["coordinate"], item["page_size"], item["zoom_size"]) for item in response_data["data"]]
            print("result from api---", result)
            
            # Clear existing API rectangles to avoid duplicates
            self.redact_api_rectangles.clear()
            self.redact_api_annotations.clear()
            
            # Store all rectangles data for all pages
            self.all_page_rectangles = {}  # Dictionary to store rectangles by page number
            
            for coord_str, saved_pagesize_str, saved_zoom in result:
                print("coord_str---", coord_str)
                coord = eval(coord_str)  # Consider using json.loads for safety
                print("coord after eval---", coord)
                saved_pagesize = eval(saved_pagesize_str)
                print("saved_pagesize---", saved_pagesize)
                
                page_num = coord['page']
                
                # Initialize page in dictionary if not exists
                if page_num not in self.all_page_rectangles:
                    self.all_page_rectangles[page_num] = []
                
                # Get page dimensions for scaling
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
                
                # Store rectangle data for this page
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
                self.redact_api_rectangles.append(rect_data)
                self.redact_api_annotations.append(rect_data)
            
            # Draw rectangles for current page only
            self._draw_rectangles_for_current_page()
            
        except Exception as e:
            print(f"Error fetching redaction data from API: {e}")

    def _draw_rectangles_for_current_page(self):
        """Draw rectangles only for the currently displayed page."""
        if self.current_page is None or not hasattr(self, 'all_page_rectangles'):
            return
        
        # Clear any existing rectangle drawings on canvas
        self.canvas.delete("annotation")
        
        # Draw rectangles for current page
        if self.current_page in self.all_page_rectangles:
            for rect_data in self.all_page_rectangles[self.current_page]:
                x1 = rect_data['x1'] * self.zoom_factor
                y1 = rect_data['y1'] * self.zoom_factor
                x2 = rect_data['x2'] * self.zoom_factor
                y2 = rect_data['y2'] * self.zoom_factor
                
                rect_id = self.canvas.create_rectangle(
                    x1, y1, x2, y2,
                    outline="black", 
                    fill="black" if rect_data['filled'] else "", 
                    width=3, 
                    tags="annotation"
                )
                
                # Update the canvas_id for this rectangle
                rect_data['canvas_id'] = rect_id
        



if __name__ == "__main__":
    root = ctk.CTk()
    app = DuplicateStickyNotesPDFApp(root)
    root.mainloop()























































































































































# self.file_name_is = "attachment_file.pdf"
#         # icon for the window title
#         icon_path = os.path.join(os.path.dirname(__file__), '..', 'assets', 'Atic.png')
#         self.root.iconbitmap(self.set_window_icon(icon_path))
#         self.zoom_factor = 1.0
#         self.time_redact_used = 0
#         self.lock_screen = "no"
#         self.thumbnails_rendered = False
#         self.stickynotezoomy = 1.0
#         self.annotation_is_available = False
#         self.redact_is_available = False
#         self.page_rotation = 0
#         self.rendered_page_count = 0
#         self.sticky_note_mode = False
#         self.highlight_mode = False
#         self.is_drawing_line = False
#         self.is_drawing_arrow = False
#         self.show_annoated_file = False
#         self.is_drawing_hollow_rect = False  # For hollow rectangle tool
#         self.is_drawing_filled_rect = False
#         self.is_drawing_hollow_circle = False  # Initialize the attribute
#         self.is_drawing_filled_circle = False  # Initialize for filled circle too
#         self.last_x, self.last_y = None, None
#         self.current_line = None
#         self.current_rectangle = None
#         self.annotation_listed = []
#         self.rectangle_id = None
#         self.annotations = [] # Will store all annotations
#         self.lines = []  # Store line annotations
#         self.arrows = []  # Store arrow annotations
#         self.rectangles = [] 
#         self.change_history = []
#         self.change_redact_history = []
#         self.sticky_notes = {}
#         self.thumbnails = []
#         self.thumb_color = []
#         self.thumbnail_labels = []  # Initialize the missing attribute
#         self.thumbnail_cache = {}
#         self.freehand_drawings = []
#         self.redactions = []  # To store redaction info (coordinates)
#         self.redo_redactions = []
#         self.text_annotations = {}
#         self.text_annotations_bg = {}
#         self.page_drawings = {}
#         self.icons = {}
#         self.polygons = []
#         self.redaction_mode = False
#         self.delete_mode = False
#         self.pdf_document = None
#         self.current_page = None
#         self.is_inverted = False
#         self.is_drawing = False  # Default state of the drawing mode
#         self.last_x, self.last_y = None, None  # Initialize these as well
#         self.polygon_mode = None  # 'filled' or 'hollow'
#         self.polygon_size = 50
#         self.start_point = None
#         self.pagenumber_url = None
#         # New attributes for handling movable images
#         self.image_overlays = [] 
#         # create buttons on the window frame
#         self.create_widgets()
#         self.canvas.bind("<Button-1>", self.on_canvas_click) # Left click to draw
#         self.canvas.bind("<Motion>", self.on_mouse_hover) # Hover to show
#         self.root.bind("<Left>", self.prev_page)  # Left arrow for previous page
#         self.root.bind("<Right>", self.next_page)  # Right arrow for next page
#         self.active_tooltip = None
#         # default page size
#         self.page_width = 0
#         self.page_height = 0
#         self.temp_file_path = None
#         # api to save the annotated and redact file
#         server_url = fileurl.split("/samba")[0]
#         self.server_url = server_url+r"/uploads/file-annotations"
#         print("dup server url-------------------------------------------------------",self.server_url)
#         # recieving the url from the protocol handler
#         extracted_filename = self.extract_filename(fileurl)
#         if extracted_filename:
#             self.file_name_is = extracted_filename
#         self.root.title(f"Secondary IDMS PDF Editor - {self.file_name_is}")
#         self.handle_url(fileurl)

#     def extract_filename(self,url):
#         match = re.search(r'/(?P<filename>[^/]+\.pdf)', url)
#         return match.group("filename") if match else None
        

#     # window icon 
#     def set_window_icon(self, icon_path):
#         if os.path.exists(icon_path):
#             try:
#                 self.root.iconphoto(True, ImageTk.PhotoImage(file=icon_path))
#             except Exception as e:
#                 print(f"Failed to set window icon. Error: {e}")
#         else:
#             print(f"Icon file not found: {icon_path}")

#     def create_widgets(self):
#         toolbar = ctk.CTkFrame(self.root)
#         toolbar.pack(fill=ctk.X, pady=8)
#         # button design and size
#         def create_button(parent, text="", image=None, command=None, tooltip_text=""):
#             button = ctk.CTkButton(
#                 parent,
#                 text=text,
#                 image=image,
#                 command=command,
#                 fg_color="#00498f",
#                 text_color="white",
#                 hover_color="#023261",
#                 font=("Arial", 12),
#                 width=45
#             )
#             button.pack(side=ctk.LEFT, padx=3, pady=2)
#             button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
#             button.bind("<Leave>", self.hide_tooltip)
#             return button
#     # load images in the button
#         def load_image(relative_path, size=(25, 25)):
#             if getattr(sys, 'frozen', False):
#                 base_dir = sys._MEIPASS
#             else:
#                 base_dir = os.path.dirname(os.path.abspath(__file__))
#             full_path = os.path.join(base_dir, relative_path)
#             if relative_path.lower().endswith('.svg'):
#                 png_data = cairosvg.svg2png(url=full_path)
#                 image = Image.open(io.BytesIO(png_data))
#             else:
#                 image = Image.open(full_path)
#             image = image.resize(size, Image.LANCZOS)
#             return ImageTk.PhotoImage(image)
#         # for tool tip and image identification   
#         self.icons = {
#             "lock": load_image("assets/lock.svg"),
#             "unlock": load_image("assets/unlock.svg"),
#             "load_pdf": load_image("assets/folder.svg"),
#             "new_window": load_image("assets/new_window.svg"),
#             "zoom_out": load_image("assets/zoom_out.svg"),
#             "zoom_in": load_image("assets/zoom_in.svg"),
#             "refresh_pdf": load_image("assets/refresh.svg"),
#             "prev_page": load_image("assets/prev_page.svg"),
#             "next_page": load_image("assets/next_page.svg"),
#             "undo": load_image("assets/undo.svg"),
#             "highlight": load_image("assets/highlight.svg"),
#             "sticky_note": load_image("assets/note.svg"),
#             "thumb_pin": load_image("assets/thumb_pin_yellow.svg"),
#             "rotate_90": load_image("assets/rotate_90.svg"),
#             "rotate_180": load_image("assets/rotate_180.svg"),
#             "rotate_270": load_image("assets/rotate_270.svg"),
#             "best_fit": load_image("assets/fit_to_page.svg"),
#             "best_width": load_image("assets/width.svg"),
#             "best_height": load_image("assets/height.svg"),
#             "invert_colors": load_image("assets/ying_yang.svg"),
#             "save_pdf": load_image("assets/save.svg"),
#             "zoom_area": load_image("assets/Area.svg"),
#             "free_line": load_image("assets/line.svg"),
#             "filled_polygon": load_image("assets/filled5polygon.svg"),
#             "hollow_polygon": load_image("assets/hollow5polygon.svg"),
#             "straightline": load_image("assets/straightline.svg"),
#             "arrow": load_image("assets/arrow.svg"),
#             "hollow_rectangle": load_image("assets/hollow_rectangle.svg"),
#             "filled_rectangle": load_image("assets/filled_rectangle.svg"),
#             "hollow_ellipse": load_image("assets/hollow_ellipse.svg"),
#             "filled_ellipse": load_image("assets/filled_ellipse.svg"),
#             "text": load_image("assets/text.svg"),
#             "filled_text": load_image("assets/filled_text.svg"),
#             "image": load_image("assets/image.svg"),
#             "selectarrow": load_image("assets/selectarrow.svg"), 
#             "redact": load_image("assets/redact.svg"), 
#             "removeredact": load_image("assets/remove.svg"), 
#             "eye": load_image("assets/eye.svg"), 
#         }

#         if self.lock_screen == "no":
#             button_configs = [
#                 {"image": self.icons['lock'], "command": self.lock_function, "tooltip": "Lock Annotations"},
#                 {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area"},
#                 # {"image": self.icons['eye'], "command": self.show_annotated_file, "tooltip": "Show Annotated File"},
#                 {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Document"},
#                 {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
#                 {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
#                 # {"image": self.icons['zoom_area'], "command": self.toggle_zoom_in_area_mode, "tooltip": "Zoom Area"},
#                 {"image": self.icons['highlight'], "command": self.enable_highlight_mode, "tooltip": "Highlight"},
#                 {"image": self.icons['sticky_note'], "command": self.toggle_sticky_note_mode, "tooltip": "Sticky Note"},
#                 {"image": self.icons['undo'], "command": self.undo_change, "tooltip": "Undo"},
#                 {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
#                 {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
#                 {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
#                 {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
#                 {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
#                 {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
#                 {"image": self.icons['invert_colors'], "command": self.toggle_invert_colors, "tooltip": "Invert Colors"},
#                 {"image": self.icons['save_pdf'], "command": self.save_pdf, "tooltip": "Save PDF"},
#                 # Buttons with instance variables
#                 {"image": self.icons['text'], "command": self.add_text_to_pdf, "tooltip": "Add Text"},
#                 {"image": self.icons['filled_text'], "command": self.add_text_with_background, "tooltip": "Add Text Stamp"},
#                 {"image": self.icons['free_line'], "command": self.toggle_drawing, "tooltip": "Free Hand Line", "instance_var": "draw_button"},
#                 {"image": self.icons['filled_polygon'], "command": self.toggle_filled_polygon_mode, "tooltip": "Draw Filled Polygon", "instance_var": "filled_polygon_button"},
#                 {"image": self.icons['hollow_polygon'], "command": self.toggle_hollow_polygon_mode, "tooltip": "Draw Hollow Polygon", "instance_var": "hollow_polygon_button"},
#                 {"image": self.icons.get('image'), "command": lambda: self.attach_image_to_pdf(), "tooltip": "Attach Image"},
#                 {"image": self.icons['straightline'], "command": self.activate_line_tool, "tooltip": "Draw Straight Line"},
#                 {"image": self.icons['arrow'], "command": self.activate_arrow_tool, "tooltip": "Draw Arrow"},
#                 {"image": self.icons['hollow_rectangle'], "command": self.activate_hollow_rectangle_tool, "tooltip": "Draw Hollow Rectangle"},
#                 {"image": self.icons['filled_rectangle'], "command": self.activate_filled_rectangle_tool, "tooltip": "Draw Filled Rectangle"},
#                 {"image": self.icons['hollow_ellipse'], "command": self.activate_hollow_ellipse, "tooltip": "Draw Hollow Ellipse"},
#                 {"image": self.icons['filled_ellipse'], "command": self.activate_filled_ellipse, "tooltip": "Draw Filled Ellipse"},
#                 {"image": self.icons['redact'], "command": self.activate_black_rectangle_tool, "tooltip": "Add Redaction"},
#                 {"image": self.icons['removeredact'], "command": self.undo_blackrect, "tooltip": "Remove Redaction"}, 
#             ]
#         else:
#             button_configs = [
#                 {"image": self.icons['unlock'], "command": self.lock_function, "tooltip": "Unlock Annotations"},
#                 {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
#                 {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
#                 {"image": self.icons['rotate_90'], "command": self.rotate_90clockwise, "tooltip": "Rotate 90° Right"},
#                 {"image": self.icons['rotate_180'], "command": self.rotate_180clockwise, "tooltip": "Rotate 180° Right"},
#                 {"image": self.icons['rotate_270'], "command": self.rotate_270clockwise, "tooltip": "Rotate 270° Right"},
#                 {"image": self.icons['best_fit'], "command": self.best_fit, "tooltip": "Best Fit"},
#                 {"image": self.icons['best_width'], "command": self.best_width, "tooltip": "Best Width"},
#                 {"image": self.icons['best_height'], "command": self.best_height, "tooltip": "Best Height"},
#             ]
#         current_frame = ctk.CTkFrame(toolbar)
#         current_frame.pack(fill=ctk.X)
#         buttons_in_row = 0

#         for config in button_configs:
#             if buttons_in_row >= 23:  # Start a new line
#                 current_frame = ctk.CTkFrame(toolbar)
#                 current_frame.pack(fill=ctk.X)
#                 buttons_in_row = 0

#             # Create the button
#             button = create_button(
#                 current_frame,
#                 image=config["image"],
#                 command=config["command"],
#                 tooltip_text=config["tooltip"]
#             )
#             buttons_in_row += 1

#             # Assign to instance variable if specified
#             if "instance_var" in config:
#                 setattr(self, config["instance_var"], button)
#         # button frame         
#         nav_frame = ctk.CTkFrame(current_frame, height=25)  # Place inside current_frame    
#         nav_frame.pack(side=ctk.LEFT, pady=0, padx=5)  # Align with buttons
#         # navigation buttons
#         prev_button = ctk.CTkButton(nav_frame, text="<<<", command=self.prev_page, width=30, fg_color="transparent", text_color="black")
#         prev_button.pack(side=ctk.LEFT, padx=0)
#         # button for page jump
#         self.page_entry = ctk.CTkEntry(nav_frame, width=45, justify="center", height=20)
#         self.page_entry.pack(side=ctk.LEFT, padx=0)
#         self.page_entry.insert(0, "1")
#         self.page_entry.bind("<Return>", self.go_to_page, add="+")
#         # total page count
#         self.page_total_label = ctk.CTkLabel(nav_frame, text="/ ?", width=25, fg_color="transparent", text_color="black")
#         self.page_total_label.pack(side=ctk.LEFT, padx=0)
#         # next button navigation
#         next_button = ctk.CTkButton(nav_frame, text=">>>", command=self.next_page, width=30, fg_color="transparent", text_color="black")
#         next_button.pack(side=ctk.LEFT, padx=0)
#         # go button but hidden
#         if getattr(self, "canvas_frame", None) is None:
#             canvas_frame = ctk.CTkFrame(self.root)
#             canvas_frame.pack(fill=ctk.BOTH, expand=True)
#             # thumbnail frame size
#             self.thumbnail_frame = ctk.CTkFrame(canvas_frame, width=175, fg_color="lightgray")
#             self.thumbnail_frame.pack(side=ctk.LEFT, fill=ctk.Y)            
#             # this one is with the total thumnail frame incliding scrollbar
#             self.thumbnail_canvas = ctk.CTkCanvas(self.thumbnail_frame, bg="lightgray", width=250)
#             self.thumbnail_scrollbar = ctk.CTkScrollbar(self.thumbnail_frame, orientation="vertical", command=self.thumbnail_canvas.yview, width=20)
#             self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
#             self.thumbnail_canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
#             self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y, padx=2)
#             # self.thumbnail_canvas.bind("<MouseWheel>", self.on_thumbnail_scroll)
#             self.inner_thumbnail_frame = ctk.CTkFrame(self.thumbnail_canvas, fg_color="lightgray")
#             self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
#             self.inner_thumbnail_frame.bind("<Configure>", lambda e: self.update_scroll_region() if self.pdf_document else None)
#             # total main frame size
#             self.canvas = ctk.CTkCanvas(canvas_frame, bg="lightgray", width=1050, height=750) # 
#             self.h_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="horizontal", command=self.canvas.xview)
#             self.v_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="vertical", command=self.canvas.yview)
#             self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
#             self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
#             self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
#             self.canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
#             # mouse wheel event for pdf render window for scrolling the pdf render
#             self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
#             self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
            
#     # to show the button name when hover
#     def button_tooltip(self, event, button_text, tooltip_text):
#         """Display tooltip when hovering over a button."""
#         if self.active_tooltip:
#             self.active_tooltip.destroy() # to destroy automatiacally each second
#         tooltip = ctk.CTkToplevel(self.root)
#         tooltip.wm_overrideredirect(True) # it used for closing tooltip
#         tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")  # text Position near the mouse hover
#         # tooltip design
#         label = ctk.CTkLabel(tooltip, text=tooltip_text, fg_color="light yellow",text_color="black", padx=5, pady=5)
#         label.pack()
#         if self.active_tooltip:
#             self.active_tooltip.destroy()
#         # activating tool tip
#         self.active_tooltip = tooltip
        
#     # remove or deactivate when not over
#     def hide_tooltip(self, event):
#         """Hide tooltip when the mouse leaves the button."""
#         if self.active_tooltip: 
#             self.active_tooltip.destroy()
#             self.active_tooltip = None

#     # load the pdf in the same frame
#     def split_url(self,url):
#         first_split = url.split('?', 1)
#         if len(first_split) < 2:
#             return url, ''
#         base, rest = first_split
#         second_split = rest.split('?', 1)
#         if len(second_split) == 2:
#             return f"{base}?{second_split[0]}", f"?{second_split[1]}"
#         else:
#             return f"{base}?{rest}", ''


#     #to handle url and filter the page number when passed
#     def handle_url(self, url):
#         """Handle a new URL (load the PDF) and restore the window if minimized."""
#         try:
#             print("dzdzdbzbd",url)
#             self.root.deiconify()  # Restore the window if it is minimized
#             self.root.lift()  # Bring the window to the front
#             self.root.focus_force()  # Ensure it gets focus
#             self.root.attributes("-topmost", True)  # Set the window to always be on top
#             self.root.after(500, lambda: self.root.attributes("-topmost", False))

#             extracted_filename = self.extract_filename(url)  # Extract new filename
#             if extracted_filename:
#                 self.file_name_is = extracted_filename  # Update the filename
#                 print("extracted filename",self.file_name_is)
            
#             part1, part2 = self.split_url(url)
#             query = part2.lstrip("?")        
#             # Parse the query string
#             params = parse_qs(query)
#             # Extract values
#             if "page" in part2:
#                 page_number = params.get("page_number", [None])[0]
#                 if page_number != None:
#                     page_number = page_number.strip()
#             else:
#                 page_number = None
#             self.pagenumber_url = page_number
#             try:
#                 user_id = params.get("user_id", [None])[0].strip()
#             except Exception as e:
#                 print("Error extracting user_id:", e)
#                 user_id = None
#             # self.loaderurl = part1.split('samba/')[0] + 'samba/'+"close-file-loader/"+user_id
#             # self.loaderurl = "http://172.20.1.218:3001/api/v1/"+"samba/"+"close-file-loader/"+user_id
#             print("user id",user_id)
#             print("page number",page_number)
#             print("part1",part1)
#             print("part2",part2)
#             if self.is_valid_pdf_url(part1):
#                 self.load_pdf(part1)
#                 # Update the window title with the new file name
#                 self.root.title(f"Secondary IDMS PDF Editor - {self.file_name_is}")
#             else:
#                 print(f"Invalid PDF URL: {part1}")
#                 # Handle invalid URL (show error message to user)
#                 messagebox.showerror("Error", f"The URL does not point to a valid PDF file")
#         except Exception as e:
#             print(f"Error handling URL: {e}")
#             messagebox.showerror("Error", f"Failed to process URL")
    
#     def is_valid_pdf_url(self, url):
#         """Check if the URL is valid and points to a PDF file."""
#         try:
#             # Check if URL is properly formatted
#             parsed_url = urlparse(url)
#             if not all([parsed_url.scheme, parsed_url.netloc]):
#                 return False         
#             # Check if the URL exists and returns proper headers
#             # Using HEAD request to avoid downloading the entire file
#             response = requests.head(url, timeout=5)           
#             # Check if the request was successful
#             if response.status_code != 200:
#                 return False       
#             # Check if it's a PDF based on Content-Type header
#             content_type = response.headers.get('Content-Type', '')
#             if 'application/pdf' in content_type:
#                 return True            
#             # If Content-Type is not reliable, check file extension
#             if url.lower().endswith('.pdf'):
#                 return True             
#             return False
            
#         except Exception as e:
#             print(f"Error validating URL: {e}")
#             return False


#     # Enable or disable scrollbar based on the number of pages
#     def update_scroll_region(self):
#         """Ensures that the scroll region updates properly when thumbnails are added."""
#         self.inner_thumbnail_frame.update_idletasks()  # Ensure layout updates first
#         self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
 
#         # Enable or disable scrollbar based on the number of pages
#         if len(self.pdf_document) > 4:
#             self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
#             self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
#         else:
#             self.thumbnail_scrollbar.pack_forget()  # Hide scrollbar
#             self.thumbnail_canvas.configure(yscrollcommand="")  # Disable scrolling
    
#     def notify_loader(self):
#         try:
#             print("Notifying loader server...")
#             response = requests.get(self.loaderurl, timeout=5)
#             print("Loader notified, status code:", response.status_code)
#         except Exception as e:
#             print("Failed to notify loader:", e)
    
#     def _load_pdf_internal(self):
#         """Internal function that handles PDF loading (called in a thread)."""
#         self.root.after(0, lambda: self.canvas.config(cursor="watch"))  # show wait cursor

#         try:
#             # All your existing code from `load_pdf` here (starting from print(f"Loading PDF..."))
#             # Don't modify the UI directly from this thread! Use `self.root.after(...)` for UI updates.

#             # Example: replace this direct call
#             # self.render_page(self.current_page)
#             # with:
#             try:
#                 self.root.after(500, lambda: self.best_fit())
#             except:
#                 print("Error in best_fit in load pdf")
#         except Exception as e:
#             print("Error loading PDF:", e)
#         finally:
#             self.root.after(0, lambda: self.canvas.config(cursor=""))

#     # load pdf from the server and local 
#     def load_pdf(self, file_path=None):
#         """Load a PDF file from the specified path or URL."""
#         if not file_path:
#             file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
#         if not file_path:
#             print("No file selected")
#             return

#         print(f"Loading PDF from: {file_path}")

#         # Reset editor states
#         self.sticky_notes.clear()
#         self.canvas.delete("sticky_note")
#         self.zoom_factor = 1.0
#         self.stickynotezoomy = 1.0
#         self.page_rotation = 0
#         self.time_redact_used = 0
#         self.sticky_note_mode = False
#         self.highlight_mode = False
#         self.annotation_listed = []
#         self.rectangle_id = None
#         self.annotations = [] # Will store all annotations
#         self.lines = []  # Store line annotations
#         self.arrows = []  # Store arrow annotations
#         self.rectangles = [] 
#         self.change_history = []
#         self.change_redact_history = []
#         self.sticky_notes = {}
#         self.thumbnails = []
#         self.thumb_color = []
#         self.thumbnail_labels = []  # Initialize the missing attribute
#         self.thumbnail_cache = {}
#         self.freehand_drawings = []
#         self.redactions = []  # To store redaction info (coordinates)
#         self.redo_redactions = []
#         self.text_annotations = {}
#         self.text_annotations_bg = {}
#         self.rendered_page_count = 0
#         self.page_drawings = {}
#         self.polygons = []
#         self.image_overlays = []
#         self.is_drawing_hollow_rect = False
#         self.is_drawing_filled_rect = False
#         self.is_drawing_hollow_circle = False
#         self.is_drawing_filled_circle = False
#         self.current_rectangle = None
#         self.rectangle_id = None
#         self.lock_screen = "no"
#         self.annotation_is_available = False
#         self.redact_is_available = False
#         self.load_pdf_url = file_path
#         try:
#             parsed = urlparse(file_path)
#             if parsed.scheme in ("http", "https"):
#                 print("Downloading PDF from URL...")
#                 pdf_data = None
#                 try:
#                     response = requests.get(file_path)
#                     response.raise_for_status()
#                     pdf_data = response.content
#                 except requests.exceptions.SSLError:
#                     try:
#                         print("SSL Error: Retrying without SSL verification...")
#                         response = requests.get(file_path, verify=False)
#                         response.raise_for_status()
#                         pdf_data = response.content
#                     except Exception as ssl_error:
#                         print(f"Failed to load PDF due to SSL issue: {ssl_error}")

#                 if pdf_data:
#                     self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
#                 else:
#                     print("SSL verification failed, attempting to load from decoded URL...")
#                     decoded_url = unquote(file_path)
#                     print(f"Decoded URL: {decoded_url}")
#                     response = requests.get(decoded_url, verify=False)
#                     response.raise_for_status()
#                     self.pdf_document = fitz.open(stream=response.content, filetype="pdf")

#             elif os.path.exists(file_path):  # Local file handling
#                 print("Opening local PDF...")
#                 self.pdf_document = fitz.open(file_path)
#             else:
#                 print("Invalid file path or URL.")
#                 return

#             if len(self.pdf_document) == 0:
#                 raise ValueError("The PDF has no pages.")

#             global fileurl
#             fileurl = file_path
#             self.pdf_path = file_path
#             self.current_page = int(self.pagenumber_url) - 1 if self.pagenumber_url is not None else 0
#             self.pagenumber_url = None

#             self.page_drawings = {}
#             self.is_inverted = False
#             self.text_annotations.clear()
#             self.text_annotations_bg.clear()
#             first_page = self.pdf_document[self.current_page]
#             self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
#             print(f"Page Width: {self.page_width}, Page Height: {self.page_height}")

#             global is_small_page
#             if self.page_width < 1000:
#                 is_small_page = "yes"
#             elif 2000 < self.page_width < 3000 and self.page_height > 2800:
#                 is_small_page = "longer"
#             elif 1000 <= self.page_width < 2500:
#                 is_small_page = "slightly"
#             elif 2500 <= self.page_width < 3000:
#                 is_small_page = "maybe"
#             elif 3000 <= self.page_width < 5000:
#                 is_small_page = "nope large"
#             else:
#                 is_small_page = "no"

#             # self.render_thumbnails()
#             # self.render_page(self.current_page)
#             # self.root.after(500, lambda: self.update_thumbnail_selection(self.current_page))
#             # print("load_pdf running ---",self.loaderurl)

#             self.root.after(0, lambda: self.render_page(self.current_page))
#             self.root.after(0, lambda: self.render_thumbnails())
#             self.root.after(500, lambda: self.update_thumbnail_selection(self.current_page))
#             # threading.Thread(target=self._load_pdf_internal, args=(file_path,), daemon=True).start()

#         except Exception as e:
#             print(f"Failed to load PDF: {e}")
#             self.pdf_document = None
#             self.current_page = None

#         self.update_page_display()
#         decoded_url = unquote(file_path)
#         print(f"Loaded PDF decoded: {decoded_url}")
#         global filename_pdf
#         global edit_file_name
#         global folderpath
#         global annotated_url
#         global annotatedredact_url
#         global redacted_name
#         global beforeexe
#         try:
#             filename_pdf = decoded_url.split('/')[-1]
#         except:
#             filename_pdf = decoded_url.split('\\')[-1]
#         beforeexe = filename_pdf.rsplit('.pdf', 1)[0]
#         if "_redact.pdf" in file_path:
#             edit_file_name = beforeexe.replace('_redact.pdf', '.pdf')
#             redacted_name = beforeexe + ".pdf"
#             folderpath = decoded_url.split('path=')[1]
#             folderpath = folderpath.replace('_redact.pdf', '.pdf')
#             annotatedredact_url = decoded_url.replace('.pdf', '_with_annotations.pdf')
#             annotated_url = decoded_url.replace('_redact.pdf', '_with_annotations.pdf')

#         elif "redact_with_annotations.pdf" in decoded_url:
#             annotated_url = decoded_url.replace('_redact_with_annotations.pdf', '_with_annotations.pdf')
#             annotatedredact_url = decoded_url
#             redacted_name = annotatedredact_url
#             edit_file_name = beforeexe + ".pdf"
#             folderpath = decoded_url.split('path=')[1]
#             folderpath = folderpath.replace('_redact_with_annotations.pdf', '.pdf')
#             print("redact folderpath", folderpath)
#             print("suppperrrrrrr")

#         elif "_with_annotations.pdf" in decoded_url:
#             annotated_url = decoded_url
#             annotatedredact_url = decoded_url.replace('_with_annotations.pdf','_redact_with_annotations.pdf')
#             edit_file_name = beforeexe + ".pdf"
#             redacted_name = annotatedredact_url
#             folderpath = decoded_url.split('path=')[1]
#             folderpath = folderpath.replace('_with_annotations.pdf', '.pdf')
#             print("annoted folderpath", folderpath)
#             print("suppperrrrrrr")

#         else:
#             annotated_url = decoded_url.replace('.pdf', '_with_annotations.pdf')
#             annotatedredact_url = decoded_url.replace('.pdf', '_redact_with_annotations.pdf')
#             redacted_name = decoded_url.replace('.pdf', '_redact.pdf')
#             edit_file_name = beforeexe + ".pdf"
#             folderpath = decoded_url.split('path=')[1]
#             print("else haiii")
            
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("file_path-------",file_path)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("editedfilename_pdf-------",edit_file_name)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("annotated_url*****************",annotated_url)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("annotatedredact_url ------------------------",annotatedredact_url)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("folder_pathfolder_path----",folderpath)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("redacted_name ------------------------",redacted_name)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("beforeexe ------------------------",beforeexe)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
#         print("filename_pdf ------------------------",filename_pdf)
#         print("------------------------------------------------------------------------------------------------------------------------------------------")
# ##########################################################################################################################################################################################

#     def render_thumbnails(self):
#         """
#         Render thumbnails for all pages in the PDF document efficiently.
#         Ensures all pages are rendered correctly, even in large PDFs.
#         """
#         if not self.pdf_document:
#             print("No PDF document loaded for thumbnails.")
#             return
#         # Clear existing thumbnails to prevent duplicates
#         for widget in self.inner_thumbnail_frame.winfo_children():
#             widget.destroy()
#         global thumb_color
#         thumb_color = []       
#         thumbnail_width = 100
#         thumbnail_height = 150
#         total_pages = len(self.pdf_document)
#         def batch_load_thumbnails(start_page, batch_size=10):
#             """Load thumbnails in batches to improve performance and UI responsiveness."""
#             end_page = min(start_page + batch_size, total_pages)
#             for page_number in range(start_page, end_page):
#                 if page_number in self.thumbnail_cache:
#                     continue  # Skip already cached thumbnails
#                 try:
#                     page = self.pdf_document.load_page(page_number)
#                     pix = page.get_pixmap(matrix=fitz.Matrix(0.5, 0.5))  # Scale down
#                     img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
#                     img.thumbnail((thumbnail_width, thumbnail_height), Image.LANCZOS)
#                     photo = ImageTk.PhotoImage(img)
#                     self.thumbnail_cache[page_number] = photo
#                     self.inner_thumbnail_frame.after(0, lambda p=page_number, ph=photo: add_thumbnail(p, ph))
#                 except Exception as e:
#                     print(f"Error rendering thumbnail for page {page_number}: {e}")

#             if end_page < total_pages:
#                 self.inner_thumbnail_frame.after(100, lambda: batch_load_thumbnails(end_page))
#             else:
#                 self.inner_thumbnail_frame.after(500, self.update_scroll_region)
#                 self.inner_thumbnail_frame.after(1000, lambda: self.thumbnail_canvas.yview_moveto(0))

#         def add_thumbnail(page_number, photo):
#             """Add a rendered thumbnail to the UI with a proper layout (grid for large PDFs)."""
#             label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
#             label.image = photo  # Keep reference
#             if total_pages > 50:
#                 row = page_number // 2  # Arrange in a grid (2 columns)
#                 col = page_number % 2
#                 label.grid(row=row, column=col, padx=5, pady=5, sticky="w")
#             else:
#                 label.pack(pady=5, padx=45)
#             label.bind("<Button-1>", self.create_page_selection_handler(page_number))
#             self.thumbnails.append(label)
#             thumb_color.append(label)
#         batch_load_thumbnails(0)

# ######################################################################################################################################################################################################################
#     # to pass the page number to the selected page
#     def create_page_selection_handler(self, page_number):
#         """Return a handler function to navigate to the selected page."""
#         def handler(event):
#             print(f"Thumbnail {page_number} clicked.")  # Debug log
#             self.select_page(page_number)
#         return handler
    
#     # to render the page on the canvas and highlight the selected page
#     def update_thumbnail_selection(self,page_number):
#         """Update the highlight of the selected thumbnail."""
#         # print("Updating thumbnail selection...",self.thumbnails)  # Debug log
#         print("page number of thumbnail-------------------------------------------------",page_number)
#         for label in thumb_color:
#             label.configure(text=f"Page {thumb_color.index(label) + 1}",text_color="black")
#             if hasattr(label, "original_image"):
#                 label.configure(image=label.original_image)
#         # Update selected thumbnail
#         selected_label = thumb_color[page_number]
#         selected_label.configure(text="Selected Page",text_color="red")
#         self.inner_thumbnail_frame.update_idletasks()
#     # to render the selected page on the canvas
#     def select_page(self, page_number):
#         """Handle thumbnail click event to switch pages."""
#         if 0 <= page_number < len(self.pdf_document):
#             self.current_page = page_number
#             self.render_page(self.current_page)
#             self.update_page_display() # Update page number display
#             self.update_thumbnail_selection(page_number) # Highlight selected thumbnail

#     def lock_function(self):
#         self.lock_screen = "yes" if self.lock_screen == "no" else "no"
#         current_page_number = self.current_page
#         current_pdf = self.pdf_document

#         # Destroy all widgets safely
#         for widget in self.root.winfo_children():
#             widget.destroy()

#         # Reset widget references before re-creating
#         self.canvas = None
#         self.thumbnail_canvas = None
#         self.thumbnail_frame = None
#         self.inner_thumbnail_frame = None
#         self.thumbnail_labels = []
#         self.thumbnails = []
#         self.thumb_color = []
#         self.thumbnail_cache = {}

#         # Re-create all widgets
#         self.create_widgets()

#         # Restore the PDF and page view
#         if current_pdf and current_page_number is not None:
#             self.pdf_document = current_pdf
#             self.current_page = current_page_number

#             self.render_page(self.current_page)

#             # Delay thumbnail rendering slightly to ensure canvas is ready
#             self.root.after(150, self.render_thumbnails)

#             self.update_page_display()
#             self.root.after(500, lambda: self.update_thumbnail_selection(self.current_page))

#             self.canvas.config(cursor="arrow")
#             self.canvas.bind("<Motion>", self.on_mouse_hover)
#             self.page_entry.delete(0, "end")
#             self.page_entry.insert(0, str(self.current_page + 1))
#             self.page_total_label.configure(text=f"/ {len(self.pdf_document)}")

#     # increase the page size by .2 ever time.
#     def zoom_in(self):
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.zoom_factor += 0.2
#         self.render_page(self.current_page)
#     # decrease the page size by .2 ever time.    
#     def zoom_out(self):
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         if self.zoom_factor > 0.4:
#             self.zoom_factor -= 0.2
#             self.render_page(self.current_page)
#     # to render the page in perfect fit in width or height to see all the content
#     def best_fit(self):
#         """Adjust the zoom level to fit the entire PDF page within the canvas."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return

#         canvas_width = self.canvas.winfo_width()
#         canvas_height = self.canvas.winfo_height()

#         page = self.pdf_document.load_page(self.current_page)
#         page_width, page_height = page.rect.width, page.rect.height

#         width_scale = canvas_width / page_width
#         height_scale = canvas_height / page_height
#         self.zoom_factor = min(width_scale, height_scale)

#         self.render_page(self.current_page)
#     # to show the page number entered in the entry box
#     def go_to_page(self, event=None):
#         try:
#             page_number = int(self.page_entry.get()) - 1  # Convert to zero-based index
#             if 0 <= page_number < len(self.pdf_document):
#                 self.current_page = page_number
#                 self.render_page(self.current_page)
#                 self.update_thumbnail_selection(self.current_page)
#             else:
#                 messagebox.showerror("Error", "Invalid page number.",parent=self.root)
#         except ValueError:
#             messagebox.showerror("Error", "Enter a valid page number.",parent=self.root)


#     # to remove all the changes by reloading the url again
#     def refresh(self):
#         """
#         Prompts the user to save the file and reloads the PDF if confirmed.
#         If the user declines, nothing happens.
#         """
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         response = messagebox.askyesnocancel("Confirm", "Would you like to save the file before refreshing? Any unsaved changes will be permanently lost.",parent=self.root)
#         if response is None:
#             return
#         elif response:
#             try:
#                 self.save_pdf()
#                 self.handle_url(self.load_pdf_url)
#             except Exception as e:
#                 messagebox.showerror("Error","An error occurred during refresh",parent=self.root)
#         else:
#             # User clicked 'No', just refresh without saving
#             self.handle_url(self.pdf_path)

#     # if a file related to the url is saved after change to show when clicked if it 
#     # has redacted it shows redacted as pirority even if annoted file is also saved
#     def show_annotated_file(self):
#         """Toggle the visibility of annotations on the canvas."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         response = messagebox.askyesno(
#             "Confirm",
#             "Are you sure you want to view if this page has annotations? Any unsaved changes will be lost.",
#             parent=self.root
#         )
#         if not response:
#             return
#         for url in [annotatedredact_url, annotated_url,redacted_name]:
#             if url:
#                 try:
#                     parsed = urlparse(url)
#                     if parsed.scheme in ('http', 'https'):
#                         try:
#                             response = requests.head(url, allow_redirects=True, timeout=5)
#                             if response.status_code == 200 and 'application/pdf' in response.headers.get('Content-Type', ''):
#                                 self.handle_url(url)
#                                 return
#                         except requests.RequestException:
#                             continue
#                     elif os.path.isfile(url) and url.lower().endswith('.pdf'):
#                         self.handle_url(url)
#                         return
#                 except Exception:
#                     continue

#         messagebox.showinfo("Info", "No Annotation were saved to view.",parent=self.root)

#     # to show the width in perfect width to see all the content as per window width
#     def best_width(self):
#         """Adjust the zoom level to fit the entire PDF page to the canvas width."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return

#         canvas_width = self.canvas.winfo_width()
#         page = self.pdf_document.load_page(self.current_page)
#         page_width = page.rect.width

#         self.zoom_factor = canvas_width / page_width
#         self.render_page(self.current_page)

#     # to show the height in perfect height to see all the content as per window height
#     def best_height(self):
#         """Adjust the zoom level to fit the entire PDF page to the canvas height."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return

#         canvas_height = self.canvas.winfo_height()
#         page = self.pdf_document.load_page(self.current_page)
#         page_height = page.rect.height

#         self.zoom_factor = canvas_height / page_height
#         self.render_page(self.current_page)

#     # to show all the changes done on the pdf by render the pdf after each change.
#     def render_page(self, page_number):
#         """Render a PDF page to the canvas with the current zoom factor."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         # Load and render the PDF page
        
#         global pageinfo
#         pageinfo = page_number
#         page = self.pdf_document.load_page(page_number)
#         print("page_number - ",page_number)
#         matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
#         pix = page.get_pixmap(matrix=matrix)
#         img = Image.open(io.BytesIO(pix.tobytes("png")))
#         # Apply inversion if needed
#         if self.is_inverted:
#             img = ImageOps.invert(img.convert("RGB"))
#         # Convert to a format suitable for display
#         img_tk = ImageTk.PhotoImage(img)
#         # Clear and redraw the canvas
#         self.canvas.delete("all")
#         self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
#         self.canvas.img_tk = img_tk  # Keep a reference to prevent garbage collection
#         # Update scrollable region
#         self.page_width, self.page_height = pix.width, pix.height
#         self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
#         print("self.rendered_page_count---",self.rendered_page_count)
#         if self.rendered_page_count == 0:
#             print("best fit running haiiiii.")
#             threading.Thread(target=self._load_pdf_internal, daemon=True).start()
#             self.rendered_page_count += 1
#         # Redraw sticky notes    
#         self.redraw_sticky_notes()
#         self.redraw_text_annotations()
#         self.redraw_text_with_background()
#         self.redraw_polygons()
#         self.redraw_all_annotations()
#         self.redraw_image_overlays(page_number)
#         self.redraw_freehand_drawings()
#         self.canvas.config(scrollregion=self.canvas.bbox("all"))

#     # def redraw_image_overlays(self, page_number):
#     #     """Redraw image overlays for the current page with proper scaling."""
#     #     if not hasattr(self, "image_overlays"):
#     #         self.image_overlays = []
#     #         return
            
#     #     # Clear existing image overlays from canvas
#     #     self.canvas.delete("image_overlay")
#     #     self.tk_images = {}  # Reset the tk_images dictionary
        
#     #     current_page_overlays = [overlay for overlay in self.image_overlays if overlay["page"] == page_number]
        
#     #     for overlay in current_page_overlays:
#     #         try:
#     #             # Get the base coordinates and size
#     #             base_x = overlay["base_x"]
#     #             base_y = overlay["base_y"]
#     #             base_width = overlay["base_width"]
#     #             base_height = overlay["base_height"]
                
#     #             # Apply zoom factor to coordinates and dimensions
#     #             scaled_x = base_x * self.zoom_factor
#     #             scaled_y = base_y * self.zoom_factor
#     #             scaled_width = base_width * self.zoom_factor
#     #             scaled_height = base_height * self.zoom_factor
                
#     #             # Update overlay with scaled values for reference
#     #             overlay["x"] = scaled_x
#     #             overlay["y"] = scaled_y
#     #             overlay["width"] = scaled_width
#     #             overlay["height"] = scaled_height
                
#     #             # Resize and display the image
#     #             img = Image.open(overlay["image_path"])
#     #             img = img.resize((int(scaled_width), int(scaled_height)), Image.LANCZOS)
#     #             tk_img = ImageTk.PhotoImage(img)
#     #             self.tk_images[overlay["id"]] = tk_img
                
#     #             canvas_id = self.canvas.create_image(
#     #                 scaled_x, scaled_y,
#     #                 image=tk_img,
#     #                 anchor="nw",
#     #                 tags=("image_overlay", overlay["id"]))
#     #             overlay["canvas_id"] = canvas_id
                
#     #         except Exception as e:
#     #             print(f"Failed to redraw image overlay: {e}")

#     def redraw_image_overlays(self, page_number):
#         """Redraw image overlays for the current page with proper scaling and rotation."""
#         if not hasattr(self, "image_overlays"):
#             self.image_overlays = []
#             return
#         self.canvas.delete("image_overlay")
#         self.tk_images = {}  # Reset the tk_images dictionary
        
#         rotation_angle = 0
#         if self.pdf_document:
#             page = self.pdf_document[page_number]
#             rotation_angle = page.rotation
        
#         page_width = self.page_width
#         page_height = self.page_height
        
#         current_page_overlays = [overlay for overlay in self.image_overlays if overlay["page"] == page_number]
        
#         for overlay in current_page_overlays:
#             try:
#                 # Get base coordinates and dimensions (unscaled)
#                 base_x = overlay["base_x"]
#                 base_y = overlay["base_y"]
#                 base_width = overlay["base_width"]
#                 base_height = overlay["base_height"]
                
#                 # Apply zoom scaling
#                 scaled_x = base_x * self.zoom_factor
#                 scaled_y = base_y * self.zoom_factor
#                 scaled_width = base_width * self.zoom_factor
#                 scaled_height = base_height * self.zoom_factor
                
#                 # Apply rotation transformation
#                 # For proper positioning, we need to rotate coordinates based on rotation angle
#                 if rotation_angle == 0:
#                     rotated_x, rotated_y = scaled_x, scaled_y
#                     display_width, display_height = scaled_width, scaled_height
#                 else:
#                     # For rotations, we need to handle the center point of the image
#                     # Calculate the position from the center of the original image
#                     center_x_orig = scaled_x + (scaled_width / 2)
#                     center_y_orig = scaled_y + (scaled_height / 2)
                    
#                     # Use rotate_point to get the rotated position
#                     rotated_center_x, rotated_center_y = self.rotate_point(
#                         center_x_orig, center_y_orig, 
#                         page_width, page_height, 
#                         rotation_angle)
                    
#                     # Swap dimensions for 90° and 270° rotations
#                     if rotation_angle in [90, 270]:
#                         display_width, display_height = scaled_height, scaled_width
#                     else:
#                         display_width, display_height = scaled_width, scaled_height
                    
#                     # Calculate the top-left corner from the center point
#                     rotated_x = rotated_center_x - (display_width / 2)
#                     rotated_y = rotated_center_y - (display_height / 2)
                
#                 # Update overlay with new coordinates
#                 overlay["x"] = rotated_x
#                 overlay["y"] = rotated_y
#                 overlay["width"] = display_width
#                 overlay["height"] = display_height
                
#                 # Load and prepare the image
#                 img = Image.open(overlay["image_path"])
                
#                 # Rotate the image if needed
#                 if rotation_angle != 0:
#                     pil_rotation = {
#                         90: 270,  # PIL uses counter-clockwise rotation
#                         180: 180,
#                         270: 90
#                     }.get(rotation_angle, 0)
#                     img = img.rotate(pil_rotation, expand=True)
                
#                 # Resize the image
#                 img = img.resize((int(display_width), int(display_height)), Image.LANCZOS)
                
#                 # Convert to Tkinter PhotoImage
#                 tk_img = ImageTk.PhotoImage(img)
#                 self.tk_images[overlay["id"]] = tk_img
                
#                 # Create the image on canvas
#                 canvas_id = self.canvas.create_image(
#                     rotated_x, rotated_y,
#                     image=tk_img,
#                     anchor="nw",
#                     tags=("image_overlay", overlay["id"]))
                    
#                 overlay["canvas_id"] = canvas_id
                
#             except Exception as e:
#                 print(f"Failed to redraw image overlay: {e}")

#     def redraw_all_annotations(self):
#         """Redraw all annotations on the current page with proper rotation"""
#         if not self.pdf_document:
#             return
#         page = self.pdf_document[self.current_page]
#         rotation_angle = page.rotation  # Get current page rotation
        
#         self.redraw_lines(rotation_angle)
#         self.redraw_arrows(rotation_angle)
#         self.redraw_rectangles(rotation_angle)
#         self.redraw_ellipses(rotation_angle)

#     def redraw_lines(self, rotation_angle=0):
#         """Redraw all line annotations for the current page with rotation"""
#         self.canvas.delete("line")
#         page_width, page_height = self.page_width, self.page_height
        
#         for annotation in self.lines:
#             if annotation['page'] == self.current_page:
#                 # Apply zoom factor to coordinates
#                 x1 = annotation['x1'] * self.zoom_factor
#                 y1 = annotation['y1'] * self.zoom_factor
#                 x2 = annotation['x2'] * self.zoom_factor
#                 y2 = annotation['y2'] * self.zoom_factor
                
#                 # Apply rotation
#                 x1, y1 = self.rotate_point(x1, y1, page_width, page_height, rotation_angle)
#                 x2, y2 = self.rotate_point(x2, y2, page_width, page_height, rotation_angle)
                
#                 self.canvas.create_line(
#                     x1, y1, x2, y2,
#                     fill="red", width=3, tags=("annotation", "line"))

#     def redraw_arrows(self, rotation_angle=0):
#         """Redraw all arrow annotations for the current page with rotation"""
#         self.canvas.delete("arrow")
#         page_width, page_height = self.page_width, self.page_height
        
#         for annotation in self.arrows:
#             if annotation['page'] == self.current_page:
#                 # Apply zoom factor to coordinates
#                 x1 = annotation['x1'] * self.zoom_factor
#                 y1 = annotation['y1'] * self.zoom_factor
#                 x2 = annotation['x2'] * self.zoom_factor
#                 y2 = annotation['y2'] * self.zoom_factor
                
#                 # Apply rotation
#                 x1, y1 = self.rotate_point(x1, y1, page_width, page_height, rotation_angle)
#                 x2, y2 = self.rotate_point(x2, y2, page_width, page_height, rotation_angle)
                
#                 self.canvas.create_line(
#                     x1, y1, x2, y2,
#                     fill="red", width=3, arrow=ctk.LAST, 
#                     arrowshape=(16, 20, 6), tags=("annotation", "arrow"))

#     def redraw_rectangles(self, rotation_angle=0):
#         """Redraw all rectangle annotations for the current page with rotation"""
#         self.canvas.delete("rectangle")
#         page_width, page_height = self.page_width, self.page_height
        
#         for annotation in self.rectangles:
#             print("annotation ------------------",annotation)
#             if annotation['page'] == self.current_page:
#                 # Apply zoom factor to coordinates
#                 x1 = annotation['x1'] * self.zoom_factor
#                 y1 = annotation['y1'] * self.zoom_factor
#                 x2 = annotation['x2'] * self.zoom_factor
#                 y2 = annotation['y2'] * self.zoom_factor
                
#                 # For rectangles, we need to rotate all four corners
#                 corners = [
#                     (x1, y1),
#                     (x2, y1),
#                     (x2, y2),
#                     (x1, y2)
#                 ]
                
#                 # Rotate each corner
#                 rotated_corners = []
#                 for x, y in corners:
#                     rx, ry = self.rotate_point(x, y, page_width, page_height, rotation_angle)
#                     rotated_corners.extend([rx, ry])
                
#                 outline_color = annotation['color']
#                 fill_color = "" if not annotation['filled'] else annotation['color']
                
#                 # Draw as polygon instead of rectangle to handle rotation
#                 self.canvas.create_polygon(
#                     rotated_corners,
#                     outline=outline_color, fill=fill_color, 
#                     width=3, tags=("annotation", "rectangle"))

#     def redraw_ellipses(self, rotation_angle=0):
#         """Redraw all ellipse annotations on the current page with correct rotation"""
#         self.canvas.delete("ellipse")
        
#         ellipse_annotations = [ann for ann in self.annotations 
#                             if isinstance(ann, tuple) and ann[0] == 'ellipse' 
#                             and ann[1] is not None]
        
#         for annotation in ellipse_annotations:
#             _, x1, y1, x2, y2, _, mode,numb = annotation
#             if numb == self.current_page:    
#                 # Apply zoom factor to coordinates
#                 unscaled_x1, unscaled_y1 = x1, y1
#                 unscaled_x2, unscaled_y2 = x2, y2
                
#                 # Scale coordinates
#                 x1 = unscaled_x1 * self.zoom_factor
#                 y1 = unscaled_y1 * self.zoom_factor
#                 x2 = unscaled_x2 * self.zoom_factor
#                 y2 = unscaled_y2 * self.zoom_factor
                
#                 # Determine the page dimensions at current zoom level
#                 page_width = self.page_width / self.zoom_factor
#                 page_height = self.page_height / self.zoom_factor
                
#                 # Calculate the four corners of the bounding box
#                 corners = [
#                     (x1, y1),  # Top-left
#                     (x2, y1),  # Top-right
#                     (x2, y2),  # Bottom-right
#                     (x1, y2)   # Bottom-left
#                 ]
                
#                 # Rotate each corner
#                 rotated_corners = []
#                 for corner_x, corner_y in corners:
#                     rx, ry = self.rotate_point(corner_x, corner_y, 
#                                             self.page_width, self.page_height, 
#                                             rotation_angle)
#                     rotated_corners.append((rx, ry))
                
#                 # Find bounding box of rotated corners
#                 rotated_x_coords = [p[0] for p in rotated_corners]
#                 rotated_y_coords = [p[1] for p in rotated_corners]
#                 rotated_x1 = min(rotated_x_coords)
#                 rotated_y1 = min(rotated_y_coords)
#                 rotated_x2 = max(rotated_x_coords)
#                 rotated_y2 = max(rotated_y_coords)
                
#                 # Generate ellipse points
#                 num_points = 72
#                 points = []
                
#                 # Calculate center and radii of the original ellipse
#                 cx = (x1 + x2) / 2
#                 cy = (y1 + y2) / 2
#                 rx = abs(x2 - x1) / 2
#                 ry = abs(y2 - y1) / 2
                
#                 # Generate points around the ellipse and rotate each point
#                 for i in range(num_points):
#                     angle = 2 * math.pi * i / num_points
#                     point_x = cx + rx * math.cos(angle)
#                     point_y = cy + ry * math.sin(angle)
                    
#                     # Rotate this point according to page rotation
#                     rotated_point_x, rotated_point_y = self.rotate_point(
#                         point_x, point_y, 
#                         self.page_width, self.page_height, 
#                         rotation_angle
#                     )
#                     points.extend([rotated_point_x, rotated_point_y])
                
#                 fill = "" if mode == "hollow" else "orange"
#                 self.canvas.create_polygon(
#                     points,
#                     outline="orange", width=3, fill=fill,
#                     smooth=True, tags=("ellipse", "annotation"))


#     # def redraw_all_annotations(self):
#     #     """Redraw all annotations on the current page"""
#     #     self.redraw_lines()
#     #     self.redraw_arrows()
#     #     self.redraw_rectangles()
#     #     self.redraw_ellipses()  # Make sure ellipses are redrawn too

#     # def redraw_ellipses(self):
#     #     """Redraw all ellipse annotations on the current page after zooming or rotating."""
#     #     self.canvas.delete("ellipse")
#     #     if not self.pdf_document:
#     #         return
            
#     #     ellipse_annotations = [ann for ann in self.annotations 
#     #                         if isinstance(ann, tuple) and ann[0] == 'ellipse' 
#     #                         and ann[1] is not None]
                            
#     #     for annotation in ellipse_annotations:
#     #         # Unpack the tuple: (type, x1, y1, x2, y2, id, mode)
#     #         _, x1, y1, x2, y2, _, mode = annotation
            
#     #         # Apply zoom factor to coordinates
#     #         display_x1 = x1 * self.zoom_factor
#     #         display_y1 = y1 * self.zoom_factor
#     #         display_x2 = x2 * self.zoom_factor
#     #         display_y2 = y2 * self.zoom_factor
            
#     #         # Determine if filled based on mode
#     #         fill = "" if mode == "hollow" else "orange"
            
#     #         # Create the ellipse on canvas
#     #         ellipse_id = self.canvas.create_oval(
#     #             display_x1, display_y1, display_x2, display_y2,
#     #             outline="orange", width=3, fill=fill, tags="ellipse")
        
#     # def redraw_lines(self):
#     #     """Redraw all line annotations for the current page"""
#     #     for annotation in self.lines:
#     #         if annotation['page'] == self.current_page:
#     #             # Apply zoom factor to coordinates
#     #             x1 = annotation['x1'] * self.zoom_factor
#     #             y1 = annotation['y1'] * self.zoom_factor
#     #             x2 = annotation['x2'] * self.zoom_factor
#     #             y2 = annotation['y2'] * self.zoom_factor
                
#     #             self.canvas.create_line(
#     #                 x1, y1, x2, y2,
#     #                 fill="red", width=3, tags="annotation")
    
#     # def redraw_arrows(self):
#     #     """Redraw all arrow annotations for the current page"""
#     #     for annotation in self.arrows:
#     #         if annotation['page'] == self.current_page:
#     #             # Apply zoom factor to coordinates
#     #             x1 = annotation['x1'] * self.zoom_factor
#     #             y1 = annotation['y1'] * self.zoom_factor
#     #             x2 = annotation['x2'] * self.zoom_factor
#     #             y2 = annotation['y2'] * self.zoom_factor
                
#     #             self.canvas.create_line(
#     #                 x1, y1, x2, y2,
#     #                 fill="red", width=3, arrow=ctk.LAST, 
#     #                 arrowshape=(16, 20, 6), tags="annotation")
    
#     # def redraw_rectangles(self):
#     #     """Redraw all rectangle annotations for the current page"""
#     #     for annotation in self.rectangles:
#     #         if annotation['page'] == self.current_page:
#     #             # Apply zoom factor to coordinates
#     #             x1 = annotation['x1'] * self.zoom_factor
#     #             y1 = annotation['y1'] * self.zoom_factor
#     #             x2 = annotation['x2'] * self.zoom_factor
#     #             y2 = annotation['y2'] * self.zoom_factor
                
#     #             outline_color = "red"
#     #             fill_color = "" if not annotation['filled'] else "red"
                
#     #             self.canvas.create_rectangle(
#     #                 x1, y1, x2, y2,
#     #                 outline=outline_color, fill=fill_color, 
#     #                 width=3, tags="annotation")

#     def rotate_point(self, x, y, page_width, page_height, rotation_angle):
#         """Rotate a point (x, y) based on the given rotation angle."""
#         if rotation_angle == 90:
#             if is_small_page == "yes":
#                 rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y, x
#             elif is_small_page == "slightly":
#                 rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y, x
#             elif is_small_page == "longer":
#                 print("rhdttjfykfkyf buka buka")
#                 rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y, x
#             elif is_small_page == "maybe":
#                 rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y, x
#             elif is_small_page == "nope large":
#                 rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y, x
#             elif is_small_page == "nope very large":
#                 rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y, x
#             else:
#                 rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y, x
#         elif rotation_angle == 180:
#             rotated_x, rotated_y = page_width - x, page_height - y  
#         elif rotation_angle == 270:
#             if is_small_page == "yes":
#                 rotated_x, rotated_y = y, self.page_width-(180*self.zoom_factor) - x
#             elif is_small_page == "slightly":
#                 rotated_x, rotated_y =y, self.page_width-(1050*self.zoom_factor) - x
#             elif is_small_page == "longer":
#                 rotated_x, rotated_y = y, self.page_width-(720*self.zoom_factor) - x 
#             elif is_small_page == "maybe":
#                 rotated_x, rotated_y = y, self.page_width-(750*self.zoom_factor) - x 
#             elif is_small_page == "nope large":
#                 rotated_x, rotated_y = y, self.page_width-(1000*self.zoom_factor) - x
#             elif is_small_page == "nope very large":
#                 rotated_x, rotated_y = y, self.page_width-(4300*self.zoom_factor) - x
#             else:
#                 rotated_x, rotated_y = y, self.page_width-(2000*self.zoom_factor) - x 
#         else:  # 0 degrees
#             rotated_x, rotated_y = x, y  
#         return rotated_x, rotated_y

#     def redraw_polygons(self):
#         """Redraw all polygons, adjusting for zoom and rotation properly."""
#         if not self.pdf_document or self.current_page is None:
#             return

#         self.canvas.delete("polygon")
#         page = self.pdf_document[self.current_page]
#         rotation_angle = page.rotation  # Get current page rotation

#         if self.current_page not in self.page_drawings:
#             return

#         page_width, page_height = self.page_width, self.page_height  # Get current page dimensions

#         for mode, points, polygon_id in self.page_drawings[self.current_page]:
#             scaled_points = [coord * self.zoom_factor for coord in points]

#             rotated_points = []
#             for i in range(0, len(scaled_points), 2):
#                 x, y = scaled_points[i], scaled_points[i + 1]
#                 new_x, new_y = self.rotate_point(x, y, page_width, page_height, rotation_angle)
#                 rotated_points.extend([new_x, new_y])

#             polygon_id = self.canvas.create_polygon(
#                 rotated_points,
#                 fill="blue" if mode == "filled" else "",
#                 outline="black" if mode == "filled" else "red",
#                 width=4,
#                 tags=("polygon",),
#             )


#     # mouse scroll event for vertical scrolling
#     # def on_mouse_scroll(self, event):
#     #     """Handles vertical scrolling."""
#     #     if self.page_height > self.canvas.winfo_height():  # Scroll only if page is taller
#     #         self.canvas.yview_scroll(-1 * (event.delta // 120), "units")

#     def on_mouse_scroll(self, event):
#         # Get canvas dimensions and page dimensions
#         canvas_width = self.canvas.winfo_width()
#         canvas_height = self.canvas.winfo_height()
#         actual_page_width = self.page_width * self.zoom_factor
#         actual_page_height = self.page_height * self.zoom_factor
#         num_pages = len(self.pdf_document) if self.pdf_document else 0
#         delta = int(-1 * (event.delta / 120))  # Scroll direction adjustment
        
#         # Check if this is the first page and we're trying to scroll up
#         at_first_page = self.current_page == 0
#         scrolling_up = delta < 0
        
#         # Special case: First page, scrolling up, and page smaller than canvas
#         if at_first_page and scrolling_up and actual_page_height <= canvas_height:
#             # Don't do anything - prevent the scroll
#             return
        
#         # Get scroll position
#         top_visible = self.canvas.yview()[0] <= 0.01
#         bottom_visible = self.canvas.yview()[1] >= 0.99
        
#         # Normal scrolling logic for when page is larger than canvas
#         if actual_page_height > canvas_height or (not at_first_page):
#             self.canvas.yview_scroll(delta, "units")
        
#         # Page navigation when reaching bottom/top of current page
#         if bottom_visible and delta > 0:  # Scroll down at bottom
#             if self.current_page < num_pages - 1:
#                 self.current_page += 1
#                 self.render_page(self.current_page)
#                 self.update_thumbnail_selection(self.current_page)
#                 self.update_page_display()
#                 self.canvas.yview_moveto(0.0)
#         elif top_visible and delta < 0:  # Scroll up at top
#             if self.current_page > 0:
#                 self.current_page -= 1
#                 self.render_page(self.current_page)
#                 self.update_thumbnail_selection(self.current_page)
#                 self.update_page_display()
#                 self.canvas.yview_moveto(1.0)

#     def on_shift_mouse_scroll(self, event):
#         """Handles horizontal scrolling when Shift is held."""
#         # Calculate actual page width with zoom factor
#         actual_page_width = self.page_width * self.zoom_factor
#         canvas_width = self.canvas.winfo_width()
        
#         # Only allow horizontal scrolling if the page width exceeds the canvas width
#         # or we're in a multi-page document
#         num_pages = len(self.pdf_document) if self.pdf_document else 0
        
#         if actual_page_width > canvas_width or num_pages > 1:
#             self.canvas.xview_scroll(-1 * (event.delta // 120), "units")

#     def enable_sticky_note_mode(self):
#         """Activate sticky note mode."""
#         self.sticky_note_mode = True
#         self.highlight_mode = False

#         # Unbind previous actions and bind the sticky note click action
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
    

#     def redraw_sticky_notes(self):
#         """Redraw sticky notes after rendering the page and adjust for rotation."""
#         self.canvas.delete("sticky_note")
#         if not self.pdf_document:
#             return
            
#         page = self.pdf_document[self.current_page]
#         rotation_angle = page.rotation  # Get current page rotation

#         for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
#             if page_num == self.current_page:
#                 x_position = x_scaled * self.zoom_factor
#                 y_position = y_scaled * self.zoom_factor

#                 # Get page dimensions at the current zoom level
#                 page_width = page.rect.width * self.zoom_factor
#                 page_height = page.rect.height * self.zoom_factor

#                 # Adjust coordinates based on rotation
#                 if rotation_angle == 90:
#                     if is_small_page == "yes":
#                         rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "slightly":
#                         rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "longer":
#                         rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "maybe":
#                         rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "nope large":
#                         rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "nope very large":
#                         rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
#                     else:
#                         rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position
#                 elif rotation_angle == 180:
#                     rotated_x = page_width - x_position
#                     rotated_y = page_height - y_position
#                 elif rotation_angle == 270:
#                     if is_small_page == "yes":
#                         rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
#                     elif is_small_page == "slightly":
#                         rotated_x, rotated_y =y_position, self.page_width-(1050*self.zoom_factor) - x_position
#                     elif is_small_page == "longer":
#                         rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position
#                     elif is_small_page == "maybe":
#                         rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
#                     elif is_small_page == "nope large":
#                         rotated_x, rotated_y = y_position, self.page_height-(1000*self.zoom_factor)- x_position
#                     elif is_small_page == "nope very large":
#                         rotated_x, rotated_y = y_position, self.page_height-(4300*self.zoom_factor)- x_position
#                     else:
#                         rotated_x, rotated_y = y_position, self.page_height-(2000*self.zoom_factor) - x_position
           
#                 else:  # 0 degrees
#                     rotated_x = x_position
#                     rotated_y = y_position
                    
#                 self.canvas.create_image(
#                     rotated_x, rotated_y,
#                     image=self.icons['thumb_pin'],
#                     anchor="center",
#                     tags="sticky_note"
#                 )
#         self.annotation_is_available = True
#         self.root.update_idletasks()
  
#     def on_canvas_click(self, event):
#         """Add a sticky note at the clicked position on the canvas."""
#         if not self.pdf_document or not self.sticky_note_mode:
#             return

#         x = self.canvas.canvasx(event.x)
#         y = self.canvas.canvasy(event.y)

#         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
#             return

#         note_text = self.ask_for_note_text(x, y,"Add Sticky Note")
#         if not note_text:
#             return

#         x_scaled = x / self.zoom_factor
#         y_scaled = y / self.zoom_factor

#         self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
#         # changes_data = ("sticky_note", self.current_page, x_scaled, y_scaled, note_text)
#         # changes_data = str(changes_data)
#         # sql_check = """
#         #     SELECT COUNT(*) FROM pdf_editor_details 
#         #     WHERE folder_path = %s AND filename = %s AND changes_data = %s
#         # """
#         # mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
#         # result = mycursor.fetchone()
#         # if result[0] == 0:
#         #     sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
#         #     val = (beforeexe,folderpath,changes_data,0)
#         #     mycursor.execute(sql, val)
#         #     mydb.commit()
#         self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
#         print("Sticky note added at:", x_scaled, y_scaled)
#         print("Sticky notes:----",self.change_history)
#         # Safely retrieve the icon for sticky notes
#         self.annotation_is_available = True
#         sticky_icon = self.icons.get("thumb_pin")
#         if sticky_icon:
#             self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
#         else:
#             print("Warning: 'sticky_note' icon not found.")  # Refresh to apply the changes
#         self.annotation_listed.append("sticky_note")

#     def ask_for_note_text(self, x, y,title):
#         """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
#         dialog = ctk.CTkToplevel(self.root)
#         dialog.title(title)
#         dialog.geometry("400x250")
#         dialog.resizable(False, False)

#         label = ctk.CTkLabel(
#             dialog, text="Enter your note:", font=ctk.CTkFont(size=14, weight="bold")
#         )
#         label.pack(pady=(15, 10))

#         text_box = ctk.CTkTextbox(dialog, wrap="word", height=100, width=360)
#         text_box.pack(padx=15, pady=5, fill="x")
#         text_box.focus_set()

#         note_text_var = ctk.StringVar()

#         # Button functionality
#         def on_ok_click():
#             note_text = text_box.get("1.0", "end").strip()
#             if note_text:
#                 note_text_var.set(note_text)
#                 dialog.destroy()
#             else:
#                 messagebox.showerror("Empty Note", "You must enter some text to save the sticky note.",parent=self.root)

#         # Create buttons
#         buttons_frame = ctk.CTkFrame(dialog)
#         buttons_frame.pack(side="bottom", pady=15)

#         ok_button = ctk.CTkButton(
#             buttons_frame, text="Apply", command=on_ok_click, fg_color="#00498f", text_color="white"
#         )
#         ok_button.pack(side="left", padx=10)

#         cancel_button = ctk.CTkButton(
#             buttons_frame, text="Cancel", command=dialog.destroy, fg_color="#6c757d", text_color="white"
#         )
#         cancel_button.pack(side="left", padx=10)

#         dialog.grab_set()
#         dialog.wait_window()

#         self.sticky_note_mode = False
#         self.add_text_mode = False
#         self.add_text_bg_mode = False
#         return note_text_var.get() or None

#     def undo_change(self):
#         print("Undoing the last change...",self.change_history)
#         if not self.change_history:
#             return

#         last_action = self.change_history.pop()
#         action_type = last_action[0]
        
#         if action_type == "highlight":
#             _, page, annot_id = last_action
#             page_obj = self.pdf_document[page]
#             annot = page_obj.first_annot
#             while annot:
#                 if annot.info.get('id') == annot_id:
#                     page_obj.delete_annot(annot)
#                     self.render_page(self.current_page)
#                     break
#                 annot = annot.next
#             if self.annotation_listed[-1]=="highlight":
#                 self.annotation_listed.pop()
        
#         elif action_type == "freehand":
#             _, page, line_id, _ = last_action
#             # Remove from the canvas
#             self.canvas.delete(line_id)
#             # Remove from history
#             self.change_history = [entry for entry in self.change_history if entry[2] != line_id]
#             # Redraw remaining freehand drawings to refresh the canvas
#             self.redraw_freehand_drawings()
#             self.render_page(self.current_page)
#             if self.annotation_listed[-1]=="freehand":
#                 self.annotation_listed.pop()
        
#         elif action_type == "add_annotation":
#             # New code for undoing line, arrow, rectangle, and ellipse annotations
#             annotation_data = last_action[1]
#             annotation_type = annotation_data.get('type')
            
#             # Remove from canvas
#             if 'id' in annotation_data:
#                 self.canvas.delete(annotation_data['id'])
            
#             # Remove from appropriate list
#             if annotation_type == 'line':
#                 self.lines = [line for line in self.lines if line != annotation_data]
#                 if self.annotation_listed[-1]=="line":
#                     self.annotation_listed.pop()
#             elif annotation_type == 'arrow':
#                 self.arrows = [arrow for arrow in self.arrows if arrow != annotation_data]
#                 if self.annotation_listed[-1]=="arrow":
#                     self.annotation_listed.pop()
#             elif annotation_type == 'rectangle':
#                 self.rectangles = [rect for rect in self.rectangles if rect != annotation_data]
#                 if self.annotation_listed[-1]=="rectangle":
#                     self.annotation_listed.pop()
#             # Remove from annotations list
#             self.annotations = [ann for ann in self.annotations 
#                             if not (isinstance(ann, dict) and ann.get('id') == annotation_data.get('id'))]
#             self.render_page(self.current_page)

#         elif action_type == "ellipse":
#             # Handle ellipse annotations
#             _, x1, y1, x2, y2, ellipse_id, mode = last_action
#             if ellipse_id:
#                 self.canvas.delete(ellipse_id)
#             # Remove from annotations list
#             ellipse_to_remove = None
#             for ann in self.annotations:
#                 if isinstance(ann, tuple) and ann[0] == 'ellipse' and ann[1] == x1 and ann[2] == y1 and ann[3] == x2 and ann[4] == y2:
#                     ellipse_to_remove = ann
#                     break
#             if ellipse_to_remove:
#                 self.annotations.remove(ellipse_to_remove)
#             if self.annotation_listed[-1]=="ellipse":
#                 self.annotation_listed.pop()
#             self.render_page(self.current_page)

#         elif action_type in ("add_text", "add_text_bg"):
#             _, page, x_scaled, y_scaled, text = last_action
#             annotation_dict = self.text_annotations if action_type == "add_text" else self.text_annotations_bg
#             if (page, x_scaled, y_scaled) in annotation_dict:
#                 del annotation_dict[(page, x_scaled, y_scaled)]
#                 page_obj = self.pdf_document[page]
#                 annot = page_obj.first_annot
#                 while annot:
#                     if annot.info and annot.info.get("contents") == text:
#                         page_obj.delete_annot(annot)
#                         break
#                     annot = annot.next
#                 self.render_page(self.current_page)
#             if self.annotation_listed[-1]=="text_bg":
#                 self.annotation_listed.pop()
#             elif self.annotation_listed[-1]=="text":
#                 self.annotation_listed.pop()

#         elif action_type == "polygon":
#             _, page, prev_state, polygon_id = last_action
#             if page in self.page_drawings:
#                 for i, (mode, points, pid) in enumerate(self.page_drawings[page]):
#                     if pid == polygon_id:
#                         if prev_state is None:
#                             # Undo polygon creation (remove it)
#                             self.canvas.delete(polygon_id)
#                             del self.page_drawings[page][i]
#                         else:
#                             # Restore previous state (undo move/reshape)
#                             self.page_drawings[page][i] = (mode, prev_state, polygon_id)
#                             self.canvas.coords(polygon_id, prev_state)
#                         break
#                 self.render_page(self.current_page)
#             if self.annotation_listed[-1]=="polygon":
#                 self.annotation_listed.pop()

#         elif action_type == "sticky_note":
#             _, page, x_scaled, y_scaled, _ = last_action
#             if (page, x_scaled, y_scaled) in self.sticky_notes:
#                 del self.sticky_notes[(page, x_scaled, y_scaled)]
#                 if self.annotation_listed[-1]=="sticky_note":
#                     self.annotation_listed.pop()
#                 self.render_page(self.current_page)

#         elif action_type == "image_overlay":
#             _, page, overlay_info = last_action
#             # Remove from image_overlays list
#             if hasattr(self, "image_overlays"):
#                 self.image_overlays = [overlay for overlay in self.image_overlays 
#                                     if overlay["id"] != overlay_info["id"]]
            
#             # Delete the image from canvas if it exists
#             if "canvas_id" in overlay_info:
#                 self.canvas.delete(overlay_info["canvas_id"])
            
#             # Remove from tk_images dictionary to free memory
#             if hasattr(self, "tk_images") and overlay_info["id"] in self.tk_images:
#                 del self.tk_images[overlay_info["id"]]
            
#             if self.annotation_listed[-1]=="image_overlay":
#                 self.annotation_listed.pop()
            
#             # Only re-render if we're on the same page
#             if page == self.current_page:
#                 self.render_page(self.current_page)

#         else:
#             print(f"Unknown action type: {action_type}")


#     def enable_highlight_mode(self):
#         """ Activate highlight mode """
#         self.deactivate_tools()
#         self.highlight_mode = True
#         self.is_drawing_hollow_rect = False
#         self.is_drawing_filled_rect = False
#         self.canvas.bind("<Button-1>", self.start_highlight_rectangle)
#         self.canvas.bind("<B1-Motion>", self.draw_highlight_rectangle)
#         self.canvas.bind("<ButtonRelease-1>", self.finalize_highlight)

#     def start_highlight_rectangle(self, event):
#         """Start a rectangle selection for highlighting"""
#         self.start_x = self.canvas.canvasx(event.x)
#         self.start_y = self.canvas.canvasy(event.y)
        
#         # Delete any existing highlight preview
#         if self.rectangle_id:
#             self.canvas.delete(self.rectangle_id)
        
#         # Draw the initial rectangle immediately
#         self.rectangle_id = self.canvas.create_rectangle(
#             self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
#             outline="yellow", width=2)

#     def draw_highlight_rectangle(self, event):
#         """Draw the rectangle dynamically as the mouse is dragged."""
#         if self.rectangle_id is None:
#             return  # Prevents calling coords on None
        
#         current_x = self.canvas.canvasx(event.x)
#         current_y = self.canvas.canvasy(event.y)
#         # Update rectangle coordinates safely
#         self.canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)


#     def finalize_highlight(self, event):
#         """Finalize the highlight and save it to the PDF."""
#         if self.start_x is None or self.start_y is None:
#             return
#         end_x = self.canvas.canvasx(event.x) / self.zoom_factor
#         end_y = self.canvas.canvasy(event.y) / self.zoom_factor
#         start_x = self.start_x / self.zoom_factor
#         start_y = self.start_y / self.zoom_factor
#         rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
#         page = self.pdf_document[self.current_page]
#         rotation = page.rotation
#         page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor
#         if rotation == 90:
#             rect = fitz.Rect(
#                 rect.y0,
#                 page_width - rect.x1,
#                 rect.y1,
#                 page_width - rect.x0)
#         elif rotation == 180:
#             rect = fitz.Rect(
#                 page_width - rect.x1,
#                 page_height - rect.y1,
#                 page_width - rect.x0,
#                 page_height - rect.y0)
#         elif rotation == 270:
#             rect = fitz.Rect(
#                 page_height - rect.y1,
#                 rect.x0,
#                 page_height - rect.y0,
#                 rect.x1)
#         try:
#             highlight = page.add_highlight_annot(rect)
#             highlight.update()
#             highlight.set_border(width=0, dashes=(0, 0))
#             annot_id = highlight.info.get('id')
#             # changes_data = ("highlight", self.current_page, annot_id)
#             # changes_data = str(changes_data)
#             # if annot_id:
#             #     sql_check = """
#             #         SELECT COUNT(*) FROM pdf_editor_details 
#             #         WHERE folder_path = %s AND filename = %s AND changes_data = %s
#             #     """
#             #     mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
#             #     result = mycursor.fetchone()
#             #     if result[0] == 0:
#             #         print(f"Added highlight with ID: {annot_id}")
#             #         print("beforeexe----",beforeexe)
#             #         sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
#             #         val = (beforeexe,folderpath,changes_data,0)
#             #         mycursor.execute(sql, val)
#             #         mydb.commit()
#             if annot_id:
#                 self.change_history.append(("highlight", self.current_page, annot_id))
#                 print("highlight added",self.change_history)
#                 self.annotation_is_available = True
#                 self.annotation_listed.append("highlight")
#         except Exception as e:
#             messagebox.showerror("Error", f"Failed to add highlight: please drag the area you want to highlight",parent=self.root)
#             return    
#         self.render_page(self.current_page)
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")
#         self.deactivate_tools()

#     def on_mouse_hover(self, event):
#         """Change cursor when hovering over a polygon or sticky note."""
#         if not self.pdf_document or self.current_page is None:
#             return
#         x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
#         tooltip_shown = False
#         page = self.pdf_document[self.current_page]
#         rotation_angle = page.rotation

#         # Adjust the coordinates for zoom
#         adjusted_x, adjusted_y = x / self.zoom_factor, y / self.zoom_factor

#         for drawing in self.page_drawings.get(self.current_page, []):
#             if isinstance(drawing, tuple) and len(drawing) == 3:  # Polygon (id, points, color)
#                 _, points, _ = drawing

#                 # Adjust the polygon coordinates for zoom
#                 zoomed_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in zip(points[::2], points[1::2])]

#                 if self.is_point_inside_polygon(x, y, sum(zoomed_points, ())):  # Flatten the list
#                     self.canvas.config(cursor="hand2")
#                     return  # Exit function early if hovering over a polygon

#         # Sticky note cursor handling
#         for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
#             if page_num == self.current_page:
#                 x_position = x_scaled * self.zoom_factor
#                 y_position = y_scaled * self.zoom_factor
#                 page_width = page.rect.width * self.zoom_factor
#                 page_height = page.rect.height * self.zoom_factor

#                 # Handle rotation
#                 if rotation_angle == 90:
#                     rotated_x, rotated_y = self.page_height + (180 * self.zoom_factor) - y_position, x_position
#                 elif rotation_angle == 180:
#                     rotated_x = page_width - x_position
#                     rotated_y = page_height - y_position
#                 elif rotation_angle == 270:
#                     rotated_x, rotated_y = y_position, self.page_width - (180 * self.zoom_factor) - x_position
#                 else:  # 0 degrees
#                     rotated_x = x_position
#                     rotated_y = y_position

#                 if abs(x - rotated_x) < 20 and abs(y - rotated_y) < 20:  # Adjust hover sensitivity
#                     if not tooltip_shown:
#                         self.show_tooltip(event.x_root, event.y_root, text)
#                         tooltip_shown = True
#                     break

#         if not tooltip_shown:
#             if self.active_tooltip:
#                 self.active_tooltip.destroy()
#                 self.active_tooltip = None
#             self.canvas.config(cursor="arrow")  # Ensure cursor resets correctly


#     def show_tooltip(self, x, y, text):
#         """Display the sticky note text as a tooltip."""
#         if getattr(self, "active_tooltip", None):
#             self.active_tooltip.destroy()
#         wraptext = textwrap.fill(text, width=50)  # Ensuring the line ends at 50 characters
#         today = date.today().strftime("%m-%d-%Y")
#         wrapped_text = f"{today}\n\n{wraptext}"
#         tooltip = ctk.CTkToplevel(self.root)
#         tooltip.overrideredirect(True)
#         tooltip.geometry(f"+{int(x) + 10}+{int(y) + 10}")  # Ensure integer coordinates
#         label = ctk.CTkLabel(
#             tooltip, text=wrapped_text, bg_color="light yellow", text_color="black", padx=10, pady=5
#         )
#         label.pack()
#         if getattr(self, "active_tooltip", None):
#             self.active_tooltip.destroy()
#         self.active_tooltip = tooltip

#     def toggle_sticky_note_mode(self):
#         """Toggle sticky note mode"""
#         if self.sticky_note_mode:
#             self.sticky_note_mode = False
#             self.canvas.unbind("<Button-1>")
#         else:
#             self.enable_sticky_note_mode()

# # -----------------------------------------------------------------------------------------------------------

#     def save_pdf(self, file_path=None):
#         """Save the PDF with embedded sticky notes and upload directly to the server."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF document to save.")
#             return
#         global edit_file_name
#         global folderpath
#         print("self.annotation_listed",self.annotation_listed)
#         print ("folderpath name ======== ",folderpath)
#         print("edit_file_name-----------------",edit_file_name)
#         print("filename_pdf-----------------",filename_pdf)
#         if "redact_with_annotations" in folderpath:
#             folderpath = folderpath.replace("_redact_with_annotations.pdf", ".pdf")
#         elif "_redact" in folderpath:
#             folderpath = folderpath.replace("_redact.pdf", ".pdf")
#         elif "_with_annotation" in folderpath:
#             folderpath = folderpath.replace("_with_annotations.pdf", ".pdf")
#         print ("folderpath name ======== ",folderpath)
#         print("Serverurl--------------------------------------------------------------------------------------------------",self.server_url)
#         try:
#             temp_pdf = fitz.open()
#             for page_num in range(len(self.pdf_document)):
#                 page = self.pdf_document[page_num]
#                 temp_pdf.insert_pdf(self.pdf_document, from_page=page_num, to_page=page_num)

#             for page_num in self.page_drawings:
#                 if page_num < len(temp_pdf):
#                     page = temp_pdf[page_num]
#                     # Manually embed polygons without changing current_page
#                     self._embed_polygons_to_page(page, page_num)
            
#             for annotation in self.annotations:
#                 if isinstance(annotation, tuple) and annotation[0] == 'ellipse' and annotation[1] is not None:
#                     _, x1, y1, x2, y2, _, mode,numb = annotation
#                     page_num = numb
#                     page = temp_pdf[page_num]
#                     self.add_ellipse_annotation(page, x1, y1, x2, y2, mode)
            
#             if hasattr(self, "image_overlays"):
#                 for overlay in self.image_overlays:
#                     page_num = overlay["page"]
#                     if page_num < len(temp_pdf):
#                         page = temp_pdf[page_num]
#                         self.add_image_overlay_to_pdf(page, overlay)
#             print("terethetttehht reached here .........................")
#             try:
#                 for rect in self.rectangles:
#                     if rect['type'] == 'rectangle' and rect['page'] < len(temp_pdf):
#                         page = temp_pdf[rect['page']]
                        
#                         # Create a rectangle using the page's draw methods instead of annotations
#                         rect_coords = fitz.Rect(rect['x1'], rect['y1'], rect['x2'], rect['y2'])
                        
#                         # Set color based on string color (convert to RGB tuple)
#                         if rect['color'] == "red":
#                             rgb_color = (1, 0, 0)  # Red in RGB (0-1 range)
#                         else:
#                             rgb_color = (0, 0, 0)  # Default to black
                        
#                         # Draw rectangle on the page
#                         if rect['filled']:
#                             # For filled rectangle
#                             page.draw_rect(rect_coords, color=rgb_color, fill=rgb_color, width=4)
#                         else:
#                             # For hollow rectangle
#                             page.draw_rect(rect_coords, color=rgb_color, fill=None, width=6)


#                 # Add line annotations
#                 for line in self.lines:
#                     if line['type'] == 'line' and line['page'] < len(temp_pdf):
#                         page = temp_pdf[line['page']]
#                         # Create a line using PyMuPDF
#                         start_point = fitz.Point(line['x1'], line['y1'])
#                         end_point = fitz.Point(line['x2'], line['y2'])
#                         rgb_color = (1, 0, 0)  # Red in RGB (0-1 range)
#                         page.draw_line(start_point, end_point, color=rgb_color, width=6)
                        
#                 # Add arrow annotations
#                 for arrow in self.arrows:
#                     if arrow['page'] < len(temp_pdf):
#                         page = temp_pdf[arrow['page']]
#                         start_point = fitz.Point(arrow['x1'], arrow['y1'])
#                         end_point = fitz.Point(arrow['x2'], arrow['y2'])
                        
#                         # Create the arrow annotation
#                         annot = page.add_line_annot(start_point, end_point)
#                         annot.set_colors(stroke=(1, 0, 0))  # Red color
#                         ## Line end styles: 0=None, 1=Square, 2=Circle, 3=Diamond, 4=OpenArrow, 5=ClosedArrow, 6=Butt, 7=ROpenArrow, 8=RClosedArrow
#                         annot.set_line_ends(0, 5)  # First value is start style, second is end style (2 = arrow)
#                         annot.set_border(width=6)
#                         annot.update()

#             except Exception as e:
#                 print(f"Error adding rectangle annotations: {str(e)}")
#             for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
#                 page = temp_pdf[page_num]
#                 self.add_text_sticky_annotation(page, x_scaled, y_scaled, text)
#             for (page_num, x_scaled, y_scaled), annotation_data in self.text_annotations.items():
#                 page = temp_pdf[page_num]           
#                 if isinstance(annotation_data, dict):
#                     text = annotation_data["text"]
#                 else:
#                     text = annotation_data
#                 self.add_plain_text_annotation(page, x_scaled, y_scaled, text)
#             for (page_num, x_scaled, y_scaled), text in self.text_annotations_bg.items():
#                 page = temp_pdf[page_num]
#                 self.add_text_with_bg_annotation(page, x_scaled, y_scaled, text)
#             print("before freehand")
#             # Add freehand drawings to the PDF
#             for item in self.change_history:
#                 if item[0] == "freehand":
#                     _, page_num, _, points = item
#                     page = temp_pdf[page_num]
#                     self.add_freehand_line_annotation(page, points)
#             pdf_buffer = io.BytesIO()
#             temp_pdf.save(pdf_buffer, garbage=4, deflate=True, deflate_images=True, clean=True)
#             pdf_buffer.seek(0)
#             print("before save function-----------------")

#             if len(self.change_redact_history) > 0 or len(self.redactions) > 0:           
#                 if "_redact.pdf" in filename_pdf: 
#                     print("____________________redact.pdf")
#                     if len(self.annotation_listed)==0:   
#                         edit_file_name = edit_file_name
#                         print("redact_file_name--*****-",edit_file_name)
#                         files = {'folder_path': (None, folderpath),
#                                 'redact': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                             print("File saved successfully  _redact.pdf")
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return         
#                     elif len(self.annotation_listed)>0:
#                         edit_file_name = edit_file_name.replace(".pdf", "_with_annotations.pdf")
#                         print("yes redact and annotation")
#                         files = {'folder_path': (None, folderpath),
#                                 'redact_with_annotations': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                             print("File saved successfully  _redact.pdf_with_annotations")
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return
#                 if "_redact_with_annotations.pdf" in edit_file_name:
#                     edit_file_name = edit_file_name
#                     print("yes redact and annotation")
#                     files = {'folder_path': (None, folderpath),
#                             'redact_with_annotations': (edit_file_name, pdf_buffer, 'application/pdf')}
#                     response = requests.post(self.server_url, files=files)
#                     if response.status_code in [200, 201]:
#                         messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                         print("File saved successfully  _redact.pdf_with_annotations")
#                     else:
#                         messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                         return
#                 elif "_with_annotations.pdf" in edit_file_name:
#                     edit_file_name = edit_file_name.replace("_with_annotations.pdf", "_redact_with_annotations.pdf")
#                     print("yes annotation ")
#                     files = {'folder_path': (None, folderpath),
#                             'redact_with_annotations': (edit_file_name, pdf_buffer, 'application/pdf')}
#                     response = requests.post(self.server_url, files=files)
#                     if response.status_code in [200, 201]:
#                         messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                         print("File saved successfully  _redact.pdf_with_annotations")
#                     else:
#                         messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                         return
#                 else:
#                     if len(self.annotation_listed)==0:
#                         edit_file_name = edit_file_name.replace(".pdf", "_redact.pdf")
#                         print("yes annotation ")
#                         files = {'folder_path': (None, folderpath),
#                                 'redact': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                             print("File saved successfully  _redact.pdf_with_annotations")
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return
#                     elif len(self.annotation_listed)>0:
#                         edit_file_name = edit_file_name.replace(".pdf", "_redact_with_annotations.pdf")
#                         print("yes annotation ")
#                         files = {'folder_path': (None, folderpath),
#                                 'redact_with_annotations': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                             print("File saved successfully  _redact.pdf_with_annotations")
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return
#             elif len(self.redactions) == 0:
#                 print("no redactions svsvsfbbfxxfsdvxfsdfxfxf    elifff")
#                 if len(self.annotation_listed)>0:
#                     if "_redact.pdf" in filename_pdf:
#                         edit_file_name = edit_file_name.replace(".pdf", "_with_annotations.pdf")
#                         files = {'folder_path': (None, folderpath),
#                                 'redact_with_annotations': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return
#                     elif "redact_with_annotations.pdf" in edit_file_name:
#                         edit_file_name = edit_file_name
#                         files = {'folder_path': (None, folderpath),
#                                 'redact_with_annotations': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return
#                     elif "with_annotations.pdf" in edit_file_name:
#                         edit_file_name = edit_file_name
#                         files = {'folder_path': (None, folderpath),
#                                 'file': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return
#                     else:
#                         edit_file_name = edit_file_name.replace(".pdf", "_with_annotations.pdf")
#                         print("edit_file_name------- else part---------",edit_file_name)
#                         files = {'folder_path': (None, folderpath),
#                                 'file': (edit_file_name, pdf_buffer, 'application/pdf')}
#                         response = requests.post(self.server_url, files=files)
#                         if response.status_code in [200, 201]:
#                             messagebox.showinfo("Success", "File saved successfully",parent=self.root)
#                         else:
#                             messagebox.showerror("Error", "Failed to save the file.",parent=self.root)
#                             return                
#                 else:
#                     messagebox.showinfo("Info", "No Annotation made to save the file.",parent=self.root)
#         except:
#             print(f"Failed to save PDF")

#     def add_ellipse_annotation(self, page, x1, y1, x2, y2, mode):
#         """Add ellipse annotation to the PDF page."""
#         try:
#             # Create a new shape on the page
#             shape = page.new_shape()
            
#             # Calculate center and radii of the ellipse
#             cx = (x1 + x2) / 2
#             cy = (y1 + y2) / 2
#             rx = abs(x2 - x1) / 2
#             ry = abs(y2 - y1) / 2
            
#             # Draw the ellipse
#             shape.draw_oval(fitz.Rect(x1, y1, x2, y2))
            
#             # Set fill and stroke properties
#             fill_color = None
#             if mode == "filled":
#                 fill_color = (1, 0.5, 0)  # Orange color
            
#             # Finish the shape with or without fill
#             shape.finish(color=(1, 0.5, 0), fill=fill_color, width=6)
            
#             # Commit the shape to the page
#             shape.commit(overlay=True)
#         except Exception as e:
#             print(f"Error adding ellipse annotation: {e}")

#     def add_image_overlay_to_pdf(self, page, overlay):
#         """Add image overlay to the PDF page."""
#         try:
#             # Extract overlay properties
#             base_x = overlay["base_x"]
#             base_y = overlay["base_y"]
#             base_width = overlay["base_width"]
#             base_height = overlay["base_height"]
#             image_path = overlay["image_path"]
            
#             # Create a rectangle for the image placement
#             rect = fitz.Rect(base_x, base_y, base_x + base_width, base_y + base_height)
            
#             # Check if the image file exists and is readable
#             if os.path.isfile(image_path):
#                 try:
#                     # Insert the image onto the page
#                     page.insert_image(rect, filename=image_path)
#                 except Exception as img_error:
#                     print(f"Error inserting image into PDF: {img_error}")
#             else:
#                 print(f"Image file not found: {image_path}")
#         except Exception as e:
#             print(f"Error adding image overlay: {e}")

#     def _embed_polygons_to_page(self, page, page_num):
#         """Helper function to embed polygons to a specific page without changing self.current_page."""
#         try:
#             if page_num not in self.page_drawings:
#                 return
                
#             # Delete existing polygon annotations if any
#             for annot in page.annots():
#                 if annot.info.get("title") == "polygon_annotation":
#                     annot.delete()
                    
#             for drawing in self.page_drawings[page_num]:
#                 if len(drawing) != 3:
#                     continue
                    
#                 mode, points, polygon_id = drawing
                
#                 # Skip if this polygon should be ignored
#                 if hasattr(self, 'embedded_polygons') and page_num in self.embedded_polygons:
#                     if any(p[2] == polygon_id for p in self.embedded_polygons[page_num]):
#                         continue
                        
#                 # Convert points to pairs of coordinates
#                 scaled_points = [(points[i], points[i + 1]) for i in range(0, len(points), 2)]
                
#                 path = page.new_shape()
#                 # Draw lines between points to form the polygon
#                 for i in range(len(scaled_points)):
#                     p1 = scaled_points[i]
#                     p2 = scaled_points[(i + 1) % len(scaled_points)]
#                     path.draw_line(p1, p2)
                    
#                 # Set fill or outline based on mode
#                 if mode == "filled":
#                     path.finish(fill=(0, 0, 1), color=(0, 0, 0))
#                 elif mode == "hollow":
#                     path.finish(color=(1, 0, 0), fill=None, width=6)
                    
#                 # Commit the shape to the page
#                 path.commit(overlay=True)
                
#                 # Track that we've embedded this polygon
#                 if not hasattr(self, 'embedded_polygons'):
#                     self.embedded_polygons = {}
#                 if page_num not in self.embedded_polygons:
#                     self.embedded_polygons[page_num] = []
#                 self.embedded_polygons[page_num].append(drawing)
                
#         except Exception as e:
#             print(f"Error embedding polygons to page {page_num}: {e}")

#     def add_text_sticky_annotation(self, page, x_scaled, y_scaled, text):
#         """Helper function to add text annotations properly."""
#         today = date.today().strftime("%m-%d-%Y")
#         base_text_size = 20  
#         scaling_factor = max(page.rect.width, page.rect.height) / 1000  
#         text_size = int(base_text_size * scaling_factor)
#         marker_size = int(12 * scaling_factor)
#         text_offset = int(15 * scaling_factor)
#         padding = int(10 * scaling_factor)
#         vertical_padding = int(15 * scaling_factor)
        
#         marker_color = (1, 0, 0)
#         page.draw_circle(center=(x_scaled, y_scaled), radius=marker_size / 2, color=marker_color, fill=marker_color)
        
#         lines = self.wrap_text(f"{today}\n{text}", 50)
#         max_text_width = max(len(line) for line in lines) * text_size * 0.6
#         max_text_height = len(lines) * text_size * 1.5
#         background_width = max_text_width + padding * 2
#         background_height = max_text_height + vertical_padding * 2.5
        
#         page.draw_rect(
#             rect=(x_scaled, y_scaled + text_offset - vertical_padding, 
#                   x_scaled + background_width, y_scaled + text_offset + background_height),
#             color=(1, 1, 0), overlay=True, fill_opacity=0.9, fill=(1, 1, 0)
#         )
        
#         text_x = x_scaled + padding
#         text_y = y_scaled + text_offset
#         for i, line in enumerate(lines):
#             page.insert_text(point=(text_x, text_y + (i * text_size * 1.5)), text=line, fontsize=text_size, color=(0, 0, 0))

#     def add_freehand_line_annotation(self, page, points):
#         """Add freehand line drawing to the PDF page."""
#         if not points or len(points) < 2:
#             return     
#         # Set line properties
#         stroke_color = (0, 0, 0)  # Black color    
#         # Calculate scaling factor for line width based on page size
#         scaling_factor = max(page.rect.width, page.rect.height) / 1000
#         line_width = 2 * scaling_factor  # Adjust line width based on page size      
#         # Convert the points to a continuous line
#         page.draw_polyline(points, color=stroke_color, width=line_width)

#     def add_plain_text_annotation(self, page, x_scaled, y_scaled, text):
#         """Add plain text annotation to the PDF page."""
#         try:
#             text_size = 18  # Default text size
#             scaling_factor = max(page.rect.width, page.rect.height) / 1000
#             adjusted_text_size = int(text_size * scaling_factor)
            
#             # Ensure text stays within page boundaries
#             max_width = page.rect.width - x_scaled - 20  # 20-unit buffer from edge
            
#             # Convert text to properly wrapped text if needed
#             wrapped_text = self.wrap_text_for_saving(text, max_width, adjusted_text_size)
            
#             # Add the text to the PDF
#             page.insert_text(
#                 point=(x_scaled, y_scaled),
#                 text=wrapped_text,
#                 fontsize=adjusted_text_size,
#                 color=(0, 0, 0)  # Black color
#             )
#         except Exception as e:
#             print(f"Error adding text annotation: {e}")

#     def wrap_text_for_saving(self, text, max_width, font_size):
#         """Ensure text is properly wrapped before saving to PDF."""
#         # PyMuPDF doesn't automatically wrap text, so we need to do it manually
#         # Approximate character width based on font size
#         char_width = font_size * 0.5  # Rough estimate
        
#         # Calculate max chars per line
#         max_chars = int(max_width / char_width * 0.9)  # 10% safety margin
#         max_chars = max(min(max_chars, 80), 5)  # Reasonable bounds
        
#         # If text already contains newlines, respect them
#         if '\n' in text:
#             lines = text.split('\n')
#             wrapped_lines = []
#             for line in lines:
#                 if len(line) <= max_chars:
#                     wrapped_lines.append(line)
#                 else:
#                     # Wrap this line
#                     words = line.split()
#                     current_line = []
#                     current_length = 0
                    
#                     for word in words:
#                         word_len = len(word)
#                         space_len = 1 if current_length > 0 else 0
                        
#                         if current_length + word_len + space_len > max_chars:
#                             if current_line:  # Add current line if it exists
#                                 wrapped_lines.append(' '.join(current_line))
#                             current_line = [word]
#                             current_length = word_len
#                         else:
#                             current_line.append(word)
#                             current_length += word_len + space_len
                    
#                     if current_line:  # Add the last line
#                         wrapped_lines.append(' '.join(current_line))
            
#             return '\n'.join(wrapped_lines)
#         else:
#             # Wrap text that doesn't already have newlines
#             words = text.split()
#             lines = []
#             current_line = []
#             current_length = 0
            
#             for word in words:
#                 word_len = len(word)
#                 space_len = 1 if current_length > 0 else 0
                
#                 if current_length + word_len + space_len > max_chars:
#                     if current_line:  # Add current line if it exists
#                         lines.append(' '.join(current_line))
#                     current_line = [word]
#                     current_length = word_len
#                 else:
#                     current_line.append(word)
#                     current_length += word_len + space_len
            
#             if current_line:  # Add the last line
#                 lines.append(' '.join(current_line))
            
#             return '\n'.join(lines)

#     def add_text_with_bg_annotation(self, page, x_scaled, y_scaled, text):
#         """Add text with background annotation to the PDF page."""
#         text_size = 18 # Default text size
#         scaling_factor = max(page.rect.width, page.rect.height) / 1000
#         adjusted_text_size = int(text_size * scaling_factor)
#         padding = int(15 * scaling_factor)
        
#         # Calculate text dimensions for background
#         lines = text.split('\n')
#         max_width = max(len(line) for line in lines) * adjusted_text_size * 0.6
#         text_height = len(lines) * adjusted_text_size * 1.2
        
#         # Draw background rectangle
#         page.draw_rect(
#             rect=(x_scaled - padding, y_scaled - padding, 
#                 x_scaled + max_width + padding, y_scaled + text_height + padding),
#             color=(0, 1, 1),  # Cyan color
#             fill=(0, 1, 1),
#             fill_opacity=0.9
#         )   
#         # Insert text on top of background
#         for i, line in enumerate(lines):
#             page.insert_text(
#                 point=(x_scaled, y_scaled + (i * adjusted_text_size * 1.2)),
#                 text=line,
#                 fontsize=adjusted_text_size,
#                 color=(0, 0, 0)  # Black color
#             )
            
#     def wrap_text(self, text, max_line_length):
#         """Wrap the text into lines with a maximum number of characters per line."""
#         words = text.split(" ")
#         lines = []
#         current_line = ""
#         for word in words:
#             if len(current_line) + len(word) + 1 <= max_line_length:
#                 current_line += (word + " ")
#             else:
#                 lines.append(current_line.strip())
#                 current_line = word + " "
#         if current_line:
#             lines.append(current_line.strip())
#         return lines
    
#     def update_page_display(self):
#         if self.pdf_document:
#             total_pages = len(self.pdf_document)
#             self.page_entry.delete(0, ctk.END)
#             self.page_entry.insert(0, str(self.current_page + 1))  # One-based index
#             self.page_total_label.configure(text=f"/ {total_pages}")
    
#     def prev_page(self, event=None):
#         """Go to the previous page in the PDF."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         if self.current_page > 0:
#             self.current_page -= 1
#             self.render_page(self.current_page)
#             self.update_thumbnail_selection(self.current_page)
#             self.update_page_display()

#     def next_page(self, event=None):
#         """Go to the next page in the PDF."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         if self.current_page < len(self.pdf_document) - 1:
#             self.current_page += 1
#             self.render_page(self.current_page)
#             self.update_thumbnail_selection(self.current_page)
#             self.update_page_display()


#     def rotate_90clockwise(self):
#         """Rotate the current page clockwise."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         page = self.pdf_document[self.current_page]
#         page.set_rotation((page.rotation + 90) % 360)
#         self.render_page(self.current_page)

#     def rotate_180clockwise(self):
#         """Rotate the current page clockwise."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         page = self.pdf_document[self.current_page]
#         page.set_rotation((page.rotation + 180) % 360)
#         self.render_page(self.current_page)

#     def rotate_270clockwise(self):
#         """Rotate the current page clockwise."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         page = self.pdf_document[self.current_page]
#         page.set_rotation((page.rotation + 270) % 360)
#         self.render_page(self.current_page)

#     def toggle_invert_colors(self):
#         """Toggle color inversion for the PDF."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.is_inverted = not self.is_inverted
#         self.render_page(self.current_page)
#         self.redraw_sticky_notes()


#     def zoom_in_area(self, event):
#         """Zoom into a specific area of the canvas based on mouse click."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return

#         # Get the canvas click position adjusted for scrolling
#         canvas_x = self.canvas.canvasx(event.x) / self.zoom_factor
#         canvas_y = self.canvas.canvasy(event.y) / self.zoom_factor

#         # Define the zoom area dimensions
#         zoom_area_size = 150
#         left = max(0, canvas_x - zoom_area_size // 2)
#         top = max(0, canvas_y - zoom_area_size // 2)
#         right = min(self.page_width, canvas_x + zoom_area_size // 1)
#         bottom = min(self.page_height, canvas_y + zoom_area_size // 2)

#         # Calculate the zoom factors for the selected area
#         canvas_width = self.canvas.winfo_width()
#         canvas_height = self.canvas.winfo_height()
#         zoom_width_factor = canvas_width / (right - left)
#         zoom_height_factor = canvas_height / (bottom - top)

#         # Update the zoom factor to fit the selected area
#         self.zoom_factor = min(zoom_width_factor, zoom_height_factor)

#         # Render the selected zoomed-in area
#         page = self.pdf_document.load_page(self.current_page)
#         matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)

#         # Translate the viewport to the selected area
#         translation_matrix = fitz.Matrix(1, 0, 0, 1, -left, -top)
#         combined_matrix = matrix * translation_matrix
#         pix = page.get_pixmap(matrix=combined_matrix, clip=(left, top, right, bottom))

#         # Convert the pixmap to an image
#         img = Image.open(io.BytesIO(pix.tobytes("png")))
#         if self.is_inverted:
#             img = ImageOps.invert(img.convert("RGB"))
#         img_tk = ImageTk.PhotoImage(img)

#         # Update the canvas with the new zoomed-in area
#         self.canvas.delete("all")
#         self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
#         self.canvas.img_tk = img_tk

#         # Update canvas scroll region
#         self.page_width, self.page_height = pix.width, pix.height
#         self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
#         # Disable zoom-in area mode after use
#         self.toggle_zoom_in_area_mode()

#     def toggle_zoom_in_area_mode(self):
#         """Toggle the mode to allow zooming into a specific area."""
#         if hasattr(self, "zoom_in_area_enabled") and self.zoom_in_area_enabled:
#             self.canvas.unbind("<Button-1>")
#             self.zoom_in_area_enabled = False
#         else:
#             self.canvas.bind("<Button-1>", self.zoom_in_area)
#             self.zoom_in_area_enabled = True

#     def toggle_drawing(self):
#         """Toggle the freehand drawing mode without embedding strokes into the PDF."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.is_drawing = not self.is_drawing  # Toggle drawing mode
#         if self.is_drawing:
#             self.canvas.bind("<Button-1>", self.start_freehand_drawing)
#             self.canvas.bind("<B1-Motion>", self.draw_freehand_line)
#             self.canvas.bind("<ButtonRelease-1>", self.finish_freehand_drawing)
#         else:
#             self.canvas.unbind("<Button-1>")
#             self.canvas.unbind("<B1-Motion>")
#             self.canvas.unbind("<ButtonRelease-1>")

#     def start_freehand_drawing(self, event):
#         """Start recording a freehand drawing stroke with unscaled coordinates."""
#         self.freehand_stroke = [(event.x / self.zoom_factor, event.y / self.zoom_factor)]
#         self.current_line = self.canvas.create_line(
#             self.freehand_stroke[0][0] * self.zoom_factor,
#             self.freehand_stroke[0][1] * self.zoom_factor,
#             self.freehand_stroke[0][0] * self.zoom_factor,
#             self.freehand_stroke[0][1] * self.zoom_factor,
#             fill="black", width=2
#         )

#     def draw_freehand_line(self, event):
#         """Draw a freehand stroke in real-time with unscaled coordinates."""
#         if not hasattr(self, "freehand_stroke"):
#             return

#         x, y = event.x / self.zoom_factor, event.y / self.zoom_factor
#         page_width = self.page_width / self.zoom_factor
#         page_height = self.page_height / self.zoom_factor

#         # Ensure the stroke stays within the page bounds
#         x = max(0, min(x, page_width))
#         y = max(0, min(y, page_height))

#         self.freehand_stroke.append((x, y))
#         scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in self.freehand_stroke]
#         self.canvas.coords(self.current_line, *sum(scaled_points, ()))

#     def finish_freehand_drawing(self, event):
#         """Save the drawn freehand stroke for undo functionality without embedding into the PDF."""
#         if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
#             return
#         self.freehand_drawings.append((self.current_page, self.current_line, self.freehand_stroke))
#         self.change_history.append(("freehand", self.current_page, self.current_line, self.freehand_stroke))

#         self.annotation_is_available = True
#         del self.freehand_stroke
#         del self.current_line
#         self.toggle_drawing()
#         self.render_page(self.current_page)  # Re-render to ensure it's drawn correctly
#         self.redraw_freehand_drawings()
#         self.annotation_listed.append("freehand")

#     # def finish_freehand_drawing(self, event):
#     #     """Save the drawn freehand stroke for undo functionality without embedding into the PDF."""
#     #     if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
#     #         return
        
#     #     # Save the stroke in change history
#     #     # changes_data = (("freehand", self.current_page, self.current_line, self.freehand_stroke))
#     #     # changes_data = str(changes_data)
#     #     # sql_check = """
#     #     #     SELECT COUNT(*) FROM pdf_editor_details 
#     #     #     WHERE folder_path = %s AND filename = %s AND changes_data = %s
#     #     # """
#     #     # mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
#     #     # result = mycursor.fetchone()
#     #     # if result[0] == 0:
#     #     #     sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
#     #     #     val = (beforeexe,folderpath,changes_data,0)
#     #     #     mycursor.execute(sql, val)
#     #     #     mydb.commit()
#     #     self.freehand_drawings.append((self.current_page, self.current_line, self.freehand_stroke))
#     #     print("(self.current_page, self.current_line, self.freehand_stroke)-",(self.current_page, self.current_line, self.freehand_stroke))
#     #     self.change_history.append(("freehand", self.current_page, self.current_line, self.freehand_stroke))
#     #     self.annotation_is_available = True
#     #     del self.freehand_stroke
#     #     del self.current_line
#     #     self.toggle_drawing()
#     #     self.render_page(self.current_page)
#     #     self.redraw_freehand_drawings()

#     def redraw_freehand_drawings(self):
#         """Redraw all freehand drawings, applying zoom and rotation transformations."""
#         self.canvas.delete("freehand")  # Clear previous drawings

#         for i, entry in enumerate(self.change_history):
#             if entry[0] == "freehand":
#                 _, page, line_id, points = entry
#                 if page != self.current_page:
#                     continue
                
#                 transformed_points = [self.apply_transformations(x, y) for x, y in points]
#                 scaled_points = [(x * self.zoom_factor, y * self.zoom_factor) for x, y in transformed_points]
#                 fill_color = "black" if not self.is_inverted else "white"
#                 new_line_id = self.canvas.create_line(
#                     *sum(scaled_points, ()),
#                     fill=fill_color, width=3, tags="freehand"
#                 )
#                 self.change_history[i] = ("freehand", page, new_line_id, points)
#     def apply_transformations(self, x, y):
#         """Apply rotation first, then zoom transformations to a given point."""
#         page = self.pdf_document[self.current_page]
#         rotation_angle = page.rotation
#         page_width = self.page_width / self.zoom_factor  # Unscaled width
#         page_height = self.page_height / self.zoom_factor  # Unscaled height

#         # Apply rotation without zooming
#         if rotation_angle == 90:
#             if is_small_page == "yes":
#                 x, y = page_height+(180) - y, x
#             elif is_small_page == "slightly":
#                 x,y = page_height+(1050)-y, x
#             elif is_small_page == "longer":
#                 x, y = page_height+(720) - y, x 
#             elif is_small_page == "maybe":
#                 x, y = page_height+(750) - y, x
#             elif is_small_page == "nope large":
#                 x, y = page_height+(1000) - y, x
#             elif is_small_page == "nope very large":
#                 x, y = page_height+(4300) - y, x
#             else:
#                 x, y = page_height+(2000) - y, x
#         elif rotation_angle == 180:
#             x, y = page_width - x, page_height - y
#         elif rotation_angle == 270:
#             if is_small_page == "yes":
#                 x, y = y, page_width-(180) - x
#             elif is_small_page == "slightly":
#                 x,y = y, page_width-(1050) - x
#             elif is_small_page == "longer":
#                 x, y = y, page_width-(720) - x
#             elif is_small_page == "maybe":
#                 x, y = y, page_width-(750) - x
#             elif is_small_page == "nope large":
#                 x, y = y, page_width-(1000) - x
#             elif is_small_page == "nope very large":
#                 x, y = y, page_width-(4300) - x
#             else:
#                 x, y = y, page_width-(2000) - x
#         return x, y

#     def toggle_filled_polygon_mode(self):
#         """Toggle filled polygon drawing mode."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return

#         if self.polygon_mode == "filled":
#             # Deactivate the mode
#             self.filled_polygon_button.configure(text="")
#             self.polygon_mode = None
#             self.start_point = None
#             self.polygon_created = False  # Reset creation flag
#             self.polygon_active = "no"
#             self.canvas.unbind("<Button-1>")
#             self.canvas.config(cursor="arrow")
#             # self.embed_polygons_in_pdf()
#             self.redraw_polygons()
#         else:
#             # Deactivate hollow mode if active
#             if self.polygon_mode == "hollow":
#                 self.hollow_polygon_button.configure(text="")

#             # Activate filled mode
#             self.filled_polygon_button.configure(text="#")
#             self.polygon_active = "yes"
#             self.polygon_mode = "filled"
#             self.start_point = None
#             self.polygon_created = False  # Reset creation flag
#             self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)


#     def toggle_hollow_polygon_mode(self):
#         """Toggle hollow polygon drawing mode."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return

#         if self.polygon_mode == "hollow":
#             # Deactivate the mode
#             self.hollow_polygon_button.configure(text="")
#             self.polygon_mode = None
#             self.start_point = None
#             self.polygon_active = "no"
#             self.polygon_created = False  # Reset creation flag
#             self.canvas.unbind("<Button-1>")
#             self.canvas.config(cursor="arrow")
#             self.redraw_polygons()
#             # self.embed_polygons_in_pdf()
#         else:
#             # Deactivate filled mode if active
#             if self.polygon_mode == "filled":
#                 self.filled_polygon_button.configure(text="")

#             # Activate hollow mode
#             self.hollow_polygon_button.configure(text="#")
#             self.polygon_active = "yes"
#             self.polygon_mode = "hollow"
#             self.start_point = None
#             self.polygon_created = False  # Reset creation flag
#             self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)


#     def is_point_inside_polygon(self, x, y, points):
#         num_points = len(points) // 2
#         polygon = [(points[i * 2], points[i * 2 + 1]) for i in range(num_points)]
#         inside = False

#         for i in range(num_points):
#             x1, y1 = polygon[i]
#             x2, y2 = polygon[(i + 1) % num_points]

#             if ((y1 > y) != (y2 > y)) and (x < (x2 - x1) * (y - y1) / (y2 - y1) + x1):
#                 inside = not inside

#         return inside

#     def generate_polygon_points(self, x, y, radius, sides):
#         """Generate the points of a regular polygon with given sides and radius."""
#         points = []
#         for i in range(sides):
#             angle = 2 * math.pi * i / sides
#             px = x + radius * math.cos(angle)
#             py = y + radius * math.sin(angle)
#             points.append(px)
#             points.append(py)
#         return points

#     def on_canvas_polygon_click(self, event):
#         """Handle canvas clicks for creating or modifying polygons."""
#         if not self.polygon_mode:
#             return
        
#         # Convert the click position to PDF space
#         x = self.canvas.canvasx(event.x) / self.zoom_factor
#         y = self.canvas.canvasy(event.y) / self.zoom_factor

#         if self.current_page not in self.page_drawings:
#             self.page_drawings[self.current_page] = []

#         for idx, drawing in enumerate(self.page_drawings[self.current_page]):
#             if len(drawing) != 3:
#                 continue

#             mode, points, polygon_id = drawing

#             if self.is_point_inside_polygon(x, y, points):
#                 self.canvas.config(cursor="hand2")

#                 # Convert the zoom factor correctly for dragging
#                 zoom_adjusted_radius = max(10, 15 / self.zoom_factor)
#                 for i in range(0, len(points), 2):
#                     vx, vy = points[i], points[i + 1]
#                     if abs(vx - x) < zoom_adjusted_radius and abs(vy - y) < zoom_adjusted_radius:
#                         self.dragging_polygon = (idx, i // 2)
#                         self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
#                         self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
#                         self.canvas.config(cursor="fleur")
#                         return

#                 self.dragging_polygon = (idx, None)
#                 self.start_drag_x, self.start_drag_y = x, y
#                 self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
#                 self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
#                 self.canvas.config(cursor="fleur")
#                 return

#         # If a new polygon needs to be created
#         if self.start_point is None:
#             self.start_point = (x, y)

#             points = self.generate_polygon_points(
#                 x, y, 
#                 self.polygon_size / self.zoom_factor, 
#                 5
#             )

#             # Scale points back for display on the canvas
#             scaled_points = [coord * self.zoom_factor for coord in points]

#             polygon_id = self.canvas.create_polygon(
#                 scaled_points,
#                 fill="blue" if self.polygon_mode == "filled" else "",
#                 outline="black" if self.polygon_mode == "filled" else "red",
#                 tags=("polygon",)
#             )

#             self.page_drawings[self.current_page].append((self.polygon_mode, points, polygon_id))
#             self.change_history.append(("polygon", self.current_page, None, polygon_id))
#         else:
#             self.start_point = None

#         self.redraw_polygons()

#     def embed_polygons_in_pdf(self):
#         """Embed only existing polygons in the PDF with proper scaling."""
#         if not self.pdf_document or self.current_page not in self.page_drawings:
#             return  # No valid PDF or no drawings on the current page

#         page = self.pdf_document[self.current_page]
        
#         # Remove old polygon annotations before embedding new ones
#         for annot in page.annots():
#             if annot.info.get("title") == "polygon_annotation":
#                 annot.delete()

#         zoom_matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
#         self.annotation_is_available = True

#         # Ensure only non-removed polygons get embedded
#         remaining_polygons = []
        
#         for drawing in self.page_drawings[self.current_page]:  
#             if len(drawing) != 3:
#                 print(f"Skipping invalid entry: {drawing}")
#                 continue

#             mode, points, polygon_id = drawing

#             # Check if this polygon has been removed via undo
#             if self.current_page in self.embedded_polygons:
#                 if any(p[2] == polygon_id for p in self.embedded_polygons[self.current_page]):
#                     continue  # Skip embedding removed polygons

#             scaled_points = [(points[i] / self.zoom_factor, points[i + 1] / self.zoom_factor)
#                             for i in range(0, len(points), 2)]

#             path = page.new_shape()
#             for i in range(len(scaled_points)):
#                 p1 = scaled_points[i]
#                 p2 = scaled_points[(i + 1) % len(scaled_points)]
#                 path.draw_line(p1, p2)

#             if mode == "filled":
#                 path.finish(fill=(0, 0, 1), color=None)
#             elif mode == "hollow":
#                 path.finish(color=(1, 0, 0), fill=None)

#             path.commit()

#             remaining_polygons.append(drawing)  # Only keep actually embedded polygons

#         self.embedded_polygons[self.current_page] = remaining_polygons  # Update embedded list
#         self.annotation_listed.append("polygon")
#     def on_polygon_drag_vertex(self, event):
#         if not hasattr(self, 'dragging_polygon'):
#             return

#         idx, vertex_idx = self.dragging_polygon
#         if vertex_idx is None:
#             return

#         mode, points, polygon_id = self.page_drawings[self.current_page][idx]
#         x = self.canvas.canvasx(event.x) / self.zoom_factor
#         y = self.canvas.canvasy(event.y) / self.zoom_factor

#         x = max(0, min(x, self.page_width / self.zoom_factor))
#         y = max(0, min(y, self.page_height / self.zoom_factor))

#         points[vertex_idx * 2] = x
#         points[vertex_idx * 2 + 1] = y

#         scaled_points = [p * self.zoom_factor for p in points]
#         self.canvas.coords(polygon_id, *scaled_points)


#     def on_polygon_drag_entire(self, event):
#         if not hasattr(self, 'dragging_polygon'):
#             return
#         idx, _ = self.dragging_polygon
#         mode, points, polygon_id = self.page_drawings[self.current_page][idx]
#         x, y = self.canvas.canvasx(event.x) / self.zoom_factor, self.canvas.canvasy(event.y) / self.zoom_factor
#         dx, dy = x - self.start_drag_x, y - self.start_drag_y

#         # Constrain entire polygon to remain inside the page boundary
#         min_x = min(points[::2]) + dx
#         min_y = min(points[1::2]) + dy
#         max_x = max(points[::2]) + dx
#         max_y = max(points[1::2]) + dy

#         if min_x < 0 or max_x > self.page_width / self.zoom_factor or min_y < 0 or max_y > self.page_height / self.zoom_factor:
#             return  # Prevent movement outside the page

#         for i in range(0, len(points), 2):
#             points[i] += dx
#             points[i + 1] += dy

#         scaled_points = [(p * self.zoom_factor) for p in points]
#         self.canvas.coords(polygon_id, scaled_points)

#         self.start_drag_x, self.start_drag_y = x, y


#     def on_polygon_drag_release(self, event):
#         """Release the polygon after dragging."""
#         if hasattr(self, 'dragging_polygon'):
#             del self.dragging_polygon
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")
#         self.redraw_polygons()

#     def attach_image_to_pdf(self):
#         """Attach an image to the currently loaded PDF with interactive placement and resizing."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF loaded.", parent=self.root)
#             return

#         # Open file dialog with the subwindow as the parent to prevent focus jump to main window
#         image_path = filedialog.askopenfilename(
#             title="Select an Image",
#             filetypes=[("Image Files", "*.png;*.jpg;*.jpeg"), ("All Files", "*.*")],
#             parent=self.root  # 👈 This keeps the dialog tied to the subwindow
#         )

#         if not image_path:
#             return  # User canceled the dialog

#         try:
#             img = Image.open(image_path)
#             img.thumbnail((200, 200), Image.LANCZOS)
#             self.tk_image = ImageTk.PhotoImage(img)

#             self.active_image = self.canvas.create_image(
#                 100, 100,
#                 image=self.tk_image,
#                 anchor="nw",
#                 tags="temp_image_overlay"
#             )

#             self.image_data = {
#                 "id": f"img_{len(self.image_overlays)}",
#                 "image_path": image_path,
#                 "image_obj": img,
#                 "x": 100, "y": 100,
#                 "width": img.width, "height": img.height,
#                 "base_x": 100 / self.zoom_factor,
#                 "base_y": 100 / self.zoom_factor,
#                 "base_width": img.width / self.zoom_factor,
#                 "base_height": img.height / self.zoom_factor,
#                 "page": self.current_page
#             }

#             self.canvas.tag_bind(self.active_image, "<ButtonPress-1>", self.start_move)
#             self.canvas.tag_bind(self.active_image, "<B1-Motion>", self.do_move)
#             self.canvas.tag_bind(self.active_image, "<ButtonRelease-1>", self.finalize_move)
#             self.canvas.bind_all("<MouseWheel>", self.resize_image)

#         except Exception as e:
#             messagebox.showerror("Error", f"Failed to load image: {str(e)}", parent=self.root)

        

#     def start_move(self, event):
#         """Start dragging the image."""
#         self.image_data["start_x"] = event.x
#         self.image_data["start_y"] = event.y

#     def do_move(self, event):
#         """Move the image as the mouse drags."""
#         dx = event.x - self.image_data["start_x"]
#         dy = event.y - self.image_data["start_y"]
        
#         self.canvas.move(self.active_image, dx, dy)
#         self.image_data["x"] += dx
#         self.image_data["y"] += dy
        
#         # Update base coordinates (unscaled)
#         self.image_data["base_x"] = self.image_data["x"] / self.zoom_factor
#         self.image_data["base_y"] = self.image_data["y"] / self.zoom_factor
        
#         self.image_data["start_x"] = event.x
#         self.image_data["start_y"] = event.y

#     def finalize_move(self, event):
#         """Finalize the image overlay position."""
#         user_response = messagebox.askyesnocancel(
#                 "Confirm Position",
#                 "Are you satisfied with the current position and size of the image? To Resize hold shift and scroll",
#                 parent=self.root  # 👈 Prevent focus from switching to main window
#             )
            
#         if user_response is None:  # User clicked 'Cancel'
#             self.canvas.delete(self.active_image)  # Remove the temporary image from canvas
#             self.active_image = None
#             self.image_data = None
#             return
            
#         if not user_response:  # User clicked 'No', allow them to move/reshape again
#             return  # Do nothing, letting them continue adjusting the image
        
#         self.annotation_is_available = True
        
#         try:
#             # Create the final overlay information
#             overlay_info = {
#                 "id": self.image_data["id"],
#                 "type": "image_overlay",
#                 "image_path": self.image_data["image_path"],
#                 "x": self.image_data["x"],
#                 "y": self.image_data["y"],
#                 "width": self.image_data["width"],
#                 "height": self.image_data["height"],
#                 "base_x": self.image_data["base_x"],
#                 "base_y": self.image_data["base_y"],
#                 "base_width": self.image_data["base_width"],
#                 "base_height": self.image_data["base_height"],
#                 "page": self.current_page,
#                 "canvas_id": self.active_image
#             }
            
#             # Add to image overlays list and change history
#             self.image_overlays.append(overlay_info)
#             self.change_history.append(("image_overlay", self.current_page, overlay_info))
            
#             # Remove the temporary image and redraw it as a permanent one
#             self.canvas.delete("temp_image_overlay")
#             self.redraw_image_overlays(self.current_page)
            
#             # Unbind events - this prevents the image from being moved after finalization
#             self.canvas.unbind_all("<MouseWheel>")
#             self.active_image = None
#             self.annotation_listed.append("image_overlay")
#         except Exception as e:
#             messagebox.showerror("Error", f"Failed to add image overlay: {e}",parent=self.root)

#     def resize_image(self, event):
#         """Resize the image using the mouse scroll."""
#         if event.state & 0x0001 == 0:
#             return  # Shift not pressed; ignore scroll
            
#         scale_factor = 1.1 if event.delta > 0 else 0.9
        
#         # Calculate new width and height
#         new_width = int(self.image_data["width"] * scale_factor)
#         new_height = int(self.image_data["height"] * scale_factor)
        
#         # Prevent the image from becoming too small
#         if new_width < 50 or new_height < 50:
#             return
            
#         # Update image data
#         self.image_data["width"] = new_width
#         self.image_data["height"] = new_height
#         self.image_data["base_width"] = new_width / self.zoom_factor
#         self.image_data["base_height"] = new_height / self.zoom_factor
        
#         # Resize the image
#         img_resized = self.image_data["image_obj"].resize((new_width, new_height), Image.LANCZOS)
#         self.tk_image = ImageTk.PhotoImage(img_resized)
#         self.canvas.itemconfig(self.active_image, image=self.tk_image)


#     def add_text_to_pdf(self):
#         """Enable text-adding mode on the PDF."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         self.canvas.bind("<Button-1>", self.on_add_text_click)
#         self.add_text_mode = True

#     def on_add_text_click(self, event):
#         """Handle adding text overlay at the clicked position with strict boundary enforcement."""
#         if not self.pdf_document or not self.add_text_mode:
#             return
        
#         x = self.canvas.canvasx(event.x)
#         y = self.canvas.canvasy(event.y)
        
#         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
#             return
            
#         text = self.ask_for_note_text(x, y, "Add Text")
#         if not text:
#             return
            
#         x_scaled = x / self.zoom_factor
#         y_scaled = y / self.zoom_factor
        
#         # Get the page dimensions
#         page = self.pdf_document[self.current_page]
#         page_width_scaled = page.rect.width
        
#         # Calculate the maximum width for text container
#         # Ensure text container never exceeds page boundaries
#         max_text_width = min(page_width_scaled - x_scaled - 20, page_width_scaled * 0.4)
        
#         # Store this as part of the annotation data
#         annotation_data = {
#             "text": text,
#             "max_width": max_text_width,
#             "font_size": 16
#         }
        
#         # Store the text with its constraints
#         self.text_annotations[(self.current_page, x_scaled, y_scaled)] = annotation_data
        
#         # Add to history
#         self.change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))
        
#         # Update display
#         self.render_page(self.current_page)
#         self.add_text_mode = False
#         self.canvas.unbind("<Button-1>")
#         self.annotation_is_available = True
#         self.annotation_listed.append("text")

#     def redraw_text_annotations(self):
#         """Redraw text annotations with strict boundary enforcement."""
#         self.canvas.delete("text_annotation")  # Clear previous annotations
        
#         if not self.pdf_document:
#             return
            
#         page = self.pdf_document[self.current_page]
#         rotation_angle = page.rotation
#         fill_color = "black" if not self.is_inverted else "white"
        
#         for (page_num, x_scaled, y_scaled), annotation_data in self.text_annotations.items():
#             if page_num == self.current_page:
#                 # If using the old format (just text string), convert to new format
#                 if isinstance(annotation_data, str):
#                     annotation_data = {
#                         "text": annotation_data,
#                         "max_width": page.rect.width * 0.4,  # default to 40% of page width
#                         "font_size": 16
#                     }
                
#                 text = annotation_data["text"]
#                 max_width = annotation_data["max_width"] * self.zoom_factor
#                 font_size = annotation_data["font_size"]
                
#                 x_position = x_scaled * self.zoom_factor
#                 y_position = y_scaled * self.zoom_factor
#                 # Adjust coordinates based on rotation
#                 if rotation_angle == 90:  # Rotate text **clockwise**
#                     if is_small_page == "yes":
#                         rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "slightly":
#                         rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "longer":
#                         rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "maybe":
#                         rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "nope large":
#                         rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "nope very large":
#                         rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
#                     else:
#                         rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position

#                     angle = -90  # Fix: Rotate text correctly to the right
#                     container_width = max_width
#                 elif rotation_angle == 180:  # Rotate text upside down
#                     rotated_x = page.rect.width * self.zoom_factor - x_position
#                     rotated_y = page.rect.height * self.zoom_factor - y_position
#                     angle = 180
#                     container_width = max_width
#                 elif rotation_angle == 270:  # Rotate text **counterclockwise**
#                     if is_small_page == "yes":
#                         rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
#                     elif is_small_page == "slightly":
#                         rotated_x, rotated_y = y_position, self.page_width-(1050*self.zoom_factor) - x_position
#                     elif is_small_page == "longer":
#                         rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position
#                     elif is_small_page == "maybe":
#                        rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position 
#                     elif is_small_page == "nope large":
#                         rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
#                     elif is_small_page == "nope very large":
#                         rotated_x, rotated_y = y_position, self.page_width-(4300*self.zoom_factor) - x_position
#                     else:
#                         rotated_x, rotated_y = y_position, self.page_width-(2000*self.zoom_factor) - x_position
#                     angle = -270  # Fix: Rotate text correctly to the left
#                     container_width = max_width
#                 else:  # 0 degrees (default)
#                     rotated_x = x_position
#                     rotated_y = y_position
#                     angle = 0
#                     container_width = max_width

#                 text_container = self.canvas.create_text(
#                     rotated_x, rotated_y,
#                     text=text,
#                     font=("Arial", font_size),
#                     fill=fill_color,
#                     width=container_width,  # This is critical - it forces text wrapping
#                     tags="text_annotation",
#                     anchor="nw")
                
#                 # Apply rotation if needed
#                 self.canvas.itemconfig(text_container, angle=angle)
        
#         self.annotation_is_available = True

#     def add_text_with_background(self):
#         """Enable text-adding mode for text with a background."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.canvas.bind("<Button-1>", self.on_add_text_with_bg_click)
#         self.add_text_bg_mode = True

#     def on_add_text_with_bg_click(self, event):
#         """Handle adding text with a background at the clicked position."""
#         if not self.pdf_document or not self.add_text_bg_mode:
#             return

#         x = self.canvas.canvasx(event.x)
#         y = self.canvas.canvasy(event.y)

#         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
#             return

#         text = self.ask_for_note_text(x, y, "Add Text with Background")
#         if not text:
#             return

#         wrapped_text = "\n".join(textwrap.wrap(text, width=30))
#         x_scaled = x / self.zoom_factor
#         y_scaled = y / self.zoom_factor

#         fontsize = 16
#         text_lines = wrapped_text.split("\n")
#         max_width = max(len(line) for line in text_lines) * fontsize * 0.6
#         text_height = fontsize * 1.2 * len(text_lines)

#         # Store the text annotation with background instead of embedding in PDF
#         self.text_annotations_bg[(self.current_page, x_scaled, y_scaled)] = wrapped_text

#         #Store change history for undo
#         # changes_data = ("add_text_bg", self.current_page, x_scaled, y_scaled, text)
#         # changes_data = str(changes_data)
#         # sql_check = """
#         #     SELECT COUNT(*) FROM pdf_editor_details 
#         #     WHERE folder_path = %s AND filename = %s AND changes_data = %s
#         # """
#         # mycursor.execute(sql_check, (folderpath, beforeexe, changes_data))
#         # result = mycursor.fetchone()
#         # if result[0] == 0:
#         #     sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
#         #     val = (beforeexe,folderpath,changes_data,0)
#         #     mycursor.execute(sql, val)
#         #     mydb.commit()
#         self.change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, text))

#         self.render_page(self.current_page)  # Refresh page to show new annotation
#         self.add_text_bg_mode = False
#         self.canvas.unbind("<Button-1>")
#         self.annotation_is_available = True
#         self.annotation_listed.append("text_bg")

#     def redraw_text_with_background(self):
#         """Redraw text annotations with background after rendering the page and adjust for zoom and rotation."""
#         self.canvas.delete("text_annotation_bg")  # Clear previous background text

#         if not self.pdf_document:
#             return

#         page = self.pdf_document[self.current_page]
#         rotation_angle = page.rotation  # Get current page rotation
#         fill_color = "black" if not self.is_inverted else "white"
#         for (page_num, x_scaled, y_scaled), text in self.text_annotations_bg.items():
#             if page_num == self.current_page:
#                 x_position = x_scaled * self.zoom_factor
#                 y_position = y_scaled * self.zoom_factor

#                 # Get page dimensions at the current zoom level
#                 page_width = page.rect.width * self.zoom_factor
#                 page_height = page.rect.height * self.zoom_factor

#                 fontsize = 16
#                 wrapped_text = "\n".join(textwrap.wrap(text, width=30))
#                 text_lines = wrapped_text.split("\n")
#                 max_width = max(len(line) for line in text_lines) * fontsize * 0.6
#                 text_height = fontsize * 1.2 * len(text_lines)
#                 # Adjust coordinates based on rotation
#                 if rotation_angle == 90:  # Rotate text **clockwise**
#                     if is_small_page == "yes":
#                         rotated_x, rotated_y = self.page_height+(180*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "slightly":
#                         rotated_x, rotated_y = self.page_height+(1050*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "longer":
#                         rotated_x, rotated_y = self.page_height+(720*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "maybe":
#                         rotated_x, rotated_y = self.page_height+(750*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "nope large":
#                         rotated_x, rotated_y = self.page_height+(1000*self.zoom_factor) - y_position, x_position
#                     elif is_small_page == "nope very large":
#                         rotated_x, rotated_y = self.page_height+(4300*self.zoom_factor) - y_position, x_position
#                     else:
#                         rotated_x, rotated_y = self.page_height+(2000*self.zoom_factor) - y_position, x_position
#                     rect_x1 = rotated_x - text_height - 15
#                     rect_y1 = rotated_y
#                     rect_x2 = rotated_x
#                     rect_y2 = rotated_y + max_width + 10
#                     angle = -90  # Fix: Rotate text correctly to the right
#                 elif rotation_angle == 180:  # Rotate text upside down
#                     rotated_x = page_width - x_position
#                     rotated_y = page_height - y_position
#                     rect_x1 = rotated_x - max_width - 10
#                     rect_y1 = rotated_y - text_height - 15
#                     rect_x2 = rotated_x
#                     rect_y2 = rotated_y
#                     angle = 180
#                 elif rotation_angle == 270:  # Rotate text **counterclockwise**
#                     if is_small_page == "yes":
#                         rotated_x, rotated_y = y_position, self.page_width-(180*self.zoom_factor) - x_position
#                     elif is_small_page == "slightly":
#                         rotated_x, rotated_y = y_position, self.page_width-(1050*self.zoom_factor) - x_position
#                     elif is_small_page == "longer":
#                         rotated_x, rotated_y = y_position, self.page_width-(720*self.zoom_factor) - x_position
#                     elif is_small_page == "maybe":
#                         rotated_x, rotated_y = y_position, self.page_width-(750*self.zoom_factor) - x_position
#                     elif is_small_page == "nope large":
#                         rotated_x, rotated_y = y_position, self.page_width-(1000*self.zoom_factor) - x_position
#                     elif is_small_page == "nope very large":
#                         rotated_x, rotated_y = y_position, self.page_width-(4300*self.zoom_factor) - x_position
#                     else:
#                         rotated_x, rotated_y = y_position, self.page_width-(2000*self.zoom_factor) - x_position
#                     rect_x1 = rotated_x
#                     rect_y1 = rotated_y - max_width - 10
#                     rect_x2 = rotated_x + text_height + 15
#                     rect_y2 = rotated_y
#                     angle = -270  # Fix: Rotate text correctly to the left
#                 else:  # 0 degrees (default)
#                     rotated_x = x_position
#                     rotated_y = y_position
#                     rect_x1 = rotated_x
#                     rect_y1 = rotated_y
#                     rect_x2 = rotated_x + max_width + 10
#                     rect_y2 = rotated_y + text_height + 15
#                     angle = 0

#                 rect_id = self.canvas.create_rectangle(
#                     rect_x1, rect_y1, rect_x2, rect_y2,
#                     fill="cyan",
#                     outline="cyan",
#                     tags="text_annotation_bg"
#                 )
          
#                 text_id = self.canvas.create_text(
#                     rotated_x, rotated_y,
#                     text=text,
#                     font=("Arial", 16),
#                     fill=fill_color,
#                     tags="text_annotation",
#                     anchor="nw"
#                 )

#                 self.canvas.itemconfig(text_id, angle=angle)

#         self.annotation_is_available = True

#     def activate_line_tool(self):
#         """Activate the straight line drawing tool."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.deactivate_tools()
#         self.is_drawing_line = True
#         self.canvas.bind("<Button-1>", self.start_line)
#         self.canvas.bind("<B1-Motion>", self.draw_line_preview)
#         self.canvas.bind("<ButtonRelease-1>", self.finish_line)

#     def activate_arrow_tool(self):
#         """Activate the arrow drawing tool."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.deactivate_tools()
#         self.is_drawing_arrow = True
#         self.canvas.bind("<Button-1>", self.start_line)
#         self.canvas.bind("<B1-Motion>", self.draw_line_preview)
#         self.canvas.bind("<ButtonRelease-1>", self.finish_arrow)

#     def deactivate_tools(self):
#         """Deactivate all tools."""
#         self.is_drawing_line = False
#         self.is_drawing_arrow = False
#         self.is_drawing_hollow_rect = False
#         self.is_drawing_filled_rect = False
#         self.canvas.unbind("<Button-1>")
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")

#     def start_line(self, event):
#         """Start drawing a line or arrow."""
#         self.start_x = self.canvas.canvasx(event.x)
#         self.start_y = self.canvas.canvasy(event.y)
#         self.current_line = None

#     def draw_line_preview(self, event):
#         """Show a preview of the line or arrow while dragging."""
#         if self.current_line:
#             self.canvas.delete(self.current_line)
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
        
#         if self.is_drawing_line:
#             self.current_line = self.canvas.create_line(
#                 self.start_x, self.start_y, end_x, end_y,
#                 fill="red", width=3, tags="annotation_preview")
#         elif self.is_drawing_arrow:
#             self.current_line = self.canvas.create_line(
#                 self.start_x, self.start_y, end_x, end_y,
#                 fill="red", width=3, arrow=ctk.LAST, 
#                 arrowshape=(16, 20, 6), tags="annotation_preview")

#     def finish_line(self, event):
#         """Finish drawing the line and add it to annotations."""
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
        
#         # Create visual line on canvas
#         line_id = self.canvas.create_line(
#             self.start_x, self.start_y, end_x, end_y,
#             fill="red", width=3, tags="annotation")
        
#         # Store line data (in original PDF coordinates)
#         line_data = {
#             'type': 'line',
#             'page': self.current_page,
#             'x1': self.start_x / self.zoom_factor,
#             'y1': self.start_y / self.zoom_factor,
#             'x2': end_x / self.zoom_factor,
#             'y2': end_y / self.zoom_factor,
#             'id': line_id
#         }
        
#         self.lines.append(line_data)
#         self.annotations.append(line_data)
#         self.change_history.append(('add_annotation', line_data))
#         self.annotation_is_available = True
#         self.deactivate_tools()
#         self.annotation_listed.append("line")
#     def finish_arrow(self, event):
#         """Finish drawing the arrow and add it to annotations."""
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
        
#         # Create visual arrow on canvas
#         arrow_id = self.canvas.create_line(
#             self.start_x, self.start_y, end_x, end_y,
#             fill="red", width=3, arrow=ctk.LAST, 
#             arrowshape=(16, 20, 6), tags="annotation")
        
#         # Store arrow data (in original PDF coordinates)
#         arrow_data = {
#             'type': 'arrow',
#             'page': self.current_page,
#             'x1': self.start_x / self.zoom_factor,
#             'y1': self.start_y / self.zoom_factor,
#             'x2': end_x / self.zoom_factor,
#             'y2': end_y / self.zoom_factor,
#             'id': arrow_id
#         }
        
#         self.arrows.append(arrow_data)
#         self.annotations.append(arrow_data)
#         self.change_history.append(('add_annotation', arrow_data))
#         self.annotation_is_available = True
#         self.deactivate_tools()
#         self.annotation_listed.append("arrow")

#     def activate_hollow_rectangle_tool(self):
#         """Activate the hollow rectangle drawing tool."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.deactivate_tools()
#         self.is_drawing_hollow_rect = True
#         self.is_drawing_filled_rect = False  # Ensure only one mode is active
#         self.highlight_mode = False
#         self.canvas.bind("<Button-1>", self.start_rectangle_drawing)
#         self.canvas.bind("<B1-Motion>", self.draw_rectangle_preview)
#         self.canvas.bind("<ButtonRelease-1>", self.finish_hollow_rectangle)

#     def activate_filled_rectangle_tool(self):
#         """Activate the filled rectangle drawing tool."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         self.deactivate_tools()
#         self.is_drawing_filled_rect = True
#         self.is_drawing_hollow_rect = False
#         self.highlight_mode = False
#         self.canvas.bind("<Button-1>", self.start_rectangle_drawing)
#         self.canvas.bind("<B1-Motion>", self.draw_rectangle_preview)
#         self.canvas.bind("<ButtonRelease-1>", self.finish_filled_rectangle)

#     def start_rectangle_drawing(self, event):
#         """Start drawing a rectangle (for hollow/filled tools)."""
#         self.start_x = self.canvas.canvasx(event.x)
#         self.start_y = self.canvas.canvasy(event.y)
#         if self.current_rectangle:
#             self.canvas.delete(self.current_rectangle)
#         outline_color = "red"
#         fill_color = "" if self.is_drawing_hollow_rect else "red"
#         self.current_rectangle = self.canvas.create_rectangle(
#             self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
#             outline=outline_color, fill=fill_color, width=2, tags="annotation_preview")

#     def draw_rectangle_preview(self, event):
#         """Show a preview of the rectangle while dragging."""
#         if self.current_rectangle:
#             self.canvas.delete(self.current_rectangle)
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
#         outline_color = "red"
#         fill_color = "" if self.is_drawing_hollow_rect else "red"
#         self.current_rectangle = self.canvas.create_rectangle(
#             self.start_x, self.start_y, end_x, end_y,
#             outline=outline_color, fill=fill_color, width=3, tags="annotation_preview")

#     def finish_hollow_rectangle(self, event):
#         """Finish drawing the hollow rectangle and add it to annotations."""
#         self.finish_rectangle(event, filled=False)

#     def finish_filled_rectangle(self, event):
#         """Finish drawing the filled rectangle and add it to annotations."""
#         self.finish_rectangle(event, filled=True)

#     def finish_rectangle(self, event, filled):
#         """Finish drawing a rectangle and add it to annotations."""
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
        
#         # Ensure coordinates are properly ordered (top-left to bottom-right)
#         x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
#         x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        
#         # Delete the preview rectangle
#         if self.current_rectangle:
#             self.canvas.delete(self.current_rectangle)
        
#         # Create visual rectangle on canvas
#         outline_color = "red"
#         fill_color = "" if not filled else "red"
#         rect_id = self.canvas.create_rectangle(
#             x1, y1, x2, y2,
#             outline=outline_color, fill=fill_color, width=3, tags="annotation")
        
#         # Store rectangle data (in original PDF coordinates)
#         rect_data = {
#             'type': 'rectangle',
#             'page': self.current_page,
#             'x1': x1 / self.zoom_factor,
#             'y1': y1 / self.zoom_factor,
#             'x2': x2 / self.zoom_factor,
#             'y2': y2 / self.zoom_factor,
#             'filled': filled,
#             'id': rect_id,
#             'color': "red"
#         }
        
#         self.rectangles.append(rect_data)
#         self.annotations.append(rect_data)
#         self.change_history.append(('add_annotation', rect_data))
#         self.annotation_is_available = True
#         self.deactivate_tools()
#         self.annotation_listed.append("rectangle")

#     def activate_hollow_ellipse(self):
#         self.ellipse_mode = "hollow"
#         self.canvas.bind("<ButtonPress-1>", self.start_ellipse)
#         self.canvas.bind("<B1-Motion>", self.draw_ellipse)
#         self.canvas.bind("<ButtonRelease-1>", self.finalize_ellipse)
    
#     def activate_filled_ellipse(self):
#         self.ellipse_mode = "filled"
#         self.canvas.bind("<ButtonPress-1>", self.start_ellipse)
#         self.canvas.bind("<B1-Motion>", self.draw_ellipse)
#         self.canvas.bind("<ButtonRelease-1>", self.finalize_ellipse)
    
#     def start_ellipse(self, event):
#         # Store the actual canvas coordinates (accounting for scrolling)
#         canvas_x = self.canvas.canvasx(event.x)
#         canvas_y = self.canvas.canvasy(event.y)
        
#         # Store the unscaled coordinates by dividing by the zoom factor
#         self.start_point = (canvas_x / self.zoom_factor, canvas_y / self.zoom_factor)
#         self.current_ellipse = None

#     def draw_ellipse(self, event):
#         if not self.start_point:
#             return
        
#         # Get original unscaled start coordinates
#         x1, y1 = self.start_point
        
#         # Get current canvas coordinates and unscale them
#         canvas_x = self.canvas.canvasx(event.x)
#         canvas_y = self.canvas.canvasy(event.y)
#         x2, y2 = canvas_x / self.zoom_factor, canvas_y / self.zoom_factor
        
#         # For display, scale both coordinates by zoom factor
#         display_x1, display_y1 = x1 * self.zoom_factor, y1 * self.zoom_factor
#         display_x2, display_y2 = x2 * self.zoom_factor, y2 * self.zoom_factor
        
#         if self.current_ellipse:
#             self.canvas.delete(self.current_ellipse)
        
#         outline = "orange"
#         fill = "" if self.ellipse_mode == "hollow" else "orange"
#         self.current_ellipse = self.canvas.create_oval(
#             display_x1, display_y1, display_x2, display_y2, 
#             outline=outline, width=3, fill=fill, tags="ellipse"
#         )

#     def finalize_ellipse(self, event):
#         if not self.start_point or not self.current_ellipse:
#             return
        
#         # Get original unscaled coordinates
#         x1, y1 = self.start_point
        
#         # Get current position and unscale it
#         canvas_x = self.canvas.canvasx(event.x)
#         canvas_y = self.canvas.canvasy(event.y)
#         x2, y2 = canvas_x / self.zoom_factor, canvas_y / self.zoom_factor
        
#         # Store the original unscaled coordinates in annotations
#         self.annotations.append(("ellipse", x1, y1, x2, y2, self.current_ellipse, self.ellipse_mode,self.current_page))
#         self.change_history.append(("ellipse", x1, y1, x2, y2, self.current_ellipse, self.ellipse_mode))
        
#         self.ellipse_mode = None
#         self.start_point = None
        
#         # Reset bindings
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")
#         self.annotation_listed.append("ellipse")


#     def activate_selection_mode(self):
#         """Activate the zoom area tool."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
        
#         # Properly deactivate all tools first
#         self.deactivate_tools()
        
#         # Reset the zoom rectangle reference
#         self.zoom_rectangle = None
#         self.is_zooming_area = True
        
#         # Apply new bindings
#         self.canvas.bind("<Button-1>", self.start_zoom_area)
#         self.canvas.bind("<B1-Motion>", self.draw_zoom_rectangle)
#         self.canvas.bind("<ButtonRelease-1>", self.finish_zoom_area)
        
#     def start_zoom_area(self, event):
#         """Start drawing the zoom selection rectangle."""
#         self.start_x = self.canvas.canvasx(event.x)
#         self.start_y = self.canvas.canvasy(event.y)
#         self.zoom_rectangle = self.canvas.create_rectangle(
#             self.start_x, self.start_y, self.start_x, self.start_y, outline="blue", width=2
#         )
        
#     def draw_zoom_rectangle(self, event):
#         """Update the rectangle as the user drags the mouse."""
#         current_x = self.canvas.canvasx(event.x)
#         current_y = self.canvas.canvasy(event.y)
#         self.canvas.coords(self.zoom_rectangle, self.start_x, self.start_y, current_x, current_y)


# ####################################### fast and better ##############################################
#     def finish_zoom_area(self, event):
#         """Zoom into the selected area and keep it centered accurately."""
#         if not hasattr(self, 'zoom_rectangle') or self.zoom_rectangle is None:
#             return
            
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
#         x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
#         x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        
#         # Don't proceed with very small selections
#         if (x2 - x1) < 5 or (y2 - y1) < 5:
#             self.deactivate_selection_mode()
#             return
            
#         x1_pdf, y1_pdf = x1 / self.zoom_factor, y1 / self.zoom_factor
#         x2_pdf, y2_pdf = x2 / self.zoom_factor, y2 / self.zoom_factor
#         selected_width = x2_pdf - x1_pdf
#         selected_height = y2_pdf - y1_pdf
        
#         if selected_width <= 0 or selected_height <= 0:
#             self.deactivate_selection_mode()
#             return  # Prevent invalid selections
            
#         canvas_width = self.canvas.winfo_width()
#         canvas_height = self.canvas.winfo_height()
#         zoom_x = canvas_width / selected_width
#         zoom_y = canvas_height / selected_height
#         new_zoom_factor = min(zoom_x, zoom_y)
#         new_zoom_factor = max(0.1, min(new_zoom_factor, 10))
        
#         center_x_pdf = (x1_pdf + x2_pdf) / 2
#         center_y_pdf = (y1_pdf + y2_pdf) / 2
#         self.zoom_factor = new_zoom_factor
        
#         # Delete zoom rectangle before rendering to avoid artifacts
#         self.canvas.delete(self.zoom_rectangle)
#         self.zoom_rectangle = None
        
#         self.render_page(self.current_page)
        
#         # Calculate scrolling position to center the zoomed area
#         scroll_x = ((center_x_pdf * new_zoom_factor) - (canvas_width / 2)) / self.page_width
#         scroll_y = ((center_y_pdf * new_zoom_factor) - (canvas_height / 2)) / self.page_height
#         scroll_x = max(0, min(scroll_x, 1))
#         scroll_y = max(0, min(scroll_y, 1))
        
#         self.canvas.xview_moveto(scroll_x)
#         self.canvas.yview_moveto(scroll_y)
        
#         # Properly deactivate the selection mode to restore normal functionality
#         self.deactivate_selection_mode()

# ##############################################################################################################


#     def toggle_redaction_mode(self):
#         """Toggle redaction mode properly without requiring double clicks."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         if self.time_redact_used == 0:
#             messagebox.showinfo("Info", "Use redact only after adding all Annotations and changes if not the redact and annotations will be created on the same file.",parent=self.root)
#             response = messagebox.askyesnocancel("Confirm", "Do you want to save changes before using the redact?",parent=self.root)        
#             self.time_redact_used +=1
#             if response:
#                 self.save_pdf()
#                 if self.redaction_mode:
#                     self.deactivate_redact_tools()
#                 else:
#                     self.activate_redaction_mode()
#             elif response is None:
#                 return
#             else:
#                 if self.redaction_mode:
#                     self.deactivate_redact_tools()
#                 else:
#                     self.activate_redaction_mode()
#         else:
#             if self.redaction_mode:
#                 self.deactivate_redact_tools()
#             else:
#                 self.activate_redaction_mode()

#     def activate_redaction_mode(self):
#         """Ensure activation properly binds events and doesn't toggle incorrectly."""
#         self.redaction_mode = True
#         self.current_redaction = None  # Prevents lingering boxes
#         self.canvas.bind("<Button-1>", self.start_redaction)
#         self.canvas.bind("<B1-Motion>", self.draw_redaction_preview)
#         self.canvas.bind("<ButtonRelease-1>", self.finish_redaction)

#     def start_redaction(self, event):
#         """Start adding a redaction on click."""
#         self.start_x = self.canvas.canvasx(event.x)
#         self.start_y = self.canvas.canvasy(event.y)
#         self.current_redaction = None

#     def draw_redaction_preview(self, event):
#         """Show a redaction preview while dragging."""
#         if self.current_redaction:
#             self.canvas.delete(self.current_redaction)
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
#         self.current_redaction = self.canvas.create_rectangle(
#             self.start_x, self.start_y, end_x, end_y,
#             outline="black", fill="", width=2, tags="redaction_preview")

#     def finish_redaction(self, event):
#         """Finalize redaction on mouse release using proper PDF redaction annotation."""
#         if not self.redaction_mode:
#             return

#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
#         x1, y1 = min(self.start_x, end_x) / self.zoom_factor, min(self.start_y, end_y) / self.zoom_factor
#         x2, y2 = max(self.start_x, end_x) / self.zoom_factor, max(self.start_y, end_y) / self.zoom_factor

#         rect = fitz.Rect(x1, y1, x2, y2)
#         page = self.pdf_document[self.current_page]

#         # Add redaction annotation
#         page.add_redact_annot(rect, fill=(0, 0, 0))
#         print("rect----",rect)
#         print("type of rect---",type(rect))
#         # type of rect--- <class 'pymupdf.Rect'>
#         # changes_data = (self.current_page, rect)
#         # changes_data = str(changes_data)
#         # sql = "CALL sp_InsertPDFEditorDetails(%s, %s, %s, %s)"
#         # val = (beforeexe,folderpath,changes_data,1)
#         # mycursor.execute(sql, val)
#         # mydb.commit()
#         self.redactions.append((self.current_page, rect))
#         self.redo_redactions.append((self.current_page,self.zoom_factor, rect))
#         print("self.redactions--*****",self.redactions)
#         print("self.redo_redactions----------*****",self.redo_redactions)
#         # Remove preview outline
#         if self.current_redaction:
#             self.canvas.delete(self.current_redaction)
#             self.current_redaction = None  
#         self.render_page(self.current_page)
#         self.deactivate_redact_tools()  # Ensure deactivation
#         self.redaction_mode = False
#         self.redact_is_available = True

#     def reappear_redact(self):
#         """Finalize redaction on mouse release using proper PDF redaction annotation."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         if len(self.redo_redactions)==0:
#             return
#         print("self.redo_redactions----------*****",self.redo_redactions)
#         for page_number,zoom_factor,rect in self.redo_redactions:
#             if page_number == self.current_page:
#                 if self.zoom_factor > zoom_factor:
#                     zoom_factor = self.zoom_factor - zoom_factor
#                 elif self.zoom_factor < zoom_factor:
#                     zoom_factor = zoom_factor - self.zoom_factor
#                 elif self.zoom_factor == zoom_factor:
#                     zoom_factor = self.zoom_factor
#                 print("zoom_factor******----",zoom_factor)
#                 x1 = rect.x0 * zoom_factor
#                 y1 = rect.y0 * zoom_factor
#                 x2 = rect.x1 * zoom_factor
#                 y2 = rect.y1 * zoom_factor
#                 rect = fitz.Rect(x1, y1, x2, y2)
#                 page = self.pdf_document[page_number]
#                 page.add_redact_annot(rect, fill=(0, 0, 0))
#                 self.redactions.append((self.current_page, rect))
#                 self.current_redaction = None  
#         self.render_page(self.current_page)

#     def remove_black_boxes(self):
#         """Remove the most recent redaction annotation before applying them."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.",parent=self.root)
#             return
#         if len(self.redactions)==0:
#             return
#         page = self.pdf_document[self.current_page]
#         for i in range(len(self.redactions) - 1, -1, -1):
#             page_number, rect = self.redactions[i]
#             if page_number == self.current_page:
#                 annot = page.first_annot
#                 while annot:
#                     next_annot = annot.next  # Get next annotation before deleting
#                     if self.rects_are_close(annot.rect, rect):
#                         page.delete_annot(annot)
#                         self.redactions.pop(i)
#                         self.render_page(self.current_page)
#                         return  # Stop after removing one
#                     annot = next_annot

#     def rects_are_close(self, rect1, rect2, tol=0.1):
#         """Check if two rectangles are approximately equal within a small tolerance."""
#         return (
#             abs(rect1.x0 - rect2.x0) <= tol and
#             abs(rect1.y0 - rect2.y0) <= tol and
#             abs(rect1.x1 - rect2.x1) <= tol and
#             abs(rect1.y1 - rect2.y1) <= tol
#         )
#     def deactivate_redact_tools(self):
#         """Deactivate the redaction tool and ensure all events are unbound."""
#         self.redaction_mode = False
#         self.canvas.unbind("<Button-1>")
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")
#         self.current_redaction = None  # Clear any leftover boxes


#     def activate_black_rectangle_tool(self):
#         """Activate the filled rectangle drawing tool."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         self.deactivate_tools()
#         self.is_drawing_filled_rect = True
#         self.is_drawing_hollow_rect = False
#         self.highlight_mode = False
#         self.canvas.bind("<Button-1>", self.start_blackrectangle_drawing)
#         self.canvas.bind("<B1-Motion>", self.draw_blackrectangle_preview)
#         self.canvas.bind("<ButtonRelease-1>", self.finish_blackfilled_rectangle)

#     def start_blackrectangle_drawing(self, event):
#         """Start drawing a rectangle (for hollow/filled tools)."""
#         self.start_x = self.canvas.canvasx(event.x)
#         self.start_y = self.canvas.canvasy(event.y)
#         if self.current_rectangle:
#             self.canvas.delete(self.current_rectangle)
#         outline_color = "black"
#         fill_color = "" if self.is_drawing_hollow_rect else "black"
#         self.current_rectangle = self.canvas.create_rectangle(
#             self.start_x, self.start_y, self.start_x + 1, self.start_y + 1,
#             outline=outline_color, fill=fill_color, width=3, tags="annotation_preview")

#     def draw_blackrectangle_preview(self, event):
#         """Show a preview of the rectangle while dragging."""
#         if self.current_rectangle:
#             self.canvas.delete(self.current_rectangle)
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
#         outline_color = "black"
#         fill_color = "" if self.is_drawing_hollow_rect else "black"
#         self.current_rectangle = self.canvas.create_rectangle(
#             self.start_x, self.start_y, end_x, end_y,
#             outline=outline_color, fill=fill_color, width=3, tags="annotation_preview")

#     def finish_blackfilled_rectangle(self, event):
#         """Finish drawing the filled rectangle and add it to annotations."""
#         self.finish_blackrectangle(event, filled=True)

#     def finish_blackrectangle(self, event, filled):
#         """Finish drawing a rectangle and add it to annotations."""
#         end_x = self.canvas.canvasx(event.x)
#         end_y = self.canvas.canvasy(event.y)
        
#         # Ensure coordinates are properly ordered (top-left to bottom-right)
#         x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
#         x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)
        
#         # Delete the preview rectangle
#         if self.current_rectangle:
#             self.canvas.delete(self.current_rectangle)
        
#         # Create visual rectangle on canvas
#         outline_color = "black"
#         fill_color = "" if not filled else "black"
#         rect_id = self.canvas.create_rectangle(
#             x1, y1, x2, y2,
#             outline=outline_color, fill=fill_color, width=3, tags="annotation")
        
#         # Store rectangle data (in original PDF coordinates)
#         rect_data = {
#             'type': 'rectangle',
#             'page': self.current_page,
#             'x1': x1 / self.zoom_factor,
#             'y1': y1 / self.zoom_factor,
#             'x2': x2 / self.zoom_factor,
#             'y2': y2 / self.zoom_factor,
#             'filled': filled,
#             'id': rect_id,
#             'color': "black"
#         }
        
#         self.rectangles.append(rect_data)
#         self.annotations.append(rect_data)
#         self.change_redact_history.append(('add_annotation', rect_data))
#         self.annotation_is_available = True
#         self.deactivate_tools()


#     def undo_blackrect(self):
#         print("Undoing the last change...",self.change_redact_history)
#         if not self.change_redact_history:
#             return
#         last_action = self.change_redact_history.pop()
#         action_type = last_action[0]               
#         if action_type == "add_annotation":
#             # New code for undoing line, arrow, rectangle, and ellipse annotations
#             annotation_data = last_action[1]
#             annotation_type = annotation_data.get('type')        
#             # Remove from canvas
#             if 'id' in annotation_data:
#                 self.canvas.delete(annotation_data['id'])       
#             if annotation_type == 'rectangle':
#                 self.rectangles = [rect for rect in self.rectangles if rect != annotation_data]
#                 if self.annotation_listed[-1]=="rectangle":
#                     self.annotation_listed.pop()
#             # Remove from annotations list
#             self.annotations = [ann for ann in self.annotations 
#                             if not (isinstance(ann, dict) and ann.get('id') == annotation_data.get('id'))]
#             self.render_page(self.current_page)

#         else:
#             print(f"Unknown action type: {action_type}")