import os
import io
import math
import cv2
import numpy as np
import cairosvg
import fitz
import textwrap
from xml.etree import ElementTree as ET
from PIL import Image, ImageTk, ImageOps
import requests
from urllib.parse import urlparse
from duplicate_window import DuplicateStickyNotesPDFApp
import socket
import threading
import sys
from protocol_handler import ProtocolHandler
import customtkinter as ctk
from tkinter import filedialog, messagebox


class StickyNotesPDFApp:
    SOCKET_PORT = 65432

    def __init__(self, root):
        self.root = root
        self.root.title("Atic PDF Editor Screen")
        icon_path = os.path.join(os.path.dirname(__file__), '..', 'assets', 'Atic.png')
        self.root.iconbitmap(self.set_window_icon(icon_path))
        self.zoom_factor = 1.0
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
        self.redactions = []  # To store redaction info (coordinates)
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
        self.create_widgets()
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<Motion>", self.on_mouse_hover)
        self.root.bind("<Left>", self.prev_page)  # Left arrow for previous page
        self.root.bind("<Right>", self.next_page)  # Right arrow for next page
        self.active_tooltip = None
        self.page_width = 0
        self.page_height = 0
        self.duplicate_windows = []
        self.root.protocol("WM_DELETE_WINDOW", self.close_main_window)
        self.setup_ipc_server()
        self.temp_file_path = None
        self.server_url = "https://idms-backend.blockchaincloudapps.com/api/v1/uploads/file-annotations"

        if len(sys.argv) > 1:
            pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
            self.handle_url(pdf_url)

        
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

        # def load_image(relative_path, size=(25, 25)):
        #     if getattr(sys, 'frozen', False):
        #         base_dir = sys._MEIPASS
        #     else:
        #         base_dir = os.path.dirname(os.path.abspath(__file__))
        #     full_path = os.path.join(base_dir, relative_path)
        #     if relative_path.lower().endswith('.svg'):
        #         png_data = cairosvg.svg2png(url=full_path)
        #         image = Image.open(io.BytesIO(png_data))
        #     else:
        #         image = Image.open(full_path)
        #     image = image.resize(size, Image.LANCZOS)
        #     try:
        #         return ctk.CTkImage(light_image=image, dark_image=image, size=size)
        #     except:
        #         return ImageTk.PhotoImage(image)
                
        self.icons = {
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
        }

        button_configs = [
            {"image": self.icons['selectarrow'], "command": self.activate_selection_mode, "tooltip": "Zoom Selected Area"},
            {"image": self.icons['refresh_pdf'], "command": self.refresh, "tooltip": "Refresh Page"},
            {"image": self.icons['load_pdf'], "command": self.load_pdf, "tooltip": "Load PDF"},
            {"image": self.icons['new_window'], "command": lambda: self.create_duplicate_window(fileurl), "tooltip": "New Window"},
            {"image": self.icons['zoom_out'], "command": self.zoom_out, "tooltip": "Zoom Out"},
            {"image": self.icons['zoom_in'], "command": self.zoom_in, "tooltip": "Zoom In"},
            {"image": self.icons['zoom_area'], "command": self.toggle_zoom_in_area_mode, "tooltip": "Zoom Area"},
            {"image": self.icons['prev_page'], "command": self.prev_page, "tooltip": "Previous Page"},
            {"image": self.icons['next_page'], "command": self.next_page, "tooltip": "Next Page"},
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
            {"image": self.icons['filled_text'], "command": self.add_text_with_background, "tooltip": "Add Text stamp"},
            {"image": self.icons['free_line'], "command": self.toggle_drawing, "tooltip": "Free Hand Line", "instance_var": "draw_button"},
            {"image": self.icons['filled_polygon'], "command": self.toggle_filled_polygon_mode, "tooltip": "Draw Filled Polygon", "instance_var": "filled_polygon_button"},
            {"image": self.icons['hollow_polygon'], "command": self.toggle_hollow_polygon_mode, "tooltip": "Draw Hollow Polygon", "instance_var": "hollow_polygon_button"},
            {"image": self.icons.get('image'), "command": lambda: self.attach_image_to_pdf(), "tooltip": "Attach Image"},
            {"image": self.icons['straightline'], "command": self.activate_line_tool, "tooltip": "Draw Straight Line"},
            {"image": self.icons['arrow'], "command": self.activate_arrow_tool, "tooltip": "Draw Arrow"},
            {"image": self.icons['hollow_rectangle'], "command": self.activate_hollow_rectangle_tool, "tooltip": "Draw hollow rectangle"},
            {"image": self.icons['filled_rectangle'], "command": self.activate_filled_rectangle_tool, "tooltip": "filled rectangle"},
            {"image": self.icons['hollow_ellipse'], "command": self.activate_hollow_circle_tool, "tooltip": "Draw Hollow Ellipse"},
            {"image": self.icons['filled_ellipse'], "command": self.activate_filled_circle_tool, "tooltip": "Draw Filled Ellipse"},
            {"image": self.icons['redact'], "command": self.toggle_redaction_mode, "tooltip": "Add redaction"},
            {"image": self.icons['removeredact'], "command": self.remove_black_boxes, "tooltip": "remove redaction"},
        ]
        current_frame = ctk.CTkFrame(toolbar)
        current_frame.pack(fill=ctk.X)
        buttons_in_row = 0

        for config in button_configs:
            if buttons_in_row >= 24:  # Start a new line
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

        
        canvas_frame = ctk.CTkFrame(self.root)
        canvas_frame.pack(fill=ctk.BOTH, expand=True)

        self.thumbnail_frame = ctk.CTkFrame(canvas_frame, width=175, fg_color="lightgray")
        self.thumbnail_frame.pack(side=ctk.LEFT, fill=ctk.Y)

        self.thumbnail_canvas = ctk.CTkCanvas(self.thumbnail_frame, bg="lightgray", width=250)
        self.thumbnail_scrollbar = ctk.CTkScrollbar(self.thumbnail_frame, orientation="vertical", command=self.thumbnail_canvas.yview)
        self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
        self.thumbnail_canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
        self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        self.thumbnail_canvas.bind("<MouseWheel>", self.on_thumbnail_scroll)
        self.inner_thumbnail_frame = ctk.CTkFrame(self.thumbnail_canvas, fg_color="lightgray")
        self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
        self.inner_thumbnail_frame.bind("<Configure>", lambda e: self.update_scroll_region())
        self.canvas = ctk.CTkCanvas(canvas_frame, bg="lightgray", width=1050, height=750)
        self.h_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="horizontal", command=self.canvas.xview)
        self.v_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="vertical", command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
        self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
        self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        self.canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
        self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
        self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
        

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

    def ipc_listener(self):
        """Listen for incoming URLs and handle them."""
        while True:
            conn, _ = self.ipc_socket.accept()
            with conn:
                data = conn.recv(1024).decode("utf-8")
                if data:
                    self.root.after(0, self.handle_url, data)

    def send_to_running_instance(self, url):
        """Send the URL to the running instance."""
        try:
            with socket.create_connection(("localhost", self.SOCKET_PORT)) as client_socket:
                client_socket.sendall(url.encode("utf-8"))
        except socket.error:
            print("Failed to send URL to running instance.")

    def handle_url(self, url):
        """Handle a new URL (load the PDF)."""
        try:
            self.load_pdf(url)
        except Exception as e:
            print(f"Failed to load PDF: {e}")

    def update_scroll_region(self):
        """Ensures that the scroll region updates properly when thumbnails are added."""
        self.inner_thumbnail_frame.update_idletasks()  # Ensure layout updates first
        self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))

    # def load_pdf(self, file_path=None):
    #     if not file_path:
    #         file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
    #     try:
    #         parsed = urlparse(file_path)
    #         if parsed.scheme in ('http', 'https'):
    #             response = requests.get(file_path)
    #             response.raise_for_status()  # Raise an exception for bad status codes
    #             pdf_data = response.content
    #             self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
    #         else:
    #             self.pdf_document = fitz.open(file_path)
            
    #         if len(self.pdf_document) == 0:
    #             raise ValueError("The PDF has no pages.")
            
    #         # Reset the current page and ensure it's valid
    #         global fileurl
    #         fileurl = file_path
    #         self.pdf_path = file_path
    #         self.current_page = 0
    #         self.page_drawings = {}
    #         self.is_inverted = False
    #         self.text_annotations.clear()  # Clear annotations to avoid mismatches
    #         self.render_thumbnails()
    #         self.render_page(self.current_page)
    #         self.update_thumbnail_selection()
    #     except Exception as e:
    #         messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
    #         self.pdf_document = None
    #         self.current_page = None

    #     # For getting the file name in case needed
    #     global filename
    #     global edit_file_name
    #     global folderpath
    #     try:
    #         filename = file_path.split('/')[-1]
    #         beforeexe = filename.split('.')[0]
    #         edit_file_name = beforeexe+ "_with_annotations.pdf"    
    #         folderpath = file_path.split('/api/assets/')[1]
    #     except:
    #         filename = file_path.split('\\')[-1]
    #         beforeexe = filename.split('.')[0]
    #         edit_file_name = beforeexe+ "_with_annotations.pdf"
    #         folderpath = file_path.split('/api/assets/')[1]
    #     print("file_path-------",file_path)
    #     print(filename)
    #     print("edit_file_name",edit_file_name)
    #     print("folder_pathfolder_path----",folderpath)

    def load_pdf(self, file_path=None):
        if not file_path:
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        
        if not file_path:
            print("No file selected")
            return

        print(f"Loading PDF from: {file_path}")

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
            fileurl = file_path
            self.pdf_path = file_path
            self.current_page = 0
            self.page_drawings = {}
            self.is_inverted = False
            self.text_annotations.clear()

            print("Rendering thumbnails...")
            self.render_thumbnails()

            print("Rendering first page...")
            self.render_page(self.current_page)

            print("Updating thumbnail selection...")
            self.update_thumbnail_selection()

        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
            print(f"Failed to load PDF: {e}")  # Debug print
            self.pdf_document = None
            self.current_page = None
        global filename
        global edit_file_name
        global folderpath
        try:
            filename = file_path.split('/')[-1]
            beforeexe = filename.split('.')[0]
            edit_file_name = beforeexe+ "_with_annotations.pdf"    
            folderpath = file_path.split('/api/assets/')[1]
        except:
            filename = file_path.split('\\')[-1]
            beforeexe = filename.split('.')[0]
            edit_file_name = beforeexe+ "_with_annotations.pdf"
            folderpath = file_path.split('/api/assets/')[1]
        print("file_path-------",file_path)
        print(filename)
        print("edit_file_name",edit_file_name)
        print("folder_pathfolder_path----",folderpath)

    # def render_thumbnails(self):
    #     """Render the thumbnails of all PDF pages with fixed dimensions."""
    #     if not self.pdf_document:
    #         return

    #     # Clear existing widgets
    #     for widget in self.inner_thumbnail_frame.winfo_children():
    #         widget.destroy()

    #     self.thumbnails = []  # Clear any previously loaded thumbnails
    #     self.thumbnail_labels = []  # List to store thumbnail labels for styling

    #     thumbnail_width = 150
    #     thumbnail_height = 200

    #     for page_number in range(len(self.pdf_document)):
    #         page = self.pdf_document.load_page(page_number)
    #         pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
    #         img = Image.open(io.BytesIO(pix.tobytes("png")))

    #         # Resize and crop the image
    #         img_resized = ImageOps.fit(img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
    #         img_tk = ImageTk.PhotoImage(img_resized)
    #         self.thumbnails.append(img_tk)

    #         # Create a frame for the thumbnail
    #         frame = ctk.CTkFrame(self.inner_thumbnail_frame, fg_color="lightgray", corner_radius=10)
    #         frame.pack(pady=5, padx=20)

    #         # Add the thumbnail label
    #         label = ctk.CTkLabel(frame, image=img_tk, text="")
    #         label.pack()

    #         # Bind click event to select the page (use a default function to fix lambda binding issue)
    #         frame.bind("<Button-1>", self.create_page_selection_handler(page_number))
    #         label.bind("<Button-1>", self.create_page_selection_handler(page_number))

    #         # Save the frame for styling
    #         self.thumbnail_labels.append(frame)

    #     self.update_thumbnail_selection()
    #     self.inner_thumbnail_frame.update_idletasks()
    #     self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
######################################################################################################
    # def render_thumbnails(self):
    #     """Render the thumbnails of all PDF pages with fixed dimensions and page numbers."""
    #     if not self.pdf_document:
    #         return

    #     # Clear previous thumbnails
    #     for widget in self.inner_thumbnail_frame.winfo_children():
    #         widget.destroy()

    #     self.thumbnails = []  
    #     self.thumbnail_labels = []

    #     thumbnail_width = 150
    #     thumbnail_height = 200
    #     for page_number in range(len(self.pdf_document)):
    #         print("page_number - ",page_number)
    #         try:
    #             page = self.pdf_document.load_page(page_number)
    #             pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))  # Scale down for thumbnails
                
    #             img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
    #             img.thumbnail((thumbnail_width, thumbnail_height), Image.LANCZOS)

    #             photo = ImageTk.PhotoImage(img)
    #             label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
    #             label.image = photo  # Keep a reference to avoid garbage collection
    #             label.pack(pady=5, padx=20)
    #             label.bind("<Button-1>", self.create_page_selection_handler(page_number))
    #             self.thumbnails.append(label)
    
    #         except Exception as e:
    #             print(f"Error rendering page {page_number}: {e}")

    #     # Update the canvas scroll region
    #     self.inner_thumbnail_frame.update_idletasks()
    #     self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))

    # def render_thumbnails(self):
    #     """Render thumbnails asynchronously for better performance on large PDFs."""
    #     if not self.pdf_document:
    #         print("No PDF document loaded for thumbnails.")
    #         return

    #     print("Rendering thumbnails...")

    #     # Clear previous thumbnails
    #     for widget in self.inner_thumbnail_frame.winfo_children():
    #         widget.destroy()

    #     self.thumbnails = []
    #     self.thumbnail_labels = []
    #     self.thumbnail_cache = {}

    #     # Set optimized thumbnail size
    #     thumbnail_width = 100  
    #     thumbnail_height = 150  
    #     total_pages = len(self.pdf_document)

    #     def load_thumbnails():
    #         for page_number in range(total_pages):
    #             if page_number in self.thumbnail_cache:
    #                 continue
    #             try:
    #                 page = self.pdf_document.load_page(page_number)
    #                 print(f"Rendering thumbnail for page {page_number}...")

    #                 # Render at a slightly higher scale for better quality
    #                 pix = page.get_pixmap(matrix=fitz.Matrix(0.5, 0.5))  
    #                 img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)

    #                 # Resize with optimized resampling
    #                 img.thumbnail((thumbnail_width, thumbnail_height), Image.LANCZOS)
                    
    #                 photo = ImageTk.PhotoImage(img)

    #                 # Store reference to avoid garbage collection
    #                 self.thumbnail_cache[page_number] = photo

    #                 # Add thumbnail safely on the main thread
    #                 self.inner_thumbnail_frame.after(0, lambda p=page_number, ph=photo: add_thumbnail(p, ph))
    #             except Exception as e:
    #                 print(f"Error rendering thumbnail for page {page_number}: {e}")

    #         # Ensure scroll updates after all thumbnails are added
    #         self.inner_thumbnail_frame.after(500, self.update_scroll_region)

    #     def add_thumbnail(page_number, photo):
    #         """Add the rendered thumbnail to the UI."""
    #         print(f"Adding thumbnail for page {page_number + 1} (Total: {len(self.thumbnails) + 1})")

    #         label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
    #         label.image = photo  # Store reference
    #         label.pack(pady=5, padx=20)

    #         label.bind("<Button-1>", self.create_page_selection_handler(page_number))
    #         self.thumbnails.append(label)

    #     # Run thumbnail generation in a separate thread
    #     threading.Thread(target=load_thumbnails, daemon=True).start()

    def render_thumbnails(self):
        """Render thumbnails asynchronously for better performance on large PDFs."""
        if not self.pdf_document:
            print("No PDF document loaded for thumbnails.")
            return

        print("Rendering thumbnails...")
        
        # Clear previous thumbnails
        for widget in self.inner_thumbnail_frame.winfo_children():
            widget.destroy()

        self.thumbnails = []
        self.thumbnail_cache = {}  # Ensure proper caching
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
                        print(f"Rendering thumbnail for page {page_number}...")
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
        else:
            thumbnail_width = 150
            thumbnail_height = 200
            total_pages = len(self.pdf_document)

            def load_thumbnails():
                for page_number in range(total_pages):
                    if page_number in self.thumbnail_cache:
                        continue
                    try:
                        page = self.pdf_document.load_page(page_number)
                        print(f"Rendering thumbnail for page {page_number}...")
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
                self.inner_thumbnail_frame.after(1000, lambda: self.thumbnail_canvas.yview_moveto(0))
            def add_thumbnail(page_number, photo):
                """Add the rendered thumbnail to the UI."""
                print(f"Adding thumbnail for page {page_number + 1} (Total: {len(self.thumbnails) + 1})")

                label = ctk.CTkLabel(self.inner_thumbnail_frame, image=photo, text=f"Page {page_number + 1}")
                label.image = photo  # Store reference
                label.pack(pady=5, padx=45)

                label.bind("<Button-1>", self.create_page_selection_handler(page_number))
                self.thumbnails.append(label)


        threading.Thread(target=load_thumbnails, daemon=True).start()








####################################################################################################

    # def create_page_selection_handler(self, page_number):
    #     """Return a handler function to navigate to the selected page."""
    #     def handler(event):
    #         print(f"Thumbnail {page_number} clicked.")  # Debug log
    #         self.select_page(page_number)
    #     return handler

    def create_page_selection_handler(self, page_number):
        """Return a handler function to navigate to the selected page."""
        def handler(event):
            self.select_page(page_number)  # Ensure page selection updates UI
            self.update_thumbnail_selection()  # Ensure thumbnails update
        return handler


    # def update_thumbnail_selection(self):
    #     """Update the highlight of the selected thumbnail."""
    #     if not self.thumbnail_labels:
    #         print("No thumbnails to update.")  # Debug log
    #         return
    #     if self.thumbnail_labels:
    #         self.thumbnail_labels[0].configure(border_color="#FFA500", border_width=3)

    #     for i, frame in enumerate(self.thumbnail_labels):
    #         if i == self.current_page:
    #             frame.configure(border_color="#FFA500", border_width=3)  # Highlight
    #         else:
    #             frame.configure(border_color="lightgray", border_width=1)
    #     self.inner_thumbnail_frame.update_idletasks()

    def update_thumbnail_selection(self):
        """Update the highlight of the selected thumbnail."""
        if not self.thumbnails:
            print("No thumbnails to update.")  # Debug log
            return

        for label in self.thumbnails:
            label.configure(border_color="gray", border_width=1)  # Reset all thumbnails

        if 0 <= self.current_page < len(self.thumbnails):
            self.thumbnails[self.current_page].configure(border_color="#FFA500", border_width=3)  # Highlight selected page


    def select_page(self, page_number):
        """Navigate to the selected page."""
        self.current_page = page_number
        print(f"Selected page: {self.current_page}")  # Debug log
        self.render_page(page_number)
        self.update_thumbnail_selection()

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
        self.duplicate_windows.append(duplicate_root)

        def on_close():
            self.duplicate_windows.remove(duplicate_root)
            duplicate_root.destroy()

        duplicate_root.protocol("WM_DELETE_WINDOW", on_close)

    def close_main_window(self):
        """Closes the main window only if there are no duplicate windows open."""
        if self.duplicate_windows:
            messagebox.showerror("Warning", "Please close all duplicate windows before exiting the main window.")
        else:
            self.root.destroy()
    def zoom_in(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.zoom_factor += 0.2
        self.render_page(self.current_page)
    def zoom_out(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.zoom_factor > 0.4:
            self.zoom_factor -= 0.2
            self.render_page(self.current_page)
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

    def refresh(self):
        """
        Prompts the user to save the file and reloads the PDF if confirmed.
        If the user declines, nothing happens.
        """
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        
        response = messagebox.askyesnocancel("Confirm", "Do you want to save the file before refreshing it?")
        
        if response is None:
            # User clicked 'X' or 'Cancel', do nothing
            return
        elif response:
            # User clicked 'Yes'
            try:
                self.save_pdf()
                self.load_pdf(self.pdf_path)
            except Exception as e:
                messagebox.showerror("Error", f"An error occurred during refresh: {e}")
        else:
            # User clicked 'No', just refresh without saving
            self.load_pdf(self.pdf_path)

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


    def render_page(self, page_number):
        """Render a PDF page to the canvas with the current zoom factor."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        # Load and render the PDF page
        print("self.change_history - ",self.change_history)
        print("self.sticky_notes - ",self.sticky_notes)
        print("textself.redactions - ",self.redactions)
        print("text_annotations - ",self.text_annotations)
        page = self.pdf_document.load_page(page_number)
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
        # Redraw lines
        self.redraw_polygons()

    def update_scrollbars(self):
        """Enable or disable scrolling based on page size and window size."""
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()

        if self.pdf_document:
            page = self.pdf_document[self.current_page]
            zoom_matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
            page_rect = page.rect * zoom_matrix  # Get scaled page size

            page_width = page_rect.width
            page_height = page_rect.height

            # Enable/Disable horizontal scrollbar
            if page_width <= canvas_width:
                self.canvas.configure(xscrollcommand="")
                self.h_scrollbar.pack_forget()
            else:
                self.canvas.configure(xscrollcommand=self.h_scrollbar.set)
                self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)

            # Enable/Disable vertical scrollbar
            if page_height <= canvas_height:
                self.canvas.configure(yscrollcommand="")
                self.v_scrollbar.pack_forget()
            else:
                self.canvas.configure(yscrollcommand=self.v_scrollbar.set)
                self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)


    def redraw_polygons(self):
        """Redraw polygons on the canvas."""
        for mode, points, polygon_id in self.polygons:
            if len(points) % 2 != 0:
                continue  # Skip malformed polygons
            scaled_points = [(px * self.zoom_factor, py * self.zoom_factor) for px, py in zip(points[::2], points[1::2])]
            if mode == "filled":
                self.canvas.create_polygon(scaled_points, fill="blue", outline="black", tags="polygon")
            elif mode == "hollow":
                self.canvas.create_polygon(scaled_points, fill="", outline="red", tags="polygon")

    def on_mouse_scroll(self, event):
        """Handles vertical scrolling."""
        if self.page_height > self.canvas.winfo_height():  # Scroll only if page is taller
            self.canvas.yview_scroll(-1 * (event.delta // 120), "units")

    def on_shift_mouse_scroll(self, event):
        """Handles horizontal scrolling when Shift is held."""
        if self.page_width > self.canvas.winfo_width():  # Scroll only if page is wider
            self.canvas.xview_scroll(-1 * (event.delta // 120), "units")

    def on_thumbnail_scroll(self, event):
        """Handle vertical scrolling in the thumbnail panel using the mouse wheel."""
        self.thumbnail_canvas.yview_scroll(-1 * (event.delta // 120), "units")

    def enable_sticky_note_mode(self):
        """Activate sticky note mode."""
        self.sticky_note_mode = True
        self.highlight_mode = False

        # Unbind previous actions and bind the sticky note click action
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.canvas.bind("<Button-1>", self.on_canvas_click)

    def redraw_sticky_notes(self):
        """Redraw sticky notes after rendering the page."""
        self.canvas.delete("sticky_note")
        emoji_fill = "white" if self.is_inverted else "black"
        for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                self.canvas.create_image(
                    x_position, y_position,
                    image=self.icons['thumb_pin'],  # Use the sticky note icon
                    anchor="center",  # Center the image
                    tags="sticky_note"
                )
  
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

        # Safely retrieve the icon for sticky notes
        sticky_icon = self.icons.get("thumb_pin")
        if sticky_icon:
            self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
        else:
            print("Warning: 'sticky_note' icon not found.")  # Refresh to apply the changes


    
    # def on_canvas_click(self, event):
    #     """Add a sticky note at the clicked position on the canvas."""
    #     if not self.pdf_document or not self.sticky_note_mode:
    #         return

    #     x = self.canvas.canvasx(event.x)
    #     y = self.canvas.canvasy(event.y)

    #     if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
    #         return

    #     note_text = self.ask_for_note_text(x, y, "Enter Sticky Note")
    #     if not note_text:
    #         return

    #     x_scaled = x / self.zoom_factor
    #     y_scaled = y / self.zoom_factor

    #     self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
    #     self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))

    #     # Safely retrieve the icon for sticky notes
    #     sticky_icon = self.icons.get("thumb_pin")
    #     if sticky_icon:
    #         self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
    #     else:
    #         print("Warning: 'sticky_note' icon not found.")

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
        

    def undo_change(self):
        if not self.change_history:
            return

        last_action = self.change_history.pop()
        action_type = last_action[0]

        if action_type == "sticky_note":
            _, page, x_scaled, y_scaled, _ = last_action
            if (page, x_scaled, y_scaled) in self.sticky_notes:
                del self.sticky_notes[(page, x_scaled, y_scaled)]
                self.render_page(self.current_page)

        elif action_type in ("add_text", "add_text_bg"):
            _, page, x_scaled, y_scaled, text = last_action
            annotation_dict = (
                self.text_annotations if action_type == "add_text" else self.text_annotations_bg
            )
            if (page, x_scaled, y_scaled) in annotation_dict:
                del annotation_dict[(page, x_scaled, y_scaled)]
                page_obj = self.pdf_document[page]
                annot = page_obj.first_annot
                while annot:
                    # Match the annotation text content with the stored text
                    if annot.info and annot.info.get("contents") == text:
                        page_obj.delete_annot(annot)
                        break
                    annot = annot.next
                self.render_page(self.current_page)
       
        elif action_type == "highlight":
            _, page, annot_id = last_action
            page_obj = self.pdf_document[page]
            annot = page_obj.first_annot
            while annot:
                if annot.info.get('id') == annot_id:
                    page_obj.delete_annot(annot)
                    self.render_page(self.current_page)
                    break
                annot = annot.next

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
            if annot_id:
                self.change_history.append(("highlight", self.current_page, annot_id))
        except Exception as e:
            messagebox.showerror("Error", f"Failed to add highlight: {e}")
            return
        self.render_page(self.current_page)
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    # def on_mouse_hover(self, event):
    #     """Show sticky note text when hovering over emoji."""
    #     if not self.pdf_document:
    #         return
    #     x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)  # Adjust for scrolling
    #     tooltip_shown = False
    #     for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
    #         if page_num == self.current_page:
    #             x_position = x_scaled * self.zoom_factor
    #             y_position = y_scaled * self.zoom_factor
    #             if abs(x - x_position) < 20 and abs(y - y_position) < 20:  # Adjust hover sensitivity
    #                 if not tooltip_shown:
    #                     self.show_tooltip(event.x_root, event.y_root, text)  # Use root coordinates for tooltip
    #                     tooltip_shown = True
    #                 break
    #     if not tooltip_shown and getattr(self, "active_tooltip", None):
    #         self.active_tooltip.destroy()
    #         self.active_tooltip = None

    def on_mouse_hover(self, event):
        """Change cursor when hovering over a polygon or sticky note."""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        tooltip_shown = False

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
                if abs(x - x_position) < 20 and abs(y - y_position) < 20:  # Adjust hover sensitivity
                    if not tooltip_shown:
                        self.show_tooltip(event.x_root, event.y_root, text)  # Use root coordinates for tooltip
                        tooltip_shown = True
                    break
        # Reset cursor if not hovering over anything
        if not tooltip_shown:
            if self.active_tooltip:
                self.active_tooltip.destroy()
                self.active_tooltip = None
            self.canvas.config(cursor="")


    def show_tooltip(self, x, y, text):
        """Display the sticky note text as a tooltip."""
        if getattr(self, "active_tooltip", None):
            self.active_tooltip.destroy()
        wrapped_text = textwrap.fill(text, width=50)  # Ensuring the line ends at 50 characters
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

    def save_pdf(self, file_path=None):
        """Save the PDF with embedded sticky notes and upload directly to the server."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF document to save.")
            return
        try:
            # Create a temporary PDF to store annotations
            temp_pdf = fitz.open()
            for page in self.pdf_document:
                temp_pdf.insert_pdf(self.pdf_document, from_page=page.number, to_page=page.number)

            max_line_length = 50
            for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
                page = temp_pdf[page_num]
                marker_size = 12
                text_size = 10
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
                lines = self.wrap_text(text, max_line_length)
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
                    fill_opacity=0.5
                )

                # Insert wrapped text
                for i, line in enumerate(lines):
                    page.insert_text(
                        point=(x_scaled, y_scaled + text_offset + (i * text_size * 1.5)),
                        text=line,
                        fontsize=text_size,
                        color=(0, 0, 0)
                    )
            for page in temp_pdf:
                page.apply_redactions()
            # Save to memory buffer
            with io.BytesIO() as pdf_buffer:
                temp_pdf.save(pdf_buffer)
                pdf_buffer.seek(0)

                # Prepare file for upload
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
    
    def prev_page(self, event=None):
        """Go to the previous page in the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.current_page > 0:
            self.current_page -= 1
            self.render_page(self.current_page)

    def next_page(self, event=None):
        """Go to the next page in the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        if self.current_page < len(self.pdf_document) - 1:
            self.current_page += 1
            self.render_page(self.current_page)


    def rotate_90clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 90) % 360)
        self.render_page(self.current_page)

    # def rotate_90clockwise(self):
    #     """Rotate the current page clockwise."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
    #     self.page_rotation = (self.page_rotation + 90) % 360  # Update stored rotation
    #     self.render_page(self.current_page, self.page_rotation)

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
        """Toggle the freehand drawing mode and embed strokes into the PDF."""
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
        """Start recording a freehand drawing stroke."""
        self.freehand_stroke = [(self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))]
    
    def draw_freehand_line(self, event):
        """Draw a freehand stroke on the canvas in real-time."""
        if not hasattr(self, "freehand_stroke"):
            return
        
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        self.freehand_stroke.append((x, y))
        
        if len(self.freehand_stroke) > 1:
            x1, y1 = self.freehand_stroke[-2]
            x2, y2 = self.freehand_stroke[-1]
            self.canvas.create_line(x1, y1, x2, y2, fill="black", width=2)
    
    def finish_freehand_drawing(self, event):
        """Embed the drawn freehand stroke into the PDF."""
        if not hasattr(self, "freehand_stroke") or len(self.freehand_stroke) < 2:
            return
        
        page = self.pdf_document[self.current_page]
        scaled_stroke = [(x / self.zoom_factor, y / self.zoom_factor) for x, y in self.freehand_stroke]
        
        for i in range(len(scaled_stroke) - 1):
            x1, y1 = scaled_stroke[i]
            x2, y2 = scaled_stroke[i + 1]
            page.draw_line(p1=(x1, y1), p2=(x2, y2), width=2, color=(0, 0, 0))
        
        self.change_history.append(("freehand", self.current_page, scaled_stroke))
        del self.freehand_stroke
        self.toggle_drawing()
        self.render_page(self.current_page)

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
            self.canvas.unbind("<Button-1>")
            self.embed_polygons_in_pdf()
        else:
            # Deactivate hollow mode if active
            if self.polygon_mode == "hollow":
                self.hollow_polygon_button.configure(text="")

            # Activate filled mode
            self.filled_polygon_button.configure(text="#")
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
            self.polygon_created = False  # Reset creation flag
            self.canvas.unbind("<Button-1>")
            self.embed_polygons_in_pdf()
        else:
            # Deactivate filled mode if active
            if self.polygon_mode == "filled":
                self.filled_polygon_button.configure(text="")

            # Activate hollow mode
            self.hollow_polygon_button.configure(text="#")
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



    def on_canvas_polygon_click(self, event):
        """Handle canvas clicks for creating or modifying polygons."""
        if not self.polygon_mode:
            return

        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

        if self.current_page not in self.page_drawings:
            self.page_drawings[self.current_page] = []

        # Check if clicking inside an existing polygon
        for idx, drawing in enumerate(self.page_drawings[self.current_page]):
            if len(drawing) != 3:
                print(f"Skipping invalid entry at index {idx}: {drawing}")
                continue
            mode, points, polygon_id = drawing

            if self.is_point_inside_polygon(x, y, points):
                self.canvas.config(cursor="hand2")  # Change cursor when hovering over polygon

                # Dynamic selection radius based on zoom level
                zoom_adjusted_radius = max(10, 15 * self.zoom_factor)

                # Check if dragging a vertex
                for i in range(0, len(points), 2):
                    vx, vy = points[i], points[i + 1]
                    if abs(vx - x) < zoom_adjusted_radius and abs(vy - y) < zoom_adjusted_radius:
                        self.dragging_polygon = (idx, i // 2)
                        self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
                        self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                        self.canvas.config(cursor="fleur")  # Change cursor to grabbing hand when dragging
                        return

                # Dragging entire polygon
                self.dragging_polygon = (idx, None)
                self.start_drag_x, self.start_drag_y = x, y
                self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
                self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                self.canvas.config(cursor="fleur")  # Change cursor to grabbing hand when dragging
                return

        # Start a new polygon if no existing polygon was selected
        if self.start_point is None:
            self.start_point = (x, y)
            points = self.generate_polygon_points(x, y, self.polygon_size, 5)
            polygon_id = self.canvas.create_polygon(
                points,
                fill="blue" if self.polygon_mode == "filled" else "",
                outline="black" if self.polygon_mode == "filled" else "red",
                tags=("polygon",)
            )
            self.page_drawings[self.current_page].append((self.polygon_mode, points, polygon_id))
        else:
            self.start_point = None

        self.redraw_polygons()



    # def on_mouse_hover(self, event):
    #     """Change cursor to hand when hovering over a polygon."""
    #     x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

    #     for _, points, _ in self.page_drawings.get(self.current_page, []):
    #         if self.is_point_inside_polygon(x, y, points):
    #             self.canvas.config(cursor="hand2")  # Change to hand when hovering over polygon
    #             return

    #     self.canvas.config(cursor="")  # Reset cursor when not hovering over a polygon




    def embed_polygons_in_pdf(self):
        """Embed polygons directly as vector graphics in the PDF with proper scaling."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        zoom_matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
        for drawing in self.page_drawings[self.current_page]:
            if len(drawing) != 3:
                print(f"Skipping invalid entry: {drawing}")
                continue
            mode, points, _ = drawing
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


    def on_polygon_drag_entire(self, event):
        """Handle dragging to move the entire polygon."""
        if not hasattr(self, 'dragging_polygon'):
            return
        idx, _ = self.dragging_polygon
        mode, points, polygon_id = self.page_drawings[self.current_page][idx]

        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        dx, dy = x - self.start_drag_x, y - self.start_drag_y

        # Update points and redraw polygon
        for i in range(0, len(points), 2):
            points[i] += dx
            points[i + 1] += dy
        self.canvas.coords(polygon_id, points)

        # Update start drag position
        self.start_drag_x, self.start_drag_y = x, y

    def on_polygon_drag_vertex(self, event):
        """Handle dragging a single vertex of the polygon smoothly."""
        if not hasattr(self, 'dragging_polygon'):
            return

        idx, vertex_idx = self.dragging_polygon
        mode, points, polygon_id = self.page_drawings[self.current_page][idx]

        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

        # Introduce a snapping threshold for controlled reshaping
        snap_threshold = 5  # Pixels
        original_x, original_y = points[vertex_idx * 2], points[vertex_idx * 2 + 1]

        # Only apply movement if the displacement exceeds the threshold
        if abs(x - original_x) > snap_threshold or abs(y - original_y) > snap_threshold:
            points[vertex_idx * 2] = x
            points[vertex_idx * 2 + 1] = y
            self.canvas.coords(polygon_id, points)


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
        user_response = messagebox.askyesno(
            "Confirm Position",
            "Are you satisfied with the current position and size of the image?"
        )

        if not user_response:
            return
        try:
            page = self.pdf_document[self.current_page]
            rotation_angle = page.rotation  # Get the current page rotation
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
            img_bytes = open(img_path, "rb").read()  # Read the original image file as bytes
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
        """Add plain text to the PDF at a clicked position."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.canvas.bind("<Button-1>", self.on_add_text_click)
        self.add_text_mode = True

    def on_add_text_click(self, event):
        """Handle adding plain text to the clicked position."""
        if not self.pdf_document or not self.add_text_mode:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return
        text = self.ask_for_note_text(x, y,"Add Text")
        if not text:
            return
        wrapped_text = "\n".join(textwrap.wrap(text, width=30))
        page = self.pdf_document[self.current_page]
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        page.insert_text((x_scaled, y_scaled), wrapped_text, fontsize=16, color=(0, 0, 0))
        self.text_annotations[(self.current_page, x_scaled, y_scaled)] = text
        self.change_history.append(("add_text", self.current_page, x_scaled, y_scaled, text))
        self.render_page(self.current_page)
        self.add_text_mode = False
        self.canvas.unbind("<Button-1>")

    def add_text_with_background(self):
        """Add text with a background color to the PDF at a clicked position."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.canvas.bind("<Button-1>", self.on_add_text_with_bg_click)
        self.add_text_bg_mode = True

    def on_add_text_with_bg_click(self, event):
        """Handle adding text with a background to the clicked position."""
        if not self.pdf_document or not self.add_text_bg_mode:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return
        text = self.ask_for_note_text(x, y,"Add Text with Background")
        if not text:
            return
        wrapped_text = "\n".join(textwrap.wrap(text, width=30))
        page = self.pdf_document[self.current_page]
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        fontsize = 16
        text_lines = wrapped_text.split("\n")
        max_width = max(len(line) for line in text_lines) * fontsize * 0.6
        text_height = fontsize * 1.2 * len(text_lines)
        page.draw_rect(
                    fitz.Rect(
                        x_scaled, y_scaled, x_scaled + max_width + 10, y_scaled + text_height + 15
                    ),
                    color=(0, 1, 1),
                    fill=(0, 1, 1),)
        page.insert_text(
            (x_scaled + 7, y_scaled + 20),  # Box dimensions
            wrapped_text,
            fontsize=16,
            color=(0, 0, 0),)  # Text color

        self.text_annotations_bg[(self.current_page, x_scaled, y_scaled)] = text
        self.change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, text))
        self.render_page(self.current_page)
        self.add_text_bg_mode = False
        self.canvas.unbind("<Button-1>")


    def activate_line_tool(self):
        """Activate the straight line drawing tool."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
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
        self.deactivate_tools()
        self.is_drawing_arrow = True
        self.canvas.bind("<Button-1>", self.start_line)
        self.canvas.bind("<B1-Motion>", self.draw_line_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_arrow)

    def deactivate_tools(self):
        """Deactivate all tools."""
        self.is_drawing_line = False
        self.is_drawing_arrow = False
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    def start_line(self, event):
        """Start drawing a line or arrow."""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.current_line = None

    def draw_line_preview(self, event):
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
        """Finish drawing the line and embed it into the PDF."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        
        # Draw line on the canvas
        self.canvas.create_line(
            self.start_x, self.start_y, end_x, end_y,
            fill="red", width=3, tags="annotation"
        )

        # Embed the line into the PDF
        self.embed_line_or_arrow(self.start_x, self.start_y, end_x, end_y, is_arrow=False)
        self.deactivate_tools()

    def finish_arrow(self, event):
        """Finish drawing the arrow and embed it into the PDF."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        
        # Draw arrow on the canvas with a larger arrowhead
        self.canvas.create_line(
            self.start_x, self.start_y, end_x, end_y,
            fill="red", width=3, arrow=ctk.LAST, arrowshape=(16, 20, 6), tags="annotation"
        )

        # Embed the arrow into the PDF
        self.embed_line_or_arrow(self.start_x, self.start_y, end_x, end_y, is_arrow=True)
        self.deactivate_tools()

    def embed_line_or_arrow(self, start_x, start_y, end_x, end_y, is_arrow):
        """Embed a line or arrow directly into the PDF."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        
        page = self.pdf_document[self.current_page]
        # Convert canvas coordinates to PDF coordinates
        x1, y1 = start_x / self.zoom_factor, start_y / self.zoom_factor
        x2, y2 = end_x / self.zoom_factor, end_y / self.zoom_factor

        # Draw the main line
        page.draw_line(p1=(x1, y1), p2=(x2, y2), width=2, color=(1, 0, 0))  # Red color (RGB normalized)

        # If it's an arrow, add arrowhead
        if is_arrow:
            arrow_length = 12
            angle = math.atan2(y2 - y1, x2 - x1)
            # Calculate the points for the arrowhead
            arrow_x1 = x2 - arrow_length * math.cos(angle + math.pi / 6)
            arrow_y1 = y2 - arrow_length * math.sin(angle + math.pi / 6)
            arrow_x2 = x2 - arrow_length * math.cos(angle - math.pi / 6)
            arrow_y2 = y2 - arrow_length * math.sin(angle - math.pi / 6)

            # Draw the arrowhead lines
            page.draw_line(p1=(x2, y2), p2=(arrow_x1, arrow_y1), width=2, color=(1, 0, 0))
            page.draw_line(p1=(x2, y2), p2=(arrow_x2, arrow_y2), width=2, color=(1, 0, 0))

        # Append this change to the history
        self.change_history.append(("line_or_arrow", self.current_page, x1, y1, x2, y2, is_arrow))



    def activate_hollow_rectangle_tool(self):
        """Activate the hollow rectangle drawing tool."""
        self.deactivate_tools()
        self.is_drawing_hollow_rect = True
        self.is_drawing_filled_rect = False  # Ensure only one mode is active
        self.highlight_mode = False
        self.canvas.bind("<Button-1>", self.start_rectangle_drawing)
        self.canvas.bind("<B1-Motion>", self.draw_rectangle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_hollow_rectangle)

    def activate_filled_rectangle_tool(self):
        """Activate the filled rectangle drawing tool."""
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
            page.draw_rect(rect, color=(1, 0, 0), fill=(1, 0, 0))
        else:
            page.draw_rect(rect, color=(1, 0, 0), width=2)
        
        self.render_page(self.current_page)
        self.deactivate_tools()



    def activate_hollow_circle_tool(self):
        """Activate the hollow circle drawing tool."""
        self.deactivate_tools()
        self.is_drawing_hollow_circle = True
        self.canvas.bind("<Button-1>", self.start_circle)
        self.canvas.bind("<B1-Motion>", self.draw_circle_preview)
        self.canvas.bind("<ButtonRelease-1>", self.finish_hollow_circle)

    def activate_filled_circle_tool(self):
        """Activate the filled circle drawing tool."""
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
        """Show a preview of the circle while dragging."""
        if not hasattr(self, "is_drawing_hollow_circle"):  # Ensure attribute exists
            self.is_drawing_hollow_circle = False
        if not hasattr(self, "is_drawing_filled_circle"):
            self.is_drawing_filled_circle = False

        if self.current_circle:
            self.canvas.delete(self.current_circle)
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        radius = math.sqrt((end_x - self.start_x) ** 2 + (end_y - self.start_y) ** 2)  
        outline_color = "blue"
        fill_color = "" if self.is_drawing_hollow_circle else "blue"
        
        self.current_circle = self.canvas.create_oval(
            self.start_x - radius, self.start_y - radius, 
            self.start_x + radius, self.start_y + radius,
            outline=outline_color, fill=fill_color, width=2, tags="annotation"
        )

    def finish_hollow_circle(self, event):
        """Finish drawing the hollow circle and embed it in the PDF."""
        self.embed_circle_in_pdf(event, fill=False)

    def finish_filled_circle(self, event):
        """Finish drawing the filled circle and embed it in the PDF."""
        self.embed_circle_in_pdf(event, fill=True)

    def embed_circle_in_pdf(self, event, fill):
        """Embed the drawn circle into the PDF."""
        end_x = self.canvas.canvasx(event.x)
        end_y = self.canvas.canvasy(event.y)
        
        radius = math.sqrt((end_x - self.start_x) ** 2 + (end_y - self.start_y) ** 2)
        x_center, y_center = self.start_x / self.zoom_factor, self.start_y / self.zoom_factor
        radius /= self.zoom_factor  # Adjust radius for zoom factor
        
        page = self.pdf_document[self.current_page]
        circle_rect = fitz.Rect(
            x_center - radius, y_center - radius, 
            x_center + radius, y_center + radius
        )
        
        if fill:
            page.draw_oval(circle_rect, color=(0, 0, 1), fill=(0, 0, 1))  # Blue filled circle
        else:
            page.draw_oval(circle_rect, color=(0, 0, 1), width=2)  # Blue outline circle
        
        self.render_page(self.current_page)
        self.deactivate_tools()



    def activate_selection_mode(self):
        """Activate the zoom area tool."""
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
        if self.redaction_mode:
            self.deactivate_redact_tools()
        else:
            self.activate_redaction_mode()

    def activate_redaction_mode(self):
        """Ensure activation properly binds events and doesn't toggle incorrectly."""
        self.redaction_mode = True
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

        # Add redaction annotation (without applying)
        redact_annot = page.add_redact_annot(rect, fill=(0, 0, 0))
        # Store the redaction rectangle instead of annotation object
        self.redactions.append((self.current_page, rect))
        # Clear the preview outline
        if self.current_redaction:
            self.canvas.delete(self.current_redaction)
            self.current_redaction = None  # Reset to prevent lingering outlines
        self.render_page(self.current_page)
        self.deactivate_redact_tools()

        

    def remove_black_boxes(self):
        """Remove the most recent redaction annotation before applying them."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        if not self.redactions:
            return

        page = self.pdf_document[self.current_page]
        for i in range(len(self.redactions) - 1, -1, -1):
            page_number, rect = self.redactions[i]
            if page_number == self.current_page:
                annot = page.first_annot
                while annot:
                    next_annot = annot.next  # Get next annotation before deleting
                    if annot.rect == rect:
                        page.delete_annot(annot)
                        self.redactions.pop(i)  # Remove from stored list
                        self.render_page(self.current_page)
                        return  # Stop after removing one
                    annot = next_annot

        messagebox.showinfo("No Redactions", "No redactions left to remove.")




    # def remove_black_boxes(self):
    #     """Remove all black boxes (redactions) from the current page."""
    #     if not self.pdf_document or self.current_page is None:
    #         messagebox.showerror("Error", "No PDF loaded.")
    #         return
        
    #     page = self.pdf_document[self.current_page]
        # vector_rects = {}  # Stores black rectangles and their sequence number

        #     print(f"Checking page for black rectangles...")
        #     for p in page.get_drawings():  # Iterate through vector graphics
        #         if p["type"] == "s":  # Ignore strokes (no fill color)
        #             continue
        #         if p["fill_opacity"] != 1.0:  # Ignore transparent fills
        #             continue
        #         if p["fill"] != (0.0, 0.0, 0.0):  # Ignore non-black fills
        #             continue
        #         for item in p["items"]:
        #             if item[0] != "re":  # Ensure it's a rectangle
        #                 continue
        #             rect = fitz.Rect(item[1])  # Convert to a Rect object
        #             print(f"Found black rectangle: {rect}")
        #             vector_rects[rect] = p["seqno"]  # Store sequence number

        #     print(f"There are {len(vector_rects)} suspicious rectangles.")
    #     annotations = page.annots()
        
    #     # Remove all annotations that are black rectangles
    #     if annotations:
    #         print("Annotations:", annotations)
    #         for annot in annotations:
    #             print("Annot:", annot)
    #             if annot.rect and annot.info["subtype"] == "Redact":
    #                 print("Deleting annot:", annot)
    #                 page.delete_annot(annot)
        
    #     # Remove drawn black rectangles from redaction process
    #     to_remove = []
    #     for rect in self.redactions:
    #         try:
    #             for path in page.get_drawings():
    #                 for item in path["items"]:
    #                     if item[0] == "re":  # Check if it's a rectangle
    #                         drawn_rect = fitz.Rect(item[1])
    #                         if drawn_rect == rect:
    #                             page.draw_rect(drawn_rect, color=(1, 1, 1), fill=(1, 1, 1))  # Cover with white
    #                             to_remove.append(rect)
    #         except Exception as e:
    #             messagebox.showerror("Error", f"Failed to remove black box: {e}")
    #     print("To remove:", to_remove)
    #     for rect in to_remove:
    #         print("Removing rect:", rect)
    #         self.redactions.remove(rect)
        
    #     self.render_page(self.current_page)




    def remove_redaction(self):
        """Remove the last added redaction."""
        if not self.redactions:
            messagebox.showinfo("Info", "No redactions to remove.")
            return

        last_redaction = self.redactions.pop()
        
        if last_redaction is None:
            messagebox.showerror("Error", "Invalid redaction object.")
            return

        if not hasattr(last_redaction, "x"):
            messagebox.showerror("Error", "Redaction object is missing attributes.")
            return

        # Remove the redaction from the canvas
        self.canvas.delete(last_redaction)

        # Re-render the page to update the PDF view
        self.render_page(self.current_page)



    def deactivate_redact_tools(self):
        """Deactivate the redaction tool."""
        self.redaction_mode = False
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<ButtonRelease-1>")


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