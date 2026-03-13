import os
import tempfile
import io
import math
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
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.change_history = []
        self.sticky_notes = {}
        self.thumbnails = []
        self.canvas_bindings = {}
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
        self.active_tooltip = None
        self.page_width = 0
        self.page_height = 0
        self.duplicate_windows = []
        self.root.protocol("WM_DELETE_WINDOW", self.close_main_window)
        self.setup_ipc_server()

        if len(sys.argv) > 1:
            pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
            self.handle_url(pdf_url)

        self.temp_file_path = None
        self.server_url = "https://idms-api.blockchaincloudapps.com/upload/file"
    
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
                
        def change_svg_color(file_path, new_color, output_path=None):
            if getattr(sys, 'frozen', False):
                base_dir = sys._MEIPASS
            else:
                base_dir = os.path.dirname(os.path.abspath(__file__))
            full_file_path = os.path.join(base_dir, file_path)
            if not os.path.exists(full_file_path):
                raise FileNotFoundError(f"File not found: {full_file_path}")
            
            tree = ET.parse(full_file_path)
            root = tree.getroot()
            namespace = {'svg': 'http://www.w3.org/2000/svg'}
            for elem in root.findall(".//svg:path", namespace):
                elem.set('fill', new_color)
            
            # Write to temporary directory
            if not output_path:
                temp_dir = tempfile.gettempdir()
                output_path = os.path.join(temp_dir, os.path.basename(file_path))
            
            tree.write(output_path)
            return output_path


        # Change colors to white for most icons
        self.icons = {
            "load_pdf": load_image("assets/folder.svg"),
            "new_window": load_image("assets/new_window.svg"),
            "zoom_out": load_image("assets/zoom_out.svg"),
            "zoom_in": load_image("assets/zoom_in.svg"),
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
            "filled_polygon": load_image("assets/filledpolygon.svg"),
            "hollow_polygon": load_image("assets/hollowpolygon.svg"),
        }

        # Use a different variable name for the list of icons to process
        icon_files = [
            "assets/folder.svg",
            "assets/new_window.svg",
            "assets/zoom_out.svg",
            "assets/zoom_in.svg",
            "assets/prev_page.svg",
            "assets/next_page.svg",
            "assets/undo.svg",
            "assets/highlight.svg",
            "assets/note.svg",
            "assets/rotate_90.svg",
            "assets/rotate_180.svg",
            "assets/rotate_270.svg",
            "assets/fit_to_page.svg",
            "assets/width.svg",
            "assets/height.svg",
            "assets/ying_yang.svg",
            "assets/save.svg",
            "assets/Area.svg",
            "assets/line.svg",
            "assets/filledpolygon.svg",
            "assets/hollowpolygon.svg",
        ]

        # Change SVG colors for the list of icons
        for icon_file in icon_files:
            change_svg_color(icon_file, new_color="white")

        # Change `thumb_pin` icon color to yellow
        # change_svg_color("assets/note.svg", new_color="yellow", output_path="assets/thumb_pin_yellow.svg")

        # Update `thumb_pin` to point to the yellow version
        # self.icons["thumb_pin"] = load_image("assets/thumb_pin_yellow.svg", size=(24, 24))
        
        create_button(toolbar, image=self.icons['load_pdf'], command=self.load_pdf, tooltip_text="Load PDF")  #  text that is visible when hovered
        create_button(toolbar, image=self.icons['new_window'], command=lambda: self.create_duplicate_window(fileurl), tooltip_text="New Window")
        create_button(toolbar, image=self.icons['zoom_out'], command=self.zoom_out, tooltip_text="Zoom Out")
        create_button(toolbar, image=self.icons['zoom_in'], command=self.zoom_in, tooltip_text="Zoom In")
        create_button(toolbar, image=self.icons['zoom_area'], command=self.toggle_zoom_in_area_mode, tooltip_text="Zoom Area")
        create_button(toolbar, image=self.icons['prev_page'], command=self.prev_page, tooltip_text="Previous Page")
        create_button(toolbar, image=self.icons['next_page'], command=self.next_page, tooltip_text="Next Page")
        create_button(toolbar, image=self.icons['highlight'], command=self.enable_highlight_mode, tooltip_text="Highlight")
        create_button(toolbar, image=self.icons['sticky_note'], command=self.toggle_sticky_note_mode, tooltip_text="Sticky Note")
        create_button(toolbar, image=self.icons['undo'], command=self.undo_change, tooltip_text="Undo")
        create_button(toolbar, image=self.icons['rotate_90'], command=self.rotate_90clockwise, tooltip_text="Rotate 90° Right")
        create_button(toolbar, image=self.icons['rotate_180'], command=self.rotate_180clockwise, tooltip_text="Rotate 180° Right")
        create_button(toolbar, image=self.icons['rotate_270'], command=self.rotate_270clockwise, tooltip_text="Rotate 270° Right")
        create_button(toolbar, image=self.icons['best_fit'], command=self.best_fit, tooltip_text="Best Fit")
        create_button(toolbar, image=self.icons['best_width'], command=self.best_width, tooltip_text="Best Width")
        create_button(toolbar, image=self.icons['best_height'], command=self.best_height, tooltip_text="Best Height")
        create_button(toolbar, image=self.icons['invert_colors'], command=self.toggle_invert_colors, tooltip_text="Invert Colors")
        create_button(toolbar, image=self.icons['save_pdf'], command=self.save_pdf, tooltip_text="Save PDF")
        # self.draw_button = create_button(toolbar, image=self.icons['free_line'], command=self.toggle_drawing, tooltip_text="Free Hand Line")
        self.filled_polygon_button = create_button(toolbar, image=self.icons['filled_polygon'],command=self.toggle_filled_polygon_mode,tooltip_text="Draw a filled polygon")
        self.hollow_polygon_button = create_button(toolbar, image=self.icons['hollow_polygon'],command=self.toggle_hollow_polygon_mode,tooltip_text="Draw a hollow polygon")  

        canvas_frame = ctk.CTkFrame(self.root)
        canvas_frame.pack(fill=ctk.BOTH, expand=True)

        self.thumbnail_frame = ctk.CTkFrame(canvas_frame, width=150, fg_color="lightgray")
        self.thumbnail_frame.pack(side=ctk.LEFT, fill=ctk.Y)

        self.thumbnail_canvas = ctk.CTkCanvas(self.thumbnail_frame, bg="lightgray", width=200)
        self.thumbnail_scrollbar = ctk.CTkScrollbar(self.thumbnail_frame, orientation="vertical", command=self.thumbnail_canvas.yview)
        self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
        self.thumbnail_canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
        self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)

        self.inner_thumbnail_frame = ctk.CTkFrame(self.thumbnail_canvas, fg_color="lightgray")
        self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
        self.canvas = ctk.CTkCanvas(canvas_frame, bg="lightgray", width=1250, height=750)
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

    def load_pdf(self, file_path=None):
        if not file_path:
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        try:
            # Check if the file_path is a URL
            parsed = urlparse(file_path)
            if parsed.scheme in ('http', 'https'):
                # Download the PDF from URL
                response = requests.get(file_path)
                response.raise_for_status()  # Raise an exception for bad status codes
                pdf_data = response.content
                # Open PDF from memory buffer
                self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
            else:
                # Open local PDF file
                self.pdf_document = fitz.open(file_path)

            # Save the file path/URL for later use
            global fileurl
            fileurl = file_path
            self.pdf_path = file_path
            self.current_page = 0
            self.is_inverted = False
            self.render_thumbnails()
            self.render_page(self.current_page)
            self.update_thumbnail_selection()
            print("PDF loaded successfully.", fileurl)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
            return

        # For getting the file name in case needed
        global filename
        global edit_file_name
        global folder_path
        try:
            filename = file_path.split('/')[-1]
            beforeexe = filename.split('.')[0]
            edit_file_name = beforeexe+ "_with_annotations.pdf"
            folder_pat = file_path.rsplit('/', 1)[0] + '/'
            folder_path = folder_pat.replace("/api/", "/api/v1/")
            save_url = folder_path+edit_file_name
        except:
            filename = file_path.split('\\')[-1]
            beforeexe = filename.split('.')[0]
            edit_file_name = beforeexe+ "_with_annotations.pdf"
            folder_pat = file_path.rsplit('/', 1)[0] + '/'
            folder_path = folder_pat.replace("/api/", "/api/v1/")
            save_url = folder_path+edit_file_name
        print("file_path-------",file_path)
        print(filename)
        print("edit_file_name",edit_file_name)
        print("folder_pathfolder_path----",folder_path)
        print("save_url----------------------------",save_url)

    def render_thumbnails(self):
        """Render the thumbnails of all PDF pages with fixed dimensions."""
        if not self.pdf_document:
            return

        # Clear existing widgets
        for widget in self.inner_thumbnail_frame.winfo_children():
            widget.destroy()

        self.thumbnails = []  # Clear any previously loaded thumbnails
        self.thumbnail_labels = []  # List to store thumbnail labels for styling

        thumbnail_width = 150
        thumbnail_height = 200

        for page_number in range(len(self.pdf_document)):
            page = self.pdf_document.load_page(page_number)
            pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
            img = Image.open(io.BytesIO(pix.tobytes("png")))

            # Resize and crop the image
            img_resized = ImageOps.fit(img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
            img_tk = ImageTk.PhotoImage(img_resized)
            self.thumbnails.append(img_tk)

            # Create a frame for the thumbnail
            frame = ctk.CTkFrame(self.inner_thumbnail_frame, fg_color="lightgray", corner_radius=10)
            frame.pack(pady=5, padx=20)

            # Add the thumbnail label
            label = ctk.CTkLabel(frame, image=img_tk, text="")
            label.pack()

            # Bind click event to select the page (use a default function to fix lambda binding issue)
            frame.bind("<Button-1>", self.create_page_selection_handler(page_number))
            label.bind("<Button-1>", self.create_page_selection_handler(page_number))

            # Save the frame for styling
            self.thumbnail_labels.append(frame)

        self.update_thumbnail_selection()
        self.inner_thumbnail_frame.update_idletasks()
        self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))

    def create_page_selection_handler(self, page_number):
        """Return a handler function to navigate to the selected page."""
        def handler(event):
            print(f"Thumbnail {page_number} clicked.")  # Debug log
            self.select_page(page_number)
        return handler

    def update_thumbnail_selection(self):
        """Update the highlight of the selected thumbnail."""
        if not self.thumbnail_labels:
            print("No thumbnails to update.")  # Debug log
            return
        if self.thumbnail_labels:
            self.thumbnail_labels[0].configure(border_color="#FFA500", border_width=3)

        for i, frame in enumerate(self.thumbnail_labels):
            if i == self.current_page:
                frame.configure(border_color="#FFA500", border_width=3)  # Highlight
            else:
                frame.configure(border_color="lightgray", border_width=1)
        self.inner_thumbnail_frame.update_idletasks()

    def select_page(self, page_number):
        """Navigate to the selected page."""
        self.current_page = page_number
        print(f"Selected page: {self.current_page}")  # Debug log
        self.render_page(page_number)
        self.update_thumbnail_selection()

    def create_duplicate_window(self, fileurl):
        """Creates a duplicate window to display a PDF independently."""
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
        self.zoom_factor += 0.2
        self.render_page(self.current_page)
    def zoom_out(self):
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
            ctk.CTkMessagebox.show_error("Error", "No PDF loaded.")
            return
        # Load and render the PDF page
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
        self.redraw_freehand_drawing()
        self.redraw_polygons()
    
    def redraw_freehand_drawing(self):
        """Redraw all freehand lines based on stored coordinates and zoom factor."""
        if not hasattr(self, "drawings"):
            self.drawings = []
        for line in self.drawings:
            scaled_line = [
                coord * self.zoom_factor for coord in line
            ]  # Adjust coordinates to the current zoom level
            self.canvas.create_line(*scaled_line, fill="black", width=2)

    def on_mouse_scroll(self, event):
        """Handle vertical scrolling with the mouse wheel."""
        self.canvas.yview_scroll(-1 * (event.delta // 120), "units")

    def on_shift_mouse_scroll(self, event):
        """Handle horizontal scrolling with Shift + mouse wheel."""
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

        note_text = self.ask_for_note_text(x, y)
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
            print("Warning: 'sticky_note' icon not found.")

    def ask_for_note_text(self, x, y):
        """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
        dialog = ctk.CTkToplevel(self.root)
        dialog.title("Enter Sticky Note")
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
        elif action_type == "highlight":
            _, page, annot_id = last_action
            page_obj = self.pdf_document[page]
            annot = page_obj.first_annot
            while annot:
                if annot.info.get('id') == annot_id:
                    page_obj.delete_annot(annot)
                    self.render_page(self.current_page)
                    print(f"Highlight with ID {annot_id} removed.")
                    break
                annot = annot.next
            else:
                print(f"No annotation found with ID {annot_id}. Undo failed.")
        else:
            print(f"Unknown action type: {action_type}")

    def enable_highlight_mode(self):
        """ Activate highlight mode """
        self.highlight_mode = True
        self.sticky_note_mode = False
        self.canvas.unbind("<Button-1>")
        self.canvas.bind("<Button-1>", self.start_rectangle)
        self.canvas.bind("<B1-Motion>", self.draw_rectangle)
        self.canvas.bind("<ButtonRelease-1>", self.finalize_highlight)
        self.start_x, self.start_y = None, None
    def start_rectangle(self, event):
        """Start a rectangle selection for highlighting"""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.rectangle_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x, self.start_y, outline="yellow")
    def draw_rectangle(self, event):
        """Draw the rectangle dynamically as the mouse is dragged"""
        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
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

    def on_mouse_hover(self, event):
        """Show sticky note text when hovering over emoji."""
        if not self.pdf_document:
            return
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)  # Adjust for scrolling
        tooltip_shown = False
        for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                if abs(x - x_position) < 20 and abs(y - y_position) < 20:  # Adjust hover sensitivity
                    if not tooltip_shown:
                        self.show_tooltip(event.x_root, event.y_root, text)  # Use root coordinates for tooltip
                        tooltip_shown = True
                    break
        if not tooltip_shown and getattr(self, "active_tooltip", None):
            self.active_tooltip.destroy()
            self.active_tooltip = None

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

    def save_pdf(self):
        """Save the PDF with embedded sticky notes and upload directly to the server."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF document to save.")
            return

        try:
            temp_pdf = fitz.open()
            for page in self.pdf_document:
                temp_pdf.insert_pdf(self.pdf_document, from_page=page.number, to_page=page.number)

            max_line_length = 50
            for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
                page = temp_pdf[page_num]
                x_position = x_scaled
                y_position = y_scaled
                marker_size = 12
                text_size = 10

                # Add a colored circle instead of an emoji
                marker_color = (1, 0, 0)  # Red color
                page.draw_circle(
                    center=(x_position, y_position),
                    radius=marker_size / 2,
                    color=marker_color,
                    fill=marker_color,
                )

                # Wrap and calculate text box dimensions
                lines = self.wrap_text(text, max_line_length)
                text_offset = 15
                max_text_width = max(len(line) for line in lines) * text_size * 0.6
                max_text_height = len(lines) * text_size * 1.5
                padding = 10
                background_width = max_text_width + padding * 2
                background_height = max_text_height + padding * 2

                # Draw background rectangle for the note
                page.draw_rect(
                    rect=(
                        x_position - padding,
                        y_position + text_offset - padding,
                        x_position + background_width,
                        y_position + text_offset + background_height,
                    ),
                    color=(1, 1, 0),
                    overlay=True,
                    fill_opacity=0.5,
                    fill=(1, 1, 0),
                )

                # Add the wrapped text lines
                for i, line in enumerate(lines):
                    page.insert_text(
                        point=(x_position, y_position + text_offset + (i * text_size * 1.5)),
                        text=line,
                        fontsize=text_size,
                        color=(0, 0, 0),
                    )

            # Save PDF to an in-memory buffer
            pdf_buffer = io.BytesIO()
            temp_pdf.save(pdf_buffer)
            pdf_buffer.seek(0)

            # Upload the PDF
            files = {'file': (edit_file_name, pdf_buffer, 'application/pdf')}
            response = requests.post(folder_path, files=files)
            print("response-----",response.text)
            if response.status_code in [200, 201]:
                messagebox.showinfo("Success", "File successfully uploaded to server.")
            else:
                messagebox.showerror(
                    "Error", f"Failed to upload file. Status code: {response.status_code}, {response.text}"
                )

        except Exception as e:
            messagebox.showerror("Error", f"An error occurred: {e}")
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
    
    def prev_page(self):
        if self.current_page > 0:
            self.current_page -= 1
            self.render_page(self.current_page)

    def next_page(self):
        if self.current_page < len(self.pdf_document) - 1:
            self.current_page += 1
            self.render_page(self.current_page)

    def rotate_90clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 90) % 360)
        self.render_page(self.current_page)

    def rotate_180clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 180) % 360)
        self.render_page(self.current_page)

    def rotate_270clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 270) % 360)
        self.render_page(self.current_page)

    def toggle_invert_colors(self):
        """Toggle color inversion for the PDF."""
        if not self.pdf_document:
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

    # Toggle drawing mode
    def toggle_drawing(self):
        """Toggle the drawing mode on or off."""
        self.is_drawing = not getattr(self, "is_drawing", False)  # Ensure is_drawing defaults to False
        if self.is_drawing:
            self.draw_button.configure(text="Stop Drawing")
            self.canvas.bind("<Button-1>", self.start_drawing)
            self.canvas.bind("<B1-Motion>", self.draw_line)
        else:
            self.draw_button.configure(text="")
            self.canvas.unbind("<Button-1>")
            self.canvas.unbind("<B1-Motion>")

    def draw_line(self, event):
        """Draw a line and save it for the current page."""
        if not hasattr(self, "drawing_start"):
            return
        x1, y1 = self.drawing_start
        x2, y2 = event.x, event.y
        current_page = self.current_page

        # Save the line coordinates relative to the canvas
        line = (x1 / self.zoom_factor, y1 / self.zoom_factor, x2 / self.zoom_factor, y2 / self.zoom_factor)

        # Ensure the current page has an entry in page_drawings
        if current_page not in self.page_drawings:
            self.page_drawings[current_page] = []

        # Add the line to the current page's list
        self.page_drawings[current_page].append(line)

        # Draw the line on the canvas
        self.canvas.create_line(x1, y1, x2, y2, fill="black", width=2)
        self.drawing_start = (x2, y2)  # Update the starting point for the next segment

    # Start drawing
    def start_drawing(self, event):
        """Initialize the start point for drawing."""
        self.drawing_start = (event.x, event.y)

    # Redraw lines for the current page
    def redraw_freehand_drawing(self):
        """Redraw lines for the current page."""
        if self.current_page not in self.page_drawings:
            return

        # Get the lines for the current page
        lines = self.page_drawings[self.current_page]

        # Scale and draw each line
        for line in lines:
            scaled_line = [coord * self.zoom_factor for coord in line]
            self.canvas.create_line(*scaled_line, fill="black", width=2)





    def toggle_filled_polygon_mode(self):
        """Toggle filled polygon drawing mode."""
        self.polygon_mode = "filled"
        self.start_point = None
        self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)

    def toggle_hollow_polygon_mode(self):
        """Toggle hollow polygon drawing mode."""
        self.polygon_mode = "hollow"
        self.start_point = None
        self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)

    def on_canvas_polygon_click(self, event):
        """Handle canvas clicks for creating or modifying polygons."""
        if not self.polygon_mode:
            return
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        if self.start_point is None:
            # Start a new polygon
            self.start_point = (x, y)
            points = self.generate_polygon_points(x, y, self.polygon_size, 5)
            polygon_id = self.canvas.create_polygon(
                points, fill="blue" if self.polygon_mode == "filled" else "",
                outline="black" if self.polygon_mode == "filled" else "red",
                tags=("polygon",)
            )
            self.polygons.append((self.polygon_mode, points, polygon_id))
        else:
            # Check if the click is near a vertex of any polygon
            for idx, (mode, points, polygon_id) in enumerate(self.polygons):
                for i in range(0, len(points), 2):
                    px, py = points[i], points[i + 1]
                    if math.sqrt((px - x) ** 2 + (py - y) ** 2) < 10:
                        self.dragging_polygon = (idx, i // 2)  # Polygon index and vertex index
                        self.canvas.bind("<B1-Motion>", self.on_polygon_drag)
                        self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                        return
        self.redraw_polygons()
    
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
        
    def on_polygon_drag(self, event):
        """Handle dragging to reshape polygons."""
        if not hasattr(self, 'dragging_polygon'):
            return
        idx, vertex_idx = self.dragging_polygon
        mode, points, polygon_id = self.polygons[idx]
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        points[vertex_idx * 2], points[vertex_idx * 2 + 1] = x, y
        self.canvas.coords(polygon_id, points)

    def on_polygon_drag_release(self, event):
        """Release the polygon after dragging."""
        if hasattr(self, 'dragging_polygon'):
            del self.dragging_polygon
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    def redraw_polygons(self):
        """Redraw polygons on the canvas."""
        for mode, points, page_number in self.polygons:
            if page_number == self.current_page:
                scaled_points = [(px * self.page_width, py * self.page_height) for px, py in points]
                if mode == "filled":
                    self.canvas.create_polygon(scaled_points, fill="blue", outline="black", tags="polygon")
                elif mode == "hollow":
                    self.canvas.create_polygon(scaled_points, fill="", outline="red", tags="polygon")




     
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