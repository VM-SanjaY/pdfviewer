import os
import tempfile
import base64

import io
import tkinter as tk
import tkinter.ttk as ttk
from tkinter import filedialog, messagebox, Toplevel
import fitz
import textwrap
from PIL import Image, ImageTk, ImageOps
import requests
from urllib.parse import urlparse
from duplicate_window import DuplicateStickyNotesPDFApp
import socket
import threading
import sys
from protocol_handler import ProtocolHandler

class StickyNotesPDFApp:
    # sample port replace it to required port when connecting to live server
    SOCKET_PORT = 65432
    def __init__(self, root):
        self.root = root
        self.root.title("Atic PDF Editor Screen")
        self.zoom_factor = 1.0
        self.sticky_note_mode = False  # default set to deactive after each use.
        self.highlight_mode = False # default set to deactive after each use.
        self.change_history = []  # to remove all change in order.
        self.sticky_notes = {}  # to coordinate and text storing
        self.thumbnails = [] # for listing the thumnails
        self.pdf_document = None
        self.current_page = None
        self.is_inverted = False
        self.create_widgets()  # design and alignment for buttons.
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<Motion>", self.on_mouse_hover)  # to view tooltip
        self.active_tooltip = None 
        self.page_width = 0
        self.page_height = 0
        self.duplicate_windows = []  # List to track active duplicate windows
        self.root.protocol("WM_DELETE_WINDOW", self.close_main_window)
        self.setup_ipc_server()      
        # Handle command line arguments
        if len(sys.argv) > 1:
            pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
            self.handle_url(pdf_url)

        self.temp_file_path = None # to store the Temp. file path
        self.server_url = "https://idms-api.blockchaincloudapps.com/upload/file" # server url to upload pdf
        # Register the cleanup function to be called on window close
        # self.root.protocol("WM_DELETE_WINDOW", self.on_close) # to close the window
    
    # button design and alignment
    def create_widgets(self):
        style = ttk.Style()
        style.configure(
            "Modern.TButton",
            font=("Arial", 12),
            padding=(2, 2),  # Minimize padding for a compact look
            relief="flat",
            background="#00498f",  # Dark blue background for normal state
            foreground="white",
            borderwidth=1,
            highlightthickness=0,  # Remove focus highlight border
        )
        style.map(
            "Modern.TButton",
            background=[("active", "#00498f"), ("!disabled", "#00498f")],  # Ensure background stays dark blue on active state
            foreground=[("active", "white")],
        )
        toolbar = tk.Frame(self.root)
        toolbar.pack(fill=tk.X, pady=8)

        def create_button(parent, text, command, tooltip_text=""):
            button_frame = tk.Frame(parent, width=50, height=30)  # Set fixed width and height
            button_frame.pack_propagate(False)  # Prevent resizing to fit content
            button_frame.pack(side=tk.LEFT, padx=3)
            button = ttk.Button(
                button_frame,
                text=text,
                style="Modern.TButton",
                command=command
            )
            button.pack(fill=tk.BOTH, expand=True)  # Fill the frame
            # Add hover functionality for tooltip
            button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
            button.bind("<Leave>", self.hide_tooltip)
            return button

        # buttons with tooltips functionality
        create_button(toolbar, "📂", self.load_pdf, "Load PDF")  #  text that is visible when hovered
        create_button(toolbar, "📄+", lambda: self.create_duplicate_window(fileurl), "New Window")
        create_button(toolbar, "🔍-", self.zoom_out, "Zoom Out")
        create_button(toolbar, "🔍+", self.zoom_in, "Zoom In")
        create_button(toolbar, "⬅️", self.prev_page, "Previous Page")
        create_button(toolbar, "➡️", self.next_page, "Next Page")
        create_button(toolbar, "↩️", self.undo_change, "Undo")
        create_button(toolbar, "✒️", self.enable_highlight_mode, "Highlight")
        create_button(toolbar, "📌", self.toggle_sticky_note_mode, "Sticky Note")
        create_button(toolbar, "⮧", self.rotate_90clockwise, "Rotate 90° Right")
        create_button(toolbar, "⮠ ", self.rotate_180clockwise, "Rotate 180° Right")
        create_button(toolbar, "⮤", self.rotate_270clockwise, "Rotate 270° Right")
        create_button(toolbar, "❖", self.best_fit, "Best Fit")
        create_button(toolbar, "↔", self.best_width, "Best Width")
        create_button(toolbar, "↕", self.best_height, "Best Height")
        create_button(toolbar, "🌓", self.toggle_invert_colors, "Invert Colors")
        create_button(toolbar, "💾", self.save_pdf, "Save PDF")
        #create_button(toolbar, "Reg status", self.verify_protocol_registration, "Verify Protocol Registration")
        canvas_frame = tk.Frame(self.root)
        canvas_frame.pack(fill=tk.BOTH, expand=True)

        self.thumbnail_frame = tk.Frame(canvas_frame, width=150, bg="lightgray")
        self.thumbnail_frame.pack(side=tk.LEFT, fill=tk.Y)

        # Scrollable Thumbnail Canvas
        self.thumbnail_canvas = tk.Canvas(self.thumbnail_frame, bg="lightgray", width=200)
        self.thumbnail_scrollbar = tk.Scrollbar(self.thumbnail_frame, orient=tk.VERTICAL, command=self.thumbnail_canvas.yview)
        self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
        self.thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.inner_thumbnail_frame = tk.Frame(self.thumbnail_canvas, bg="lightgray")
        self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
        # main body design and structure.
        self.canvas = tk.Canvas(canvas_frame, bg="lightgray", width=900, height=650)
        self.h_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
        self.v_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
        self.h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Bind mouse scroll events
        self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
        self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
    # this is for the button to show text on mouse hover
    def button_tooltip(self, event, button_text, tooltip_text):
        """Display tooltip when hovering over a button."""
        if self.active_tooltip:
            self.active_tooltip.destroy() # to destroy automatiacally each second
        tooltip = tk.Toplevel(self.root)
        tooltip.wm_overrideredirect(True) # it used for closing tooltip
        tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")  # text Position near the mouse hover
        # tooltip design
        label = tk.Label(tooltip, text=tooltip_text, background="light yellow", relief="solid", padx=5, pady=5)
        label.pack()
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
        
    # open pdf from local system or by link
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
            print("PDF loaded successfully.",fileurl)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
            return
        # for getting the file name incase needed
        global filename
        global edit_file_name
        try:
            filename = file_path.split('/')[-1]
            edit_file_name = filename+"_edited"
        except:
            filename = file_path.split('\\')[-1]
            edit_file_name = filename+"_edited"
        print(filename)

    # show thumnb nail as preview on the left
    def render_thumbnails(self):
        """Render the thumbnails of all PDF pages with fixed dimensions."""
        if not self.pdf_document:
            return
        
        for widget in self.inner_thumbnail_frame.winfo_children():
            widget.destroy()
        
        self.thumbnails = []  # Clear any previously loaded thumbnails
        self.thumbnail_labels = []  # List to store thumbnail labels for styling
        
        thumbnail_width = 150  # Fixed width for thumbnails
        thumbnail_height = 200  # Fixed height for thumbnails
        
        for page_number in range(len(self.pdf_document)):
            page = self.pdf_document.load_page(page_number)
            pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))  # Initial scale for rendering
            img = Image.open(io.BytesIO(pix.tobytes("png")))
            
            # Resize and crop the image to the fixed dimensions
            img_resized = ImageOps.fit(img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
            img_tk = ImageTk.PhotoImage(img_resized)
            self.thumbnails.append(img_tk)
            
            # Create a frame to hold the thumbnail and border
            frame = tk.Frame(self.inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
            frame.pack(pady=5, padx=20)
            frame.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
            
            # Add the thumbnail label inside the frame
            label = tk.Label(frame, image=img_tk, bg="lightgray")
            label.pack()
            label.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
            
            # Save the frame for styling
            self.thumbnail_labels.append(frame)
        
        self.update_thumbnail_selection()  # Highlight the initial page
        self.inner_thumbnail_frame.update_idletasks()
        self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))

    # for heighlight the selected page
    def update_thumbnail_selection(self):
        """Update the highlight of the selected thumbnail."""
        for i, frame in enumerate(self.thumbnail_labels):
            if i == self.current_page:
                frame.config(highlightbackground="orange", highlightcolor="orange")
            else:
                frame.config(highlightbackground="lightgray", highlightcolor="lightgray")
    # when selecting page from the left to view            
    def select_page(self, page_number):
        """Navigate to the selected page."""
        self.current_page = page_number
        self.render_page(page_number)
        self.update_thumbnail_selection()

    def create_duplicate_window(self, fileurl):
        """Creates a duplicate window to display a PDF independently."""
        if not fileurl:
            messagebox.showerror("Error", "No PDF is currently loaded to duplicate.")
            return
        duplicate_root = Toplevel(self.root)  # Create a new top-level window
        duplicate_window = DuplicateStickyNotesPDFApp(duplicate_root, fileurl)
        self.duplicate_windows.append(duplicate_root)
        def on_close():
            self.duplicate_windows.remove(duplicate_root)
            duplicate_root.destroy()
        duplicate_root.protocol("WM_DELETE_WINDOW", on_close)

    def close_main_window(self):
        """Closes the main window only if there are no duplicate windows open."""
        if self.duplicate_windows:
            messagebox.showwarning("Warning", "Please close all duplicate windows before exiting the main window.")
        else:
            self.root.destroy()
    
    # zoom in function
    def zoom_in(self):
        self.zoom_factor += 0.2
        self.render_page(self.current_page)

    # zoom out function 
    def zoom_out(self):
        if self.zoom_factor > 0.4:
            self.zoom_factor -= 0.2
            self.render_page(self.current_page)
    # to show the entire pdf in the window
    def best_fit(self):
        """Adjust the zoom level to fit the entire PDF page within the canvas."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()       
        page = self.pdf_document.load_page(self.current_page)
        page_width, page_height = page.rect.width, page.rect.height      
        # Calculate scaling factors for width and height
        width_scale = canvas_width / page_width
        height_scale = canvas_height / page_height
        # Use the smaller scale to ensure the entire page fits
        self.zoom_factor = min(width_scale, height_scale)        
        # Render the page with the new zoom factor
        self.render_page(self.current_page)

    def best_width(self):
        """Adjust the zoom level to fit the entire PDF page to the canvas width."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        canvas_width = self.canvas.winfo_width()
        page = self.pdf_document.load_page(self.current_page)
        page_width = page.rect.width

        # Calculate the scaling factor for width
        self.zoom_factor = canvas_width / page_width

        # Render the page with the new zoom factor
        self.render_page(self.current_page)

    def best_height(self):
        """Adjust the zoom level to fit the entire PDF page to the canvas height."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        canvas_height = self.canvas.winfo_height()
        page = self.pdf_document.load_page(self.current_page)
        page_height = page.rect.height

        # Calculate the scaling factor for height
        self.zoom_factor = canvas_height / page_height

        # Render the page with the new zoom factor
        self.render_page(self.current_page)

    # page render as per page nymber to record changes in the undo_change function as well
    def render_page(self, page_number):
        """Render a PDF page to the canvas with the current zoom factor."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        # render as per page
        page = self.pdf_document.load_page(page_number)
        matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
        pix = page.get_pixmap(matrix=matrix)
        img = Image.open(io.BytesIO(pix.tobytes("png")))

        # Apply color inversion if needed
        if self.is_inverted:
            img = ImageOps.invert(img.convert("RGB"))
        # converting it to image for cokor correction
        img_tk = ImageTk.PhotoImage(img)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
        self.canvas.img_tk = img_tk  # Store reference to avoid cache collection

        # Update canvas scroll region to fit the image dimensions
        self.page_width, self.page_height = pix.width, pix.height
        self.canvas.config(scrollregion=(0, 0, self.page_width, self.page_height))

        # Redraw sticky notes on the page to view changes
        self.redraw_sticky_notes()

    # for activating scroll functionallity
    def on_mouse_scroll(self, event):
        """Handle vertical scrolling with the mouse wheel."""
        self.canvas.yview_scroll(-1 * (event.delta // 120), "units")
    # for activating scroll functionallity
    def on_shift_mouse_scroll(self, event):
        """Handle horizontal scrolling with Shift + mouse wheel."""
        self.canvas.xview_scroll(-1 * (event.delta // 120), "units")
    # for activating scroll functionallity
    def on_thumbnail_scroll(self, event):
        """Handle vertical scrolling in the thumbnail panel using the mouse wheel."""
        self.thumbnail_canvas.yview_scroll(-1 * (event.delta // 120), "units")
    # used to change mode so it does not remove other when using
    def enable_sticky_note_mode(self):
        """ Activate sticky note mode """
        self.sticky_note_mode = True  # Enable sticky note mode
        self.highlight_mode = False  # Disable highlight mode
        self.canvas.unbind("<B1-Motion>") # deactives
        self.canvas.unbind("<ButtonRelease-1>")# deactives
        self.canvas.bind("<Button-1>", self.on_canvas_click)# pass it to other function when it takes for adding sticky note

    # redraw the sticky note on the pdf to that is does not get removed
    def redraw_sticky_notes(self):
        """Redraw sticky notes after rendering the page."""
        self.canvas.delete("sticky_note")  # Remove any previous sticky notes

        # Adjust the emoji color based on the inversion state
        emoji_fill = "white" if self.is_inverted else "black"  # Contrast with background

        # Redraw all sticky notes
        for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                
                # First, draw a "shadow" text for the outline effect (slightly offset)
                self.canvas.create_text(
                    x_position + 1, y_position + 1, text="📌", font=("Arial", 16),
                    fill="white", tags="sticky_note_shadow"
                )
                # Now draw the main sticky note text
                self.canvas.create_text(
                    x_position, y_position, text="📌", font=("Arial", 16),
                    fill=emoji_fill, tags="sticky_note"
                )

    # for getting the coordinate and storing it to change event
    def on_canvas_click(self, event):
        """Add a sticky note at the clicked position on the canvas."""
        if not self.pdf_document or not self.sticky_note_mode:
            return

        # Adjust click coordinates for scrolling
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        print(f"Clicked coordinates (adjusted): {x}, {y}")

        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            print("Click outside page bounds.")
            return  # Clicked outside the PDF page area

        # Prompt for note text
        note_text = self.ask_for_note_text(x, y)
        if not note_text:
            print("No note text entered.")
            return  # No text entered

        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        print(f"Scaled coordinates: {x_scaled}, {y_scaled}")

        # Add the sticky note to the storage
        self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
        self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
        print(f"Added sticky note: {('sticky_note', self.current_page, x_scaled, y_scaled, note_text)}")

        # Visual feedback on the canvas
        self.canvas.create_text(x, y, text="📌", font=("Arial", 16))
        self.sticky_note_mode = False
        print("Sticky note mode disabled.")

    # textbox function for using adding text as a tooltip
    def ask_for_note_text(self, x, y):
        """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
        dialog = tk.Toplevel(self.root) # used for to show as a separate window.
        dialog.title("Enter Sticky Note")
        dialog.geometry("400x250") # window size
        dialog.configure(bg="#f9f9f9")  # Light background color
        dialog.resizable(False, False)

        # Add a title label
        label = tk.Label(
            dialog, text="Enter your note:", font=("Arial", 14, "bold"), bg="#f9f9f9"
        )
        label.pack(pady=(15, 10))

        # Create a Text widget for the note input
        text_box = tk.Text(dialog, wrap=tk.WORD, height=6, width=40, font=("Arial", 12), relief="solid")
        text_box.pack(padx=15, pady=5, fill=tk.X)
        text_box.focus_set()  # Automatically focus the text box

        # Variable to store the note text
        note_text_var = tk.StringVar()
        # button functionality
        def on_ok_click():
            note_text = text_box.get("1.0", tk.END).strip()  # Get text from the Text widget
            if note_text:
                note_text_var.set(note_text)  # Save the entered note text
                dialog.destroy()
            else:
                messagebox.showwarning(
                    "Empty Note", "You must enter some text to save the sticky note."
                )

        # Helper function to create rounded buttons
        def create_rounded_button(parent, text, bg_color, fg_color, command):
            canvas = tk.Canvas(parent, width=120, height=40, bg="#f9f9f9", highlightthickness=0)
            canvas.pack(side=tk.LEFT, padx=10)
            canvas.create_oval(10, 10, 40, 40, fill=bg_color, outline=bg_color)
            canvas.create_oval(80, 10, 110, 40, fill=bg_color, outline=bg_color)
            canvas.create_rectangle(25, 10, 95, 40, fill=bg_color, outline=bg_color)
            button_text = canvas.create_text(60, 25, text=text, fill=fg_color, font=("Arial", 12, "bold"))

            # Add click behavior
            def on_click(event):
                command()

            canvas.tag_bind(button_text, "<Button-1>", on_click)
            canvas.tag_bind("all", "<Enter>", lambda e: canvas.configure(cursor="hand2"))
            canvas.tag_bind("all", "<Button-1>", on_click)
            return canvas

        # Frame for buttons
        buttons_frame = tk.Frame(dialog, bg="#f9f9f9")
        buttons_frame.pack(side=tk.BOTTOM, pady=15)

        # Rounded OK button
        create_rounded_button(buttons_frame, "OK", bg_color="#4CAF50", fg_color="white", command=on_ok_click)

        # Rounded Cancel button
        create_rounded_button(buttons_frame, "Cancel", bg_color="#F44336", fg_color="white", command=dialog.destroy)

        # Ensure the dialog is modal
        dialog.grab_set()
        dialog.wait_window()

        self.sticky_note_mode = False
        return note_text_var.get() or None

    # used to remove the change made to the pdf as per order
    def undo_change(self):
        if not self.change_history:
            print("No actions to undo.")
            return
        # remove last data function 
        last_action = self.change_history.pop()
        print(f"Undoing action: {last_action}")
        action_type = last_action[0]
        # condition check for undo functions
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
    # similar to sticky note this is used to deactivate sticky note and enables highlight function
    def enable_highlight_mode(self):
        """ Activate highlight mode """
        self.highlight_mode = True
        self.sticky_note_mode = False
        self.canvas.unbind("<Button-1>")
        self.canvas.bind("<Button-1>", self.start_rectangle)
        self.canvas.bind("<B1-Motion>", self.draw_rectangle)
        self.canvas.bind("<ButtonRelease-1>", self.finalize_highlight)
        self.start_x, self.start_y = None, None
    # this is used to show a out line of rectangle to let the user know from where to where
    def start_rectangle(self, event):
        """Start a rectangle selection for highlighting"""
        self.start_x = self.canvas.canvasx(event.x)
        self.start_y = self.canvas.canvasy(event.y)
        self.rectangle_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x, self.start_y, outline="yellow"
        )
    # this is used to send the coordinate to cover the area after draging to highlight the area
    def draw_rectangle(self, event):
        """Draw the rectangle dynamically as the mouse is dragged"""
        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
        self.canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)
    # this function is used to highlight the area 
    def finalize_highlight(self, event):
        """Finalize the highlight and save it to the PDF."""
        if self.start_x is None or self.start_y is None:
            return  # No valid starting point

        # Get the end point of the dragged highlight
        end_x = self.canvas.canvasx(event.x) / self.zoom_factor
        end_y = self.canvas.canvasy(event.y) / self.zoom_factor
        start_x = self.start_x / self.zoom_factor
        start_y = self.start_y / self.zoom_factor

        rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
       # Adjust coordinates for page rotation
        page = self.pdf_document[self.current_page]
        rotation = page.rotation
        page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor

        if rotation == 90:
            rect = fitz.Rect(
                rect.y0,
                page_width - rect.x1,
                rect.y1,
                page_width - rect.x0
            )
        elif rotation == 180:
            rect = fitz.Rect(
                page_width - rect.x1,
                page_height - rect.y1,
                page_width - rect.x0,
                page_height - rect.y0
            )
        elif rotation == 270:
            rect = fitz.Rect(
                page_height - rect.y1,
                rect.x0,
                page_height - rect.y0,
                rect.x1
            )

        # Add a rectangle annotation as a workaround
        try:
            highlight = page.add_highlight_annot(rect)
            highlight.update()  # Ensure the annotation is saved to the PDF

            # Force rectangle appearance by tweaking the annotation border
            highlight.set_border(width=0, dashes=(0, 0))  # Ensure no rounding and no dashes
            annot_id = highlight.info.get('id') # this is used to undo function
            if annot_id:
                self.change_history.append(("highlight", self.current_page, annot_id))
        except Exception as e:
            messagebox.showerror("Error", f"Failed to add highlight: {e}")
            return

        # Re-render the page to show the highlight
        self.render_page(self.current_page)

        # Unbind the highlight-related events
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    # this function is used for sticky note
    def on_mouse_hover(self, event):
        """Show sticky note text when hovering over emoji."""
        if not self.pdf_document:
            return
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)  # Adjust for scrolling
        tooltip_shown = False
        # storing of sticky note coordinates as dictionary
        for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                if abs(x - x_position) < 20 and abs(y - y_position) < 20:  # Adjust hover sensitivity
                    if not tooltip_shown:
                        self.show_tooltip(event.x_root, event.y_root, text)  # Use root coordinates for tooltip
                        tooltip_shown = True
                    break
        # to remove the text add as a tooltip when not over
        if not tooltip_shown and getattr(self, "active_tooltip", None):
            self.active_tooltip.destroy()
            self.active_tooltip = None
    # to dispaly text on the empji during mouse hover
    def show_tooltip(self, x, y, text):
        """ Display the sticky note text as a tooltip """
        if getattr(self, "active_tooltip", None):
            self.active_tooltip.destroy()

        wrapped_text = textwrap.fill(text, width=50) # ensuring that the line end at 50 characters 
        tooltip = tk.Toplevel(self.root)
        tooltip.wm_overrideredirect(True)
        tooltip.wm_geometry(f"+{int(x) + 10}+{int(y) + 10}")  # Ensure integer coordinates

        label = tk.Label(tooltip, text=wrapped_text, background="light yellow", relief="solid", padx=5, pady=5)
        label.pack()

        self.active_tooltip = tooltip
    # deactivate sticky notes
    def toggle_sticky_note_mode(self):
        """Toggle sticky note mode"""
        if self.sticky_note_mode:
            self.sticky_note_mode = False
            self.canvas.unbind("<Button-1>")
        else:
            self.enable_sticky_note_mode()

    # save the editted pdf separately.
    def save_pdf(self):
        """Save the PDF with embedded sticky notes to a file."""
        if not self.pdf_document:
            return
        # open local system to save the file
        # file_path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF files", "*.pdf")])
        # if not file_path:
        #     return
        # Create a new empty PDF to save the data of sticky note not as emoji but as a actual text
        temp_pdf = fitz.open()  
        for page in self.pdf_document:  # Copy each page to the new PDF
            temp_pdf.insert_pdf(self.pdf_document, from_page=page.number, to_page=page.number)

        max_line_length = 50 # same to limit the character in a line
        for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
            page = temp_pdf[page_num]
            x_position = x_scaled
            y_position = y_scaled
            marker_size = 12  # Font size for emoji
            text_size = 10    # Font size for sticky note text

            page.insert_text(
                point=(x_position, y_position),
                text="📌",
                fontsize=marker_size,
                color=(1, 0, 0)  # Red color for the emoji
            )
            # storing the line as list in split up
            lines = self.wrap_text(text, max_line_length)
            text_offset = 15
            # adding text as per character width
            max_text_width = max(len(line) for line in lines) * text_size * 0.6  # Approximate width of text box
            max_text_height = len(lines) * text_size * 1.5  # Height of the text box based on number of lines
            padding = 10
            background_width = max_text_width + padding * 2  # Extra padding on both sides
            background_height = max_text_height + padding * 2  # Extra padding top and bottom
            # drawing of backgroung color to show text saved as sticky note.
            page.draw_rect(
                rect=(x_position - padding, y_position + text_offset - padding, x_position + background_width, y_position + text_offset + background_height),
                color=(1, 1, 0),  # Yellow background
                overlay=True,
                fill_opacity=0.5,
                fill=(1, 1, 0)  # This ensures the rectangle is filled with yellow
            )
            # storing the text in the sticky note.
            for i, line in enumerate(lines):
                page.insert_text(
                    point=(x_position, y_position + text_offset + (i * text_size * 1.5)),  # Vertical spacing between lines
                    text=line,
                    fontsize=text_size,
                    color=(0, 0, 0)  # Black color for the text
                )

        # temp_pdf.save(file_path) # the temp file that was created is where this changes are done. so that after saving no change are appaer on the viewing pdf.
        # temp_pdf.close()

        if temp_pdf:

            # Encode the PDF file data
            encoded_pdf_data = self.encode_pdf_data(temp_pdf.write())

            # Save the encoded PDF as a temporary file
            unreadable_filename = "temp_file.temp"  # Can choose a random or actual/unique filename to handle multiprocessing
            self.temp_file_path = self.save_pdf_as_temp(unreadable_filename, encoded_pdf_data) # encoding is not rquired, then can pass the temp_pdf directly.
            print(f"PDF saved as: {self.temp_file_path}")

            #decoded_pdf_data = self.decode_pdf_data(encoded_pdf_data)   # Decode the PDF data, if needed as per the encoding
            if self.temp_file_path:
                print("hello")
             #   files = {'file': (fileurl, decoded_pdf_data)} # Replace the actual file name to test.pdf
                files = {'file': (edit_file_name, open(fileurl, 'rb'))}
                response = requests.post(self.server_url, files=files)
                if response.status_code == 200 or response.status_code == 201:
                    print("File successfully uploaded to server.")
                else:
                    print(f"Failed to upload file. Status code: {response.status_code, response.text}")
            else:
                print("No file to send.")
        else:
            print("No PDF data to save.")

    # this function is used to decode the pdf data
    def decode_pdf_data(self, encoded_pdf_data):
        """Decode the base64-encoded PDF data."""
        return base64.b64decode(encoded_pdf_data)
    
    # this function is used to save the pdf as a file
    def encode_pdf_data(self, pdf_data):
        """Encode the PDF data to an unreadable format (base64)."""
        return base64.b64encode(pdf_data)

    # this function is used to save the pdf as a file
    def save_pdf_as_temp(self, unreadable_filename, pdf_data):
        """Save the base64-encoded PDF as a temporary file."""
        temp_dir = tempfile.gettempdir()
        temp_file_path = os.path.join(temp_dir, unreadable_filename)
        with open(temp_file_path, 'wb') as temp_file:
            temp_file.write(pdf_data)
        return temp_file_path

    # this function is used to delete the temp file after saving the pdf
    def delete_temp_file(self):
        """Delete the temporary file."""
        try:
            if self.temp_file_path:
                os.remove(self.temp_file_path)
                print(f"Temporary file {self.temp_file_path} deleted successfully.")
        except Exception as e:
            print(f"Error while deleting temp file: {e}")

    # this function is used to close the window
    def on_close(self):
        """Handle window close event, cleanup, and exit."""
        if self.temp_file_path:
            self.delete_temp_file()  # Cleanup the temporary file
        self.root.quit()  # Close the Tkinter window

    # function to wrap text as per character limit.
    def wrap_text(self, text, max_line_length):
        """Wrap the text into lines with a maximum number of characters per line."""
        words = text.split(" ")
        lines = []
        current_line = ""
        # breaking down the words in the text if a word is 100 characters then it will not split it.
        for word in words:
            if len(current_line) + len(word) + 1 <= max_line_length:
                current_line += (word + " ")
            else:
                lines.append(current_line.strip())
                current_line = word + " "
        if current_line:
            lines.append(current_line.strip())

        return lines
    # go to pervious page
    def prev_page(self):
        if self.current_page > 0:
            self.current_page -= 1
            self.render_page(self.current_page)
    # go to next page
    def next_page(self):
        if self.current_page < len(self.pdf_document) - 1:
            self.current_page += 1
            self.render_page(self.current_page)
    # rotate 90 degree
    def rotate_90clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 90) % 360)  # Rotate clockwise
        self.render_page(self.current_page)  # Re-render the page
    # rotate 180 degree
    def rotate_180clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 180) % 360)  # Rotate clockwise
        self.render_page(self.current_page)  # Re-render the page
    # rotate 270 degree
    def rotate_270clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document:
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 270) % 360)  # Rotate clockwise
        self.render_page(self.current_page)  # Re-render the page

    # converting colors inside out.
    def toggle_invert_colors(self):
        """Toggle color inversion for the PDF."""
        if not self.pdf_document:
            return
        self.is_inverted = not self.is_inverted
        self.render_page(self.current_page)
        self.redraw_sticky_notes()

    def verify_protocol_registration(self):
        """Check and display the protocol registration status"""
        handler = ProtocolHandler()
        
        # First check current status
        is_registered = handler.verify_registration()
        
        if is_registered:
            status_msg = (
                "Protocol handler is properly registered.\n\n"
                f"Protocol: {handler.protocol}\n"
                f"OS: {handler.os_type}\n"
                f"App Path: {handler.app_path}\n\n"
                "The application will open automatically when clicking PDF links."
            )
            messagebox.showinfo("Protocol Registration", status_msg)
        else:
            status_msg = (
                "Protocol handler is not registered or registration is incomplete.\n\n"
                f"Protocol: {handler.protocol}\n"
                f"OS: {handler.os_type}\n"
                f"App Path: {handler.app_path}\n\n"
                "Would you like to attempt registration now?"
            )
            result = messagebox.askquestion(
                "Protocol Registration", 
                status_msg,
                icon='warning'
            )
            if result == 'yes':
                try:
                    success, message = handler.register()
                    if success:
                        messagebox.showinfo(
                            "Registration Success", 
                            f"{message}\n\n"
                            f"Protocol: {handler.protocol}\n"
                            f"OS: {handler.os_type}\n"
                            f"App Path: {handler.app_path}"
                        )
                    else:
                        messagebox.showerror(
                            "Registration Failed", 
                            f"{message}\n\n"
                            "Please check the console for more details."
                        )
                except Exception as e:
                    messagebox.showerror(
                        "Registration Error", 
                        f"Failed to register protocol handler:\n{str(e)}"
                    )

# used to run the file.
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

    root = tk.Tk()
    app = StickyNotesPDFApp(root)
    root.mainloop()



