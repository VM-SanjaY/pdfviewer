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
        self._user_scrolling = False
        self._user_batch_navigation = False
        self._batch_load_in_progress = False
        self._last_scroll_time = 0
        self._scroll_cooldown = 1.0
        self._manual_batch_selection = None
        self._auto_revert_disabled = False
        self.thumbnail_canvas.bind("<Configure>", self.on_thumbnail_canvas_configure)
        self._batch_check_job = None
        if not hasattr(self, 'current_page') or self.current_page is None:
            self.current_page = 0
        self.load_thumbnail_batch(0)

    def on_thumbnail_canvas_configure(self, event=None):
        """Handle thumbnail canvas configuration changes."""
        if not self._user_batch_navigation and not self._batch_load_in_progress:
            self.check_and_update_thumbnail_batch()

    def on_thumbnail_scroll(self, event):
        """Handle mouse wheel scrolling in thumbnail area with improved logic."""
        import time
        current_time = time.time()
        current_batch_start = self.current_thumbnail_batch * self.thumbnail_batch_size
        current_batch_end = min(current_batch_start + self.thumbnail_batch_size, self.total_pages)
        current_batch_size = current_batch_end - current_batch_start
        if current_batch_size <= 6:
            return
        if current_time - self._last_scroll_time < self._scroll_cooldown:
            self.thumbnail_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            return
        self._user_scrolling = True
        self._user_batch_navigation = True
        self._auto_revert_disabled = True
        for job_attr in ['_scroll_reset_job', '_batch_check_job', '_revert_job', '_user_reset_job']:
            if hasattr(self, job_attr) and getattr(self, job_attr):
                self.root.after_cancel(getattr(self, job_attr))
                setattr(self, job_attr, None)
        self.thumbnail_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        self._batch_check_job = self.root.after(500, self.check_scroll_based_batch_switch)
        self._user_reset_job = self.root.after(2500, self._reset_user_navigation_flags)

    def _reset_user_navigation_flags(self):
        """Reset user navigation flags after scrolling stops."""
        self._user_scrolling = False
        self._user_batch_navigation = False
        self.root.after(5000, lambda: setattr(self, '_auto_revert_disabled', False))

    def check_scroll_based_batch_switch(self):
        """Check if we need to switch batches based on scroll position - with better logic."""
        if self._batch_load_in_progress:
            return
        try:
            import time
            scroll_top, scroll_bottom = self.thumbnail_canvas.yview()
            current_time = time.time()
            if scroll_bottom > 0.95:  # Very close to bottom (95%)
                next_batch = self.current_thumbnail_batch + 1
                max_batch = (self.total_pages - 1) // self.thumbnail_batch_size
                if next_batch <= max_batch and current_time - self._last_scroll_time >= self._scroll_cooldown:
                    print(f"User scroll: Loading next batch {next_batch}")
                    self._last_scroll_time = current_time
                    self._manual_batch_selection = next_batch
                    self._load_batch_with_protection(next_batch, "next")
            elif scroll_top < 0.05:  # Very close to top (5%)
                prev_batch = self.current_thumbnail_batch - 1
                if prev_batch >= 0 and current_time - self._last_scroll_time >= self._scroll_cooldown:
                    print(f"User scroll: Loading previous batch {prev_batch}")
                    self._last_scroll_time = current_time
                    self._manual_batch_selection = prev_batch
                    self._load_batch_with_protection(prev_batch, "prev")
                    
        except Exception as e:
            print(f"Error in scroll-based batch check: {e}")

    def _load_batch_with_protection(self, batch_index, direction):
        """Load batch with protection against rapid switching."""
        if self._batch_load_in_progress:
            print(f"Batch load already in progress, skipping batch {batch_index}")
            return
        self._batch_load_in_progress = True
        self.load_thumbnail_batch(batch_index, preserve_scroll=True, scroll_direction=direction)
        self.root.after(1000, lambda: setattr(self, '_batch_load_in_progress', False))

    def check_and_update_thumbnail_batch(self, event=None):
        """Only switch batches based on current page if appropriate."""
        if (self._user_batch_navigation or 
            self._batch_load_in_progress or 
            self._manual_batch_selection is not None):
            return
        if not hasattr(self, 'current_page') or self.current_page is None:
            target_page = 0
        else:
            target_page = max(0, min(self.current_page, self.total_pages - 1))
        new_batch_index = target_page // self.thumbnail_batch_size
        if new_batch_index != self.current_thumbnail_batch:
            print(f"Auto-switching to batch {new_batch_index} for page {target_page}")
            self.load_thumbnail_batch(new_batch_index)

    def load_thumbnail_batch(self, batch_index, preserve_scroll=False, scroll_direction=None):
        """Load a batch of thumbnails with improved state management."""
        print(f"Loading batch {batch_index} (pages {batch_index * self.thumbnail_batch_size + 1}-{min((batch_index + 1) * self.thumbnail_batch_size, self.total_pages)})")
        if self._batch_load_in_progress and batch_index != self.current_thumbnail_batch:
            print(f"Batch load in progress, queuing batch {batch_index}")
            self.root.after(500, lambda: self.load_thumbnail_batch(batch_index, preserve_scroll, scroll_direction))
            return
        if hasattr(self, '_revert_job') and self._revert_job:
            self.root.after_cancel(self._revert_job)
            self._revert_job = None
        was_user_scrolling = getattr(self, '_user_scrolling', False)
        was_user_navigating = getattr(self, '_user_batch_navigation', False)
        mouse_in_canvas = getattr(self, '_mouse_in_canvas', False)
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
            self._batch_load_in_progress = False
            return
        current_batch_size = end_page - start_page
        self._user_scrolling = was_user_scrolling
        self._user_batch_navigation = was_user_navigating
        self._mouse_in_canvas = mouse_in_canvas
        self._setup_scroll_behavior(current_batch_size)
        self.thumbnail_placeholders = {}
        for page_number in range(start_page, end_page):
            placeholder_label = ctk.CTkLabel(self.inner_thumbnail_frame, text=f"Loading Page {page_number + 1}...")
            placeholder_label.page_number = page_number
            placeholder_label.pack(pady=5, padx=50)
            self.thumbnail_placeholders[page_number] = placeholder_label
            self.thumbnails.append(placeholder_label)
            thumb_color.append(placeholder_label)
        self.update_scroll_region()
        def load_batch_worker():
            """Worker thread to load thumbnail images."""
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
                    self.inner_thumbnail_frame.after(0, lambda pn=page_number, ph=photo: self.update_thumbnail_placeholder(pn, ph))
                except Exception as e:
                    print(f"Error rendering thumbnail for page {page_number}: {e}")
                    self.inner_thumbnail_frame.after(0, lambda pn=page_number: self.update_thumbnail_error(pn))
            self.inner_thumbnail_frame.after(100, self.update_scroll_region)
            if preserve_scroll and scroll_direction:
                def set_scroll_position():
                    try:
                        if scroll_direction == "next":
                            self.thumbnail_canvas.yview_moveto(0.0)
                        elif scroll_direction == "prev":
                            self.thumbnail_canvas.yview_moveto(0.8)  # Closer to bottom for prev
                        if was_user_scrolling and mouse_in_canvas:
                            self.thumbnail_canvas.bind_all("<MouseWheel>", self.on_thumbnail_scroll)
                    except Exception as e:
                        print(f"Error setting scroll position: {e}")
                self.inner_thumbnail_frame.after(300, set_scroll_position)             
            else:
                current_batch_start = batch_index * self.thumbnail_batch_size
                current_batch_end = current_batch_start + self.thumbnail_batch_size
                if (current_batch_start <= self.current_page < current_batch_end and 
                    not self._user_batch_navigation and 
                    self._manual_batch_selection is None):
                    self.inner_thumbnail_frame.after(300, lambda: self.update_thumbnail_selection(self.current_page))
            self.inner_thumbnail_frame.after(400, lambda: setattr(self, 'thumbnails_ready', True))
            self.inner_thumbnail_frame.after(500, lambda: setattr(self, '_batch_load_in_progress', False))
        threading.Thread(target=load_batch_worker, daemon=True).start()

    def _setup_scroll_behavior(self, current_batch_size):
        """Setup scroll behavior based on current batch size."""
        if self._user_batch_navigation:
            return
        self.thumbnail_canvas.unbind("<Enter>")
        self.thumbnail_canvas.unbind("<Leave>")
        self.thumbnail_canvas.unbind_all("<MouseWheel>")
        if current_batch_size > 6:
            def start_scroll(e):
                self._user_scrolling = True
                self._user_batch_navigation = True
                self._mouse_in_canvas = True
                self._auto_revert_disabled = True
                self.thumbnail_canvas.bind_all("<MouseWheel>", self.on_thumbnail_scroll)
                if hasattr(self, '_revert_job') and self._revert_job:
                    self.root.after_cancel(self._revert_job)
                    self._revert_job = None
            
            def end_scroll(e):
                self._mouse_in_canvas = False
                self.root.after(3000, self._schedule_potential_revert)
            
            self.thumbnail_canvas.bind("<Enter>", start_scroll)
            self.thumbnail_canvas.bind("<Leave>", end_scroll)

    def _schedule_potential_revert(self):
        """Schedule a potential revert to page-based batch, but only if user is truly inactive."""
        if (not self._user_scrolling and 
            not self._user_batch_navigation and 
            not self._auto_revert_disabled and
            not self._batch_load_in_progress):
            page_batch = self.current_page // self.thumbnail_batch_size
            if page_batch != self.current_thumbnail_batch:
                print(f"Scheduling revert to page-based batch {page_batch}")
                self._revert_job = self.root.after(2000, lambda: self._execute_revert(page_batch))

    def _execute_revert(self, target_batch):
        """Execute the revert to page-based batch."""
        if (not self._user_scrolling and 
            not self._user_batch_navigation and 
            not self._batch_load_in_progress and
            not self._auto_revert_disabled):
            print(f"Reverting to page-based batch {target_batch}")
            self._manual_batch_selection = None  # Clear manual selection
            self.load_thumbnail_batch(target_batch)

    def select_page(self, page_number):
        """Handle page selection without interfering with thumbnail navigation."""
        if 0 <= page_number < len(self.pdf_document):
            print(f"Selecting page: {page_number} (0-based), Display: {page_number + 1}")
            self.current_page = page_number
            if hasattr(self, 'page_drawings'):
                if isinstance(self.page_drawings, list):
                    self.current_page_drawings = [d for d in self.page_drawings if isinstance(d, dict) and d.get('page') == page_number]
            first_page = self.pdf_document[self.current_page]
            self.page_width, self.page_height = first_page.rect.width, first_page.rect.height
            self.render_page(self.current_page)
            self.update_page_display()
            current_batch_start = self.current_thumbnail_batch * self.thumbnail_batch_size
            current_batch_end = current_batch_start + self.thumbnail_batch_size
            if current_batch_start <= page_number < current_batch_end:
                self.update_thumbnail_selection(page_number)
            else:
                if not self._user_batch_navigation and self._manual_batch_selection is None:
                    needed_batch = page_number // self.thumbnail_batch_size
                    print(f"Auto-switching to batch {needed_batch} for page selection")
                    self.load_thumbnail_batch(needed_batch)
                else:
                    print(f"Page {page_number} not in current batch {self.current_thumbnail_batch}, preserving user navigation")
        else:
            print(f"Invalid page number: {page_number}. Total pages: {len(self.pdf_document)}")

    def update_thumbnail_selection(self, page_number):
        """Update the highlight of the selected thumbnail without batch changes."""
        if page_number is None or page_number < 0 or page_number >= self.total_pages:
            page_number = 0
        current_batch_start = self.current_thumbnail_batch * self.thumbnail_batch_size
        current_batch_end = current_batch_start + self.thumbnail_batch_size
        if not (current_batch_start <= page_number < current_batch_end):
            if not self._user_batch_navigation and self._manual_batch_selection is None:
                needed_batch = page_number // self.thumbnail_batch_size
                if needed_batch != self.current_thumbnail_batch:
                    print(f"Switching to batch {needed_batch} for thumbnail selection")
                    self.load_thumbnail_batch(needed_batch)
                    return
            else:
                print(f"Page {page_number} not in current batch {self.current_thumbnail_batch}, but user has control")
                return
        for label in thumb_color:
            if hasattr(label, 'page_number'):
                label.configure(
                    text=f"Page {label.page_number + 1}",
                    text_color="black",
                    fg_color="transparent",
                    corner_radius=0)
        for label in thumb_color:
            if hasattr(label, 'page_number') and label.page_number == page_number:
                label.configure(
                    text="Selected Page", 
                    text_color="red",    
                    fg_color="#c41818", 
                    corner_radius=4, 
                    compound="center")
                self.selected_label_info = label
                if not self._user_batch_navigation:
                    self.root.after(100, lambda: self.scroll_to_thumbnail(label, page_number))
                break
    def update_thumbnail_placeholder(self, page_number, photo):
        """Update a placeholder label with the actual thumbnail image."""
        if page_number in self.thumbnail_placeholders:
            placeholder = self.thumbnail_placeholders[page_number]
            placeholder.configure(image=photo, text=f"Page {page_number + 1}")
            placeholder.image = photo
            placeholder.bind("<Button-1>", self.create_page_selection_handler(page_number))
    def update_thumbnail_error(self, page_number):
        """Update a placeholder label to show an error."""
        if page_number in self.thumbnail_placeholders:
            placeholder = self.thumbnail_placeholders[page_number]
            placeholder.configure(text=f"Error Page {page_number + 1}")
            placeholder.bind("<Button-1>", self.create_page_selection_handler(page_number))
    def create_page_selection_handler(self, page_number):
        """Return a handler function to navigate to the selected page."""
        def handler(event):
            self._manual_batch_selection = None
            self._auto_revert_disabled = False
            print(f"Thumbnail {page_number} clicked. Current page before: {self.current_page}")
            self.select_page(page_number)
            print(f"Current page after: {self.current_page}")
        return handler
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
    def go_to_page(self, event=None):
        """Handle manual page entry navigation"""
        try:
            entered_page = self.page_entry.get().strip()
            if not entered_page:
                return             
            page_number = int(entered_page) - 1  # Convert to zero-based index
            if 0 <= page_number < len(self.pdf_document):
                self.current_page = page_number
                self.render_page(self.current_page)
                self.update_thumbnail_selection(self.current_page)
                self.check_and_update_thumbnail_batch()
            else:
                self.update_page_display()
                messagebox.showerror("Error", f"Invalid page number. Enter a number between 1 and {len(self.pdf_document)}.")
        except ValueError:
            self.update_page_display()
            messagebox.showerror("Error", "Enter a valid page number.")
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
        pageinfo = page_number
        page = self.pdf_document.load_page(page_number)
        matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
        pix = page.get_pixmap(matrix=matrix)
        img = Image.open(io.BytesIO(pix.tobytes("png")))
        if self.is_inverted:
            img = ImageOps.invert(img.convert("RGB"))
        img_tk = ImageTk.PhotoImage(img)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
        self.canvas.img_tk = img_tk  # Keep a reference to prevent garbage collection
        self.page_width, self.page_height = pix.width, pix.height
        self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
        self.root.after(0, self.hide_loader)
        first_page = self.pdf_document[self.current_page]
        self.page_width_redact, self.page_height_recdact = first_page.rect.width, first_page.rect.height
        if not hasattr(self, 'redact_visible'):
            self.redact_visible = True
        if not hasattr(self, 'all_page_rectangles') or self.view_redact == "true":
            self.redraw_black_rectangles_from_api()
            self.redact_visible = True
        if hasattr(self, 'redact_visible') and self.redact_visible:
            self._draw_rectangles_for_current_page()
        if self.rendered_page_count == 0:
            self.rendered_page_count += 1
        self.redraw_sticky_notes()
        self.redraw_text_annotations()
        self.redraw_text_with_background()
        self.redraw_polygons()
        self.redraw_all_annotations()
        self.redraw_image_overlays(page_number)
        self.redraw_freehand_drawings()
        self.canvas.config(scrollregion=self.canvas.bbox("all"))











































































# import io
# import tkinter as tk
# import tkinter.ttk as ttk
# from tkinter import filedialog, messagebox, Toplevel
# import fitz
# import textwrap
# from PIL import Image, ImageTk, ImageOps
# import requests
# from urllib.parse import urlparse
# import socket
# import threading
# import sys
# from protocol_handler import ProtocolHandler

# class StickyNotesPDFApp:
#     SOCKET_PORT = 65432
#     def __init__(self, root):
#         self.root = root
#         self.root.title("Atic PDF Editor")
#         self.zoom_factor = 1.0
#         self.sticky_note_mode = False  
#         self.highlight_mode = False 
#         self.change_history = [] 
#         self.sticky_notes = {} 
#         self.thumbnails = [] 
#         self.pdf_document = None
#         self.current_page = None
#         self.is_inverted = False
#         self.create_widgets() 
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
#         self.canvas.bind("<Motion>", self.on_mouse_hover)  
#         self.active_tooltip = None 
#         self.page_width = 0
#         self.page_height = 0
#         self.duplicate_windows = []  # List to track active duplicate windows
#         self.root.protocol("WM_DELETE_WINDOW", self.close_main_window)    
#     def create_widgets(self):
#         style = ttk.Style()
#         style.configure(
#             "Modern.TButton",
#             font=("Arial", 12),
#             padding=(2, 2),  # Minimize padding for a compact look
#             relief="flat",
#             background="lightgray",
#             foreground="black",
#             borderwidth=1,)
#         style.map(
#             "Modern.TButton",
#             background=[("active", "darkgray"), ("!disabled", "lightgray")],
#             foreground=[("active", "white")],)
#         toolbar = tk.Frame(self.root)
#         toolbar.pack(fill=tk.X, pady=8)
#         def create_button(parent, text, command, tooltip_text=""):
#             button_frame = tk.Frame(parent, width=50, height=30)  # Set fixed width and height
#             button_frame.pack_propagate(False)  # Prevent resizing to fit content
#             button_frame.pack(side=tk.LEFT, padx=3)           
#             button = ttk.Button(
#                 button_frame,
#                 text=text,
#                 style="Modern.TButton",
#                 command=command)
#             button.pack(fill=tk.BOTH, expand=True)  # Fill the frame
#             button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
#             button.bind("<Leave>", self.hide_tooltip)
#             return button
#         create_button(toolbar, "📄+", self.create_duplicate_window, "New Window")
#         create_button(toolbar, "↩️", self.undo_change, "Undo")
#         create_button(toolbar, "✒️", self.enable_highlight_mode, "Highlight")
#         create_button(toolbar, "📌", self.toggle_sticky_note_mode, "Sticky Note")
#         canvas_frame = tk.Frame(self.root)
#         canvas_frame.pack(fill=tk.BOTH, expand=True)
#         self.thumbnail_frame = tk.Frame(canvas_frame, width=150, bg="lightgray")
#         self.thumbnail_frame.pack(side=tk.LEFT, fill=tk.Y)
#         self.thumbnail_canvas = tk.Canvas(self.thumbnail_frame, bg="lightgray", width=200)
#         self.thumbnail_scrollbar = tk.Scrollbar(self.thumbnail_frame, orient=tk.VERTICAL, command=self.thumbnail_canvas.yview)
#         self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
#         self.thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
#         self.thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
#         self.inner_thumbnail_frame = tk.Frame(self.thumbnail_canvas, bg="lightgray")
#         self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
#         self.canvas = tk.Canvas(canvas_frame, bg="lightgray", width=900, height=650)
#         self.h_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
#         self.v_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
#         self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
#         self.h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
#         self.v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
#         self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
#         self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
#         self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
#     def button_tooltip(self, event, button_text, tooltip_text):
#         """Display tooltip when hovering over a button."""
#         if self.active_tooltip:
#             self.active_tooltip.destroy() # to destroy automatiacally each second
#         tooltip = tk.Toplevel(self.root)
#         tooltip.wm_overrideredirect(True) # it used for closing tooltip
#         tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")  # text Position near the mouse hover
#         label = tk.Label(tooltip, text=tooltip_text, background="light yellow", relief="solid", padx=5, pady=5)
#         label.pack()
#         self.active_tooltip = tooltip
#     def hide_tooltip(self, event):
#         """Hide tooltip when the mouse leaves the button."""
#         if self.active_tooltip: 
#             self.active_tooltip.destroy()
#             self.active_tooltip = None
#     def load_pdf(self, file_path=None):
#         if not file_path:
#             file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
#         try:
#             parsed = urlparse(file_path)
#             if parsed.scheme in ('http', 'https'):
#                 response = requests.get(file_path)
#                 response.raise_for_status()  # Raise an exception for bad status codes
#                 pdf_data = response.content       
#                 self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
#             else:
#                 self.pdf_document = fitz.open(file_path)
#             self.pdf_path = file_path  
#             self.current_page = 0
#             self.is_inverted = False
#             self.render_thumbnails()
#             self.render_page(self.current_page)
#             self.update_thumbnail_selection()
#         except Exception as e:
#             messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
#             return
#     def render_thumbnails(self):
#         """Render the thumbnails of all PDF pages with fixed dimensions."""
#         if not self.pdf_document:
#             return     
#         for widget in self.inner_thumbnail_frame.winfo_children():
#             widget.destroy()    
#         self.thumbnails = []
#         self.thumbnail_labels = []        
#         thumbnail_width = 150 
#         thumbnail_height = 200  
#         for page_number in range(len(self.pdf_document)):
#             page = self.pdf_document.load_page(page_number)
#             pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))  # Initial scale for rendering
#             img = Image.open(io.BytesIO(pix.tobytes("png")))
#             img_resized = ImageOps.fit(img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
#             img_tk = ImageTk.PhotoImage(img_resized)
#             self.thumbnails.append(img_tk)
#             frame = tk.Frame(self.inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
#             frame.pack(pady=5, padx=20)
#             frame.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
#             label = tk.Label(frame, image=img_tk, bg="lightgray")
#             label.pack()
#             label.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
#             self.thumbnail_labels.append(frame)
#         self.update_thumbnail_selection()  # Highlight the initial page
#         self.inner_thumbnail_frame.update_idletasks()
#         self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
#     def update_thumbnail_selection(self):
#         """Update the highlight of the selected thumbnail."""
#         for i, frame in enumerate(self.thumbnail_labels):
#             if i == self.current_page:
#                 frame.config(highlightbackground="orange", highlightcolor="orange")
#             else:
#                 frame.config(highlightbackground="lightgray", highlightcolor="lightgray")
#     def select_page(self, page_number):
#         """Navigate to the selected page."""
#         self.current_page = page_number
#         self.render_page(page_number)
#         self.update_thumbnail_selection()
#     def create_duplicate_window(self):
#         """Creates a duplicate window to display a PDF independently."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF is loaded to view in secondary window.")
#             return
#         duplicate_window = Toplevel(self.root)
#         duplicate_window.title("Secondary PDF Viewer")
#         duplicate_window.geometry("900x650")
#         self.duplicate_windows.append(duplicate_window)
#         toolbar = tk.Frame(duplicate_window)
#         toolbar.pack(fill=tk.X, pady=8)
#         thumbnail_frame = tk.Frame(duplicate_window)
#         thumbnail_frame.pack(side=tk.LEFT, fill=tk.Y)
#         thumbnail_canvas = tk.Canvas(thumbnail_frame, bg="lightgray", width=200)
#         thumbnail_scrollbar = tk.Scrollbar(
#             thumbnail_frame, orient=tk.VERTICAL, command=thumbnail_canvas.yview)
#         thumbnail_canvas.configure(yscrollcommand=thumbnail_scrollbar.set)
#         thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
#         thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
#         inner_thumbnail_frame = tk.Frame(thumbnail_canvas, bg="lightgray")
#         thumbnail_canvas.create_window((0, 0), window=inner_thumbnail_frame, anchor="nw")
#         pdf_frame = tk.Frame(duplicate_window)
#         pdf_frame.pack(fill=tk.BOTH, expand=True, side=tk.RIGHT)
#         pdf_canvas = tk.Canvas(pdf_frame, bg="lightgray", width=700, height=600)
#         pdf_h_scrollbar = tk.Scrollbar(pdf_frame, orient=tk.HORIZONTAL, command=pdf_canvas.xview)
#         pdf_v_scrollbar = tk.Scrollbar(pdf_frame, orient=tk.VERTICAL, command=pdf_canvas.yview)
#         pdf_canvas.configure(
#             xscrollcommand=pdf_h_scrollbar.set, 
#             yscrollcommand=pdf_v_scrollbar.set)
#         pdf_canvas.grid(row=0, column=0, sticky="nsew")  # Canvas fills the available space
#         pdf_h_scrollbar.grid(row=1, column=0, sticky="ew")  # Horizontal scrollbar below the canvas
#         pdf_v_scrollbar.grid(row=0, column=1, sticky="ns")  
#         pdf_frame.grid_rowconfigure(0, weight=1)
#         pdf_frame.grid_columnconfigure(0, weight=1)
#         duplicate_pdf_document = self.pdf_document
#         duplicate_current_page = self.current_page
#         duplicate_zoom_factor = self.zoom_factor
#         duplicate_is_inverted = self.is_inverted
#         def render_duplicate_page(page_number):
#             if not duplicate_pdf_document:
#                 return
#             page = duplicate_pdf_document.load_page(page_number)
#             matrix = fitz.Matrix(duplicate_zoom_factor, duplicate_zoom_factor)
#             pix = page.get_pixmap(matrix=matrix)
#             img = Image.open(io.BytesIO(pix.tobytes("png")))
#             if duplicate_is_inverted:
#                 img = ImageOps.invert(img.convert("RGB"))
#             img_tk = ImageTk.PhotoImage(img)
#             pdf_canvas.delete("all")
#             pdf_canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
#             pdf_canvas.img_tk = img_tk
#             pdf_canvas.config(scrollregion=(0, 0, pix.width, pix.height))
#         def duplicate_render_thumbnails():
#             if not self.pdf_document:
#                 return
#             for widget in inner_thumbnail_frame.winfo_children():
#                 widget.destroy()
#             thumbnail_width = 150
#             thumbnail_height = 200
#             for page_number in range(len(self.pdf_document)):
#                 page = self.pdf_document.load_page(page_number)
#                 pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
#                 img = Image.open(io.BytesIO(pix.tobytes("png")))
#                 img_resized = ImageOps.fit(
#                     img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
#                 img_tk = ImageTk.PhotoImage(img_resized)
#                 frame = tk.Frame(inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
#                 frame.pack(pady=5, padx=20)
#                 frame.bind("<Button-1>", lambda e, p=page_number: select_page(p))
#                 label = tk.Label(frame, image=img_tk, bg="lightgray")
#                 label.pack()
#                 label.bind("<Button-1>", lambda e, p=page_number: select_page(p))
#                 frame.img_tk = img_tk
#                 frame.tag = page_number  # Tag for highlighting
#             inner_thumbnail_frame.update_idletasks()
#             thumbnail_canvas.configure(scrollregion=thumbnail_canvas.bbox("all"))
#         def highlight_thumbnail(page_number):
#             for frame in inner_thumbnail_frame.winfo_children():
#                 if hasattr(frame, "tag") and frame.tag == page_number:
#                     frame.config(bg="orange", highlightbackground="orange")
#                 else:
#                     frame.config(bg="lightgray", highlightbackground="lightgray")
#         def select_page(page_number):
#             render_duplicate_page(page_number)
#             highlight_thumbnail(page_number)
#         def zoom_in():
#             nonlocal duplicate_zoom_factor
#             duplicate_zoom_factor += 0.2
#             render_duplicate_page(duplicate_current_page)
#         def zoom_out():
#             nonlocal duplicate_zoom_factor
#             if duplicate_zoom_factor > 0.4:
#                 duplicate_zoom_factor -= 0.2
#                 render_duplicate_page(duplicate_current_page)
#         def prev_page():
#             nonlocal duplicate_current_page
#             if duplicate_current_page > 0:
#                 duplicate_current_page -= 1
#                 render_duplicate_page(duplicate_current_page)
#         def next_page():
#             nonlocal duplicate_current_page
#             if duplicate_current_page < len(duplicate_pdf_document) - 1:
#                 duplicate_current_page += 1
#                 render_duplicate_page(duplicate_current_page)
#         def rotate_90clockwise():
#             nonlocal duplicate_current_page
#             if not self.pdf_document:
#                 return
#             page = self.pdf_document[duplicate_current_page]
#             page.set_rotation((page.rotation + 90) % 360) 
#             render_duplicate_page(duplicate_current_page) 
#         def create_button(parent, text, command, tooltip_text):
#             button = ttk.Button(parent, text=text, style="Modern.TButton", command=command)
#             button.pack(side=tk.LEFT, padx=5)
#             button.bind("<Enter>", lambda event: self.button_tooltip(event, text, tooltip_text))
#             button.bind("<Leave>", self.hide_tooltip)
#         create_button(toolbar, "🔍 -", zoom_out, "Zoom Out")
#         create_button(toolbar, "🔍 +", zoom_in, "Zoom In")
#         create_button(toolbar, "⬅️", prev_page, "Previous Page")
#         create_button(toolbar, "➡️", next_page, "Next Page")
#         create_button(toolbar, "⮧", rotate_90clockwise, "Rotate 90° Right")
#         duplicate_render_thumbnails()
#         render_duplicate_page(duplicate_current_page)
#         def close_duplicate_window():
#             self.duplicate_windows.remove(duplicate_window)
#             duplicate_window.destroy()
#         duplicate_window.protocol("WM_DELETE_WINDOW", close_duplicate_window)
#     def close_main_window(self):
#         """Closes the main window only if there are no duplicate windows open."""
#         if self.duplicate_windows:
#             messagebox.showwarning("Warning", "Please close all duplicate windows before exiting the main window.")
#         else:
#             self.root.destroy()
#     def render_page(self, page_number):
#         """Render a PDF page to the canvas with the current zoom factor."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         page = self.pdf_document.load_page(page_number)
#         matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
#         pix = page.get_pixmap(matrix=matrix)
#         img = Image.open(io.BytesIO(pix.tobytes("png")))
#         if self.is_inverted:
#             img = ImageOps.invert(img.convert("RGB"))
#         img_tk = ImageTk.PhotoImage(img)
#         self.canvas.delete("all")
#         self.canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
#         self.canvas.img_tk = img_tk
#         self.page_width, self.page_height = pix.width, pix.height
#         self.canvas.config(scrollregion=(0, 0, self.page_width, self.page_height))
#         self.redraw_sticky_notes()
#     def enable_sticky_note_mode(self):
#         """ Activate sticky note mode """
#         self.sticky_note_mode = True  
#         self.highlight_mode = False  
#         self.canvas.unbind("<B1-Motion>") 
#         self.canvas.unbind("<ButtonRelease-1>")
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
#     def redraw_sticky_notes(self):
#         """Redraw sticky notes after rendering the page."""
#         self.canvas.delete("sticky_note")
#         emoji_fill = "white" if self.is_inverted else "black"  
#         for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
#             if page_num == self.current_page:
#                 x_position = x_scaled * self.zoom_factor
#                 y_position = y_scaled * self.zoom_factor
#                 self.canvas.create_text(
#                     x_position + 1, y_position + 1, text="📌", font=("Arial", 16),
#                     fill="white", tags="sticky_note_shadow")
#                 self.canvas.create_text(
#                     x_position, y_position, text="📌", font=("Arial", 16),
#                     fill=emoji_fill, tags="sticky_note")
#     def on_canvas_click(self, event):
#         """Add a sticky note at the clicked position on the canvas."""
#         if not self.pdf_document or not self.sticky_note_mode:
#             return
#         x = self.canvas.canvasx(event.x)
#         y = self.canvas.canvasy(event.y)
#         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
#             return  # Clicked outside the PDF page area
#         note_text = self.ask_for_note_text(x, y)
#         if not note_text:
#             print("No note text entered.")
#             return  # No text entered
#         x_scaled = x / self.zoom_factor
#         y_scaled = y / self.zoom_factor
#         self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
#         self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
#         self.canvas.create_text(x, y, text="📌", font=("Arial", 16))
#         self.sticky_note_mode = False
#     def ask_for_note_text(self, x, y):
#         """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
#         dialog = tk.Toplevel(self.root) 
#         dialog.title("Enter Sticky Note")
#         dialog.geometry("400x250") 
#         dialog.configure(bg="#f9f9f9") 
#         dialog.resizable(False, False)
#         label = tk.Label(
#             dialog, text="Enter your note:", font=("Arial", 14, "bold"), bg="#f9f9f9")
#         label.pack(pady=(15, 10))
#         text_box = tk.Text(dialog, wrap=tk.WORD, height=6, width=40, font=("Arial", 12), relief="solid")
#         text_box.pack(padx=15, pady=5, fill=tk.X)
#         text_box.focus_set()
#         note_text_var = tk.StringVar()
#         def on_ok_click():
#             note_text = text_box.get("1.0", tk.END).strip()  # Get text from the Text widget
#             if note_text:
#                 note_text_var.set(note_text)  # Save the entered note text
#                 dialog.destroy()
#             else:
#                 messagebox.showwarning(
#                     "Empty Note", "You must enter some text to save the sticky note.")
#         def create_rounded_button(parent, text, bg_color, fg_color, command):
#             canvas = tk.Canvas(parent, width=120, height=40, bg="#f9f9f9", highlightthickness=0)
#             canvas.pack(side=tk.LEFT, padx=10)
#             canvas.create_oval(10, 10, 40, 40, fill=bg_color, outline=bg_color)
#             canvas.create_oval(80, 10, 110, 40, fill=bg_color, outline=bg_color)
#             canvas.create_rectangle(25, 10, 95, 40, fill=bg_color, outline=bg_color)
#             button_text = canvas.create_text(60, 25, text=text, fill=fg_color, font=("Arial", 12, "bold"))
#             def on_click(event):
#                 command()
#             canvas.tag_bind(button_text, "<Button-1>", on_click)
#             canvas.tag_bind("all", "<Enter>", lambda e: canvas.configure(cursor="hand2"))
#             canvas.tag_bind("all", "<Button-1>", on_click)
#             return canvas
#         buttons_frame = tk.Frame(dialog, bg="#f9f9f9")
#         buttons_frame.pack(side=tk.BOTTOM, pady=15)
#         create_rounded_button(buttons_frame, "OK", bg_color="#4CAF50", fg_color="white", command=on_ok_click)
#         create_rounded_button(buttons_frame, "Cancel", bg_color="#F44336", fg_color="white", command=dialog.destroy)
#         dialog.grab_set()
#         dialog.wait_window()
#         self.sticky_note_mode = False
#         return note_text_var.get() or None
#     def undo_change(self):
#         if not self.change_history:
#             print("No actions to undo.")
#             return
#         last_action = self.change_history.pop()
#         print(f"Undoing action: {last_action}")
#         action_type = last_action[0]
#         if action_type == "sticky_note":
#             _, page, x_scaled, y_scaled, _ = last_action
#             if (page, x_scaled, y_scaled) in self.sticky_notes:
#                 del self.sticky_notes[(page, x_scaled, y_scaled)]
#                 self.render_page(self.current_page)
#         elif action_type == "highlight":
#             _, page, annot_id = last_action
#             page_obj = self.pdf_document[page]
#             annot = page_obj.first_annot
#             while annot:
#                 if annot.info.get('id') == annot_id:
#                     page_obj.delete_annot(annot)
#                     self.render_page(self.current_page)
#                     print(f"Highlight with ID {annot_id} removed.")
#                     break
#                 annot = annot.next
#             else:
#                 print(f"No annotation found with ID {annot_id}. Undo failed.")
#         else:
#             print(f"Unknown action type: {action_type}")
#     def enable_highlight_mode(self):
#         """ Activate highlight mode """
#         self.highlight_mode = True
#         self.sticky_note_mode = False
#         self.canvas.unbind("<Button-1>")
#         self.canvas.bind("<Button-1>", self.start_rectangle)
#         self.canvas.bind("<B1-Motion>", self.draw_rectangle)
#         self.canvas.bind("<ButtonRelease-1>", self.finalize_highlight)
#         self.start_x, self.start_y = None, None
#     def start_rectangle(self, event):
#         """Start a rectangle selection for highlighting"""
#         self.start_x = self.canvas.canvasx(event.x)
#         self.start_y = self.canvas.canvasy(event.y)
#         self.rectangle_id = self.canvas.create_rectangle(
#             self.start_x, self.start_y, self.start_x, self.start_y, outline="yellow")
#     def draw_rectangle(self, event):
#         """Draw the rectangle dynamically as the mouse is dragged"""
#         current_x = self.canvas.canvasx(event.x)
#         current_y = self.canvas.canvasy(event.y)
#         self.canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)
#     def finalize_highlight(self, event):
#         """Finalize the highlight on the PDF and deactivate highlight mode."""
#         if self.start_x is None or self.start_y is None:
#             return
#         end_x = self.canvas.canvasx(event.x) / self.zoom_factor 
#         end_y = self.canvas.canvasy(event.y) / self.zoom_factor
#         start_x = self.start_x / self.zoom_factor 
#         start_y = self.start_y / self.zoom_factor
#         rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
#         page = self.pdf_document[self.current_page]
#         try:
#             annot = page.add_highlight_annot(rect)
#             annot.update()
#             annot_id = annot.info.get('id')
#             if annot_id:
#                 self.change_history.append(("highlight", self.current_page, annot_id))
#             else:
#                 print("Warning: Annotation ID not found. Undo may fail.")
#         except Exception as e:
#             messagebox.showerror("Error", f"Failed to add highlight: {e}")
#             return
#         self.render_page(self.current_page)
#         self.highlight_mode = False
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")
#     def on_mouse_hover(self, event):
#         """Show sticky note text when hovering over emoji."""
#         if not self.pdf_document:
#             return
#         x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)  # Adjust for scrolling
#         tooltip_shown = False
#         for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
#             if page_num == self.current_page:
#                 x_position = x_scaled * self.zoom_factor
#                 y_position = y_scaled * self.zoom_factor
#                 if abs(x - x_position) < 20 and abs(y - y_position) < 20:  # Adjust hover sensitivity
#                     if not tooltip_shown:
#                         self.show_tooltip(event.x_root, event.y_root, text)  # Use root coordinates for tooltip
#                         tooltip_shown = True
#                     break
#         if not tooltip_shown and getattr(self, "active_tooltip", None):
#             self.active_tooltip.destroy()
#             self.active_tooltip = None
#     def show_tooltip(self, x, y, text):
#         """ Display the sticky note text as a tooltip """
#         if getattr(self, "active_tooltip", None):
#             self.active_tooltip.destroy()
#         wrapped_text = textwrap.fill(text, width=50) # ensuring that the line end at 50 characters 
#         tooltip = tk.Toplevel(self.root)
#         tooltip.wm_overrideredirect(True)
#         tooltip.wm_geometry(f"+{int(x) + 10}+{int(y) + 10}")  # Ensure integer coordinates
#         label = tk.Label(tooltip, text=wrapped_text, background="light yellow", relief="solid", padx=5, pady=5)
#         label.pack()
#         self.active_tooltip = tooltip
#     def toggle_sticky_note_mode(self):
#         """Toggle sticky note mode"""
#         if self.sticky_note_mode:
#             self.sticky_note_mode = False
#             self.canvas.unbind("<Button-1>")
#         else:
#             self.enable_sticky_note_mode()
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

# if __name__ == "__main__":
#     root = tk.Tk()
#     app = StickyNotesPDFApp(root)
#     root.mainloop()
































# import io
# import tkinter as tk
# import tkinter.ttk as ttk
# from tkinter import filedialog, messagebox, Toplevel
# import fitz
# from PIL import Image, ImageTk, ImageOps
# import requests
# from urllib.parse import urlparse
# import socket
# import threading
# import sys
# from protocol_handler import ProtocolHandler

# class StickyNotesPDFApp:
#     SOCKET_PORT = 65432
#     def __init__(self, root):
#         self.root = root
#         self.root.title("Atic PDF Editor")
#         self.zoom_factor = 1.0
#         self.sticky_note_mode = False  
#         self.highlight_mode = False 
#         self.change_history = []  
#         self.sticky_notes = {}  
#         self.thumbnails = [] 
#         self.pdf_document = None
#         self.current_page = None
#         self.is_inverted = False
#         self.create_widgets()  
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
#         self.canvas.bind("<Motion>", self.on_mouse_hover)  
#         self.active_tooltip = None 
#         self.page_width = 0
#         self.page_height = 0
#         self.duplicate_windows = []  # List to track active duplicate windows
#         self.root.protocol("WM_DELETE_WINDOW", self.close_main_window)
#         self.setup_ipc_server()      
#         if len(sys.argv) > 1:
#             pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
#             self.handle_url(pdf_url)
#     def create_widgets(self):
#         style = ttk.Style()
#         style.configure("Modern.TButton",
#             font=("Arial", 12),padding=(2, 2),
#             relief="flat",background="lightgray",
#             foreground="black",borderwidth=1,)
#         style.map(
#             "Modern.TButton",
#             background=[("active", "darkgray"), ("!disabled", "lightgray")],
#             foreground=[("active", "white")],)
#         toolbar = tk.Frame(self.root)
#         toolbar.pack(fill=tk.X, pady=8)
#         def create_button(parent, text, command, tooltip_text=""):
#             button_frame = tk.Frame(parent, width=50, height=30)  # Set fixed width and height
#             button_frame.pack_propagate(False)  # Prevent resizing to fit content
#             button_frame.pack(side=tk.LEFT, padx=3)
#             button = ttk.Button(
#                 button_frame,text=text,
#                 style="Modern.TButton",
#                 command=command)
#             button.pack(fill=tk.BOTH, expand=True)  # Fill the frame
#             button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
#             button.bind("<Leave>", self.hide_tooltip)
#             return button
#         create_button(toolbar, "🚃", self.create_duplicate_window, "New Window")
#         create_button(toolbar, "🔍 -", self.zoom_out, "Zoom Out")
#         create_button(toolbar, "🔍 +", self.zoom_in, "Zoom In")
#         create_button(toolbar, "⬅️", self.prev_page, "Previous Page")
#         create_button(toolbar, "➡️", self.next_page, "Next Page")
#         create_button(toolbar, "⮧", self.rotate_90clockwise, "Rotate 90° Right")
#         create_button(toolbar, "❖", self.best_fit, "Best Fit")
#         create_button(toolbar, "↔", self.best_width, "Best Width")
#         create_button(toolbar, "🌓", self.toggle_invert_colors, "Invert Colors")
#         canvas_frame = tk.Frame(self.root)
#         canvas_frame.pack(fill=tk.BOTH, expand=True)
#         self.thumbnail_frame = tk.Frame(canvas_frame, width=150, bg="lightgray")
#         self.thumbnail_frame.pack(side=tk.LEFT, fill=tk.Y)
#         self.thumbnail_canvas = tk.Canvas(self.thumbnail_frame, bg="lightgray", width=200)
#         self.thumbnail_scrollbar = tk.Scrollbar(self.thumbnail_frame, orient=tk.VERTICAL, command=self.thumbnail_canvas.yview)
#         self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
#         self.thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
#         self.thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
#         self.inner_thumbnail_frame = tk.Frame(self.thumbnail_canvas, bg="lightgray")
#         self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
#         self.canvas = tk.Canvas(canvas_frame, bg="lightgray", width=900, height=650)
#         self.h_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
#         self.v_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
#         self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
#         self.h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
#         self.v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
#         self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
#         self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
#         self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
#     def button_tooltip(self, event, button_text, tooltip_text):
#         if self.active_tooltip:
#             self.active_tooltip.destroy()
#         tooltip = tk.Toplevel(self.root)
#         tooltip.wm_overrideredirect(True)
#         tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")
#         label = tk.Label(tooltip, text=tooltip_text, background="light yellow", relief="solid", padx=5, pady=5)
#         label.pack()
#         self.active_tooltip = tooltip
#     def hide_tooltip(self, event):
#         """Hide tooltip when the mouse leaves the button."""
#         if self.active_tooltip: 
#             self.active_tooltip.destroy()
#             self.active_tooltip = None
#     def setup_ipc_server(self):
#         self.ipc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
#         try:
#             self.ipc_socket.bind(("localhost", self.SOCKET_PORT))
#             self.ipc_socket.listen(1)
#             threading.Thread(target=self.ipc_listener, daemon=True).start()
#         except socket.error:
#             if len(sys.argv) > 1:
#                 pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
#                 self.send_to_running_instance(pdf_url)
#             sys.exit()
#     def ipc_listener(self):
#         """Listen for incoming URLs and handle them."""
#         while True:
#             conn, _ = self.ipc_socket.accept()
#             with conn:
#                 data = conn.recv(1024).decode("utf-8")
#                 if data:
#                     self.root.after(0, self.handle_url, data)
#     def send_to_running_instance(self, url):
#         """Send the URL to the running instance."""
#         try:
#             with socket.create_connection(("localhost", self.SOCKET_PORT)) as client_socket:
#                 client_socket.sendall(url.encode("utf-8"))
#         except socket.error:
#             print("Failed to send URL to running instance.")
#     def handle_url(self, url):
#         """Handle a new URL (load the PDF)."""
#         try:
#             self.load_pdf(url)
#         except Exception as e:
#             print(f"Failed to load PDF: {e}")
#     def load_pdf(self, file_path=None):
#         try:
#             parsed = urlparse(file_path)
#             if parsed.scheme in ('http', 'https'):
#                 response = requests.get(file_path)
#                 response.raise_for_status()
#                 pdf_data = response.content       
#                 self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
#             self.pdf_path = file_path  
#             self.current_page = 0
#             self.is_inverted = False
#             self.render_thumbnails()
#             self.render_page(self.current_page)
#             self.update_thumbnail_selection()
#         except Exception as e:
#             messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
#             return
#     def render_thumbnails(self):
#         """Render the thumbnails of all PDF pages with fixed dimensions."""
#         if not self.pdf_document:
#             return      
#         for widget in self.inner_thumbnail_frame.winfo_children():
#             widget.destroy()     
#         self.thumbnails = []  
#         self.thumbnail_labels = []   
#         thumbnail_width = 150 
#         thumbnail_height = 200      
#         for page_number in range(len(self.pdf_document)):
#             page = self.pdf_document.load_page(page_number)
#             pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
#             img = Image.open(io.BytesIO(pix.tobytes("png")))
#             img_resized = ImageOps.fit(img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
#             img_tk = ImageTk.PhotoImage(img_resized)
#             self.thumbnails.append(img_tk)
#             frame = tk.Frame(self.inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
#             frame.pack(pady=5, padx=20)
#             frame.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
#             label = tk.Label(frame, image=img_tk, bg="lightgray")
#             label.pack()
#             label.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
#             self.thumbnail_labels.append(frame)    
#         self.update_thumbnail_selection()
#         self.inner_thumbnail_frame.update_idletasks()
#         self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
#     def update_thumbnail_selection(self):
#         """Update the highlight of the selected thumbnail."""
#         for i, frame in enumerate(self.thumbnail_labels):
#             if i == self.current_page:
#                 frame.config(highlightbackground="orange", highlightcolor="orange")
#             else:
#                 frame.config(highlightbackground="lightgray", highlightcolor="lightgray")           
#     def select_page(self, page_number):
#         """Navigate to the selected page."""
#         self.current_page = page_number
#         self.render_page(page_number)
#         self.update_thumbnail_selection()
#     def create_duplicate_window(self):
#         """Creates a duplicate window to display a PDF independently."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF is loaded to view in secondary window.")
#             return
#         duplicate_window = Toplevel(self.root)
#         duplicate_window.title("Secondary PDF Viewer")
#         duplicate_window.geometry("900x650")
#         self.duplicate_windows.append(duplicate_window)
#         toolbar = tk.Frame(duplicate_window)
#         toolbar.pack(fill=tk.X, pady=8)
#         thumbnail_frame = tk.Frame(duplicate_window)
#         thumbnail_frame.pack(fill=tk.Y, side=tk.LEFT)
#         thumbnail_canvas = tk.Canvas(thumbnail_frame, bg="lightgray", width=200)
#         thumbnail_scrollbar = tk.Scrollbar(
#             thumbnail_frame, orient=tk.VERTICAL, command=thumbnail_canvas.yview)
#         thumbnail_canvas.configure(yscrollcommand=thumbnail_scrollbar.set)
#         thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
#         thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
#         inner_thumbnail_frame = tk.Frame(thumbnail_canvas, bg="lightgray")
#         thumbnail_canvas.create_window((0, 0), window=inner_thumbnail_frame, anchor="nw")
#         pdf_frame = tk.Frame(duplicate_window)
#         pdf_frame.pack(fill=tk.BOTH, expand=True, side=tk.RIGHT)
#         pdf_canvas = tk.Canvas(pdf_frame, bg="lightgray", width=700, height=600)
#         pdf_canvas.pack(fill=tk.BOTH, expand=True)
#         pdf_h_scrollbar = tk.Scrollbar(
#             pdf_frame, orient=tk.HORIZONTAL, command=pdf_canvas.xview)
#         pdf_v_scrollbar = tk.Scrollbar(
#             pdf_frame, orient=tk.VERTICAL, command=pdf_canvas.yview)
#         pdf_canvas.configure(
#             xscrollcommand=pdf_h_scrollbar.set, yscrollcommand=pdf_v_scrollbar.set)
#         pdf_h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
#         pdf_v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
#         duplicate_pdf_document = self.pdf_document
#         duplicate_current_page = self.current_page
#         duplicate_zoom_factor = self.zoom_factor
#         duplicate_is_inverted = self.is_inverted
#         def render_duplicate_page(page_number):
#             if not self.pdf_document:
#                 return
#             page = self.pdf_document.load_page(page_number)
#             matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
#             pix = page.get_pixmap(matrix=matrix)
#             img = Image.open(io.BytesIO(pix.tobytes("png")))
#             if self.is_inverted:
#                 img = ImageOps.invert(img.convert("RGB"))
#             img_tk = ImageTk.PhotoImage(img)
#             pdf_canvas.delete("all")
#             pdf_canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
#             pdf_canvas.img_tk = img_tk
#             pdf_canvas.config(scrollregion=(0, 0, pix.width, pix.height))
#         def duplicate_render_thumbnails():
#             if not self.pdf_document:
#                 return
#             for widget in inner_thumbnail_frame.winfo_children():
#                 widget.destroy()
#             thumbnail_width = 150
#             thumbnail_height = 200
#             for page_number in range(len(self.pdf_document)):
#                 page = self.pdf_document.load_page(page_number)
#                 pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
#                 img = Image.open(io.BytesIO(pix.tobytes("png")))
#                 img_resized = ImageOps.fit(
#                     img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
#                 img_tk = ImageTk.PhotoImage(img_resized)
#                 frame = tk.Frame(inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
#                 frame.pack(pady=5)
#                 frame.bind("<Button-1>", lambda e, p=page_number: select_page(p))
#                 label = tk.Label(frame, image=img_tk, bg="lightgray")
#                 label.pack()
#                 label.bind("<Button-1>", lambda e, p=page_number: select_page(p))
#                 frame.img_tk = img_tk
#                 frame.tag = page_number  # Tag for highlighting
#             inner_thumbnail_frame.update_idletasks()
#             thumbnail_canvas.configure(scrollregion=thumbnail_canvas.bbox("all"))
#         def highlight_thumbnail(page_number):
#             for frame in inner_thumbnail_frame.winfo_children():
#                 if hasattr(frame, "tag") and frame.tag == page_number:
#                     frame.config(bg="orange", highlightbackground="orange")
#                 else:
#                     frame.config(bg="lightgray", highlightbackground="lightgray")
#         def select_page(page_number):
#             render_duplicate_page(page_number)
#             highlight_thumbnail(page_number)
#         def zoom_in():
#             nonlocal duplicate_zoom_factor
#             duplicate_zoom_factor += 0.2
#             render_duplicate_page(duplicate_current_page)
#         def zoom_out():
#             nonlocal duplicate_zoom_factor
#             if duplicate_zoom_factor > 0.4:
#                 duplicate_zoom_factor -= 0.2
#                 render_duplicate_page(duplicate_current_page)
#         def toggle_invert_colors():
#             nonlocal duplicate_is_inverted
#             duplicate_is_inverted = not duplicate_is_inverted
#             render_duplicate_page(duplicate_current_page)
#         def prev_page():
#             nonlocal duplicate_current_page
#             if duplicate_current_page > 0:
#                 duplicate_current_page -= 1
#                 render_duplicate_page(duplicate_current_page)
#         def next_page():
#             nonlocal duplicate_current_page
#             if duplicate_current_page < len(duplicate_pdf_document) - 1:
#                 duplicate_current_page += 1
#                 render_duplicate_page(duplicate_current_page)
#         def create_button(parent, text, command, tooltip_text):
#             button = ttk.Button(parent, text=text, style="Modern.TButton", command=command)
#             button.pack(side=tk.LEFT, padx=5)
#             button.bind("<Enter>", lambda event: self.button_tooltip(event, text, tooltip_text))
#             button.bind("<Leave>", self.hide_tooltip)
#         create_button(toolbar, "🔍 -", zoom_out, "Zoom Out")
#         create_button(toolbar, "🔍 +", zoom_in, "Zoom In")
#         create_button(toolbar, "⬅️", prev_page, "Previous Page")
#         create_button(toolbar, "➡️", next_page, "Next Page")
#         create_button(toolbar, "🌓", toggle_invert_colors, "Invert Colors")
#         duplicate_render_thumbnails()
#         render_duplicate_page(duplicate_current_page)
#         def close_duplicate_window():
#             self.duplicate_windows.remove(duplicate_window)
#             duplicate_window.destroy()
#         duplicate_window.protocol("WM_DELETE_WINDOW", close_duplicate_window)
#     def close_main_window(self):
#         """Closes the main window only if there are no duplicate windows open."""
#         if self.duplicate_windows:
#             messagebox.showwarning("Warning", "Please close all duplicate windows before exiting the main window.")
#         else:
#             self.root.destroy()
#     def zoom_in(self):
#         self.zoom_factor += 0.2
#         self.render_page(self.current_page)
#     def zoom_out(self):
#         if self.zoom_factor > 0.4:
#             self.zoom_factor -= 0.2
#             self.render_page(self.current_page)
#     def best_fit(self):
#         """Adjust the zoom level to fit the entire PDF page within the canvas."""
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         canvas_width = self.canvas.winfo_width()
#         canvas_height = self.canvas.winfo_height()       
#         page = self.pdf_document.load_page(self.current_page)
#         page_width, page_height = page.rect.width, page.rect.height      
#         width_scale = canvas_width / page_width
#         height_scale = canvas_height / page_height
#         self.zoom_factor = min(width_scale, height_scale)        
#         self.render_page(self.current_page)
#     def best_width(self):
#         if not self.pdf_document or self.current_page is None:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         canvas_width = self.canvas.winfo_width()
#         page = self.pdf_document.load_page(self.current_page)
#         page_width = page.rect.width
#         self.zoom_factor = canvas_width / page_width
#         self.render_page(self.current_page)
#     def render_page(self, page_number):
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         page = self.pdf_document.load_page(page_number)
#         matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
#         pix = page.get_pixmap(matrix=matrix)
#         img = Image.open(io.BytesIO(pix.tobytes("png")))
#         if self.is_inverted:
#             img = ImageOps.invert(img.convert("RGB"))
#         img_tk = ImageTk.PhotoImage(img)
#         self.canvas.delete("all")
#         self.canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
#         self.canvas.img_tk = img_tk
#         self.page_width, self.page_height = pix.width, pix.height
#         self.canvas.config(scrollregion=(0, 0, self.page_width, self.page_height))
#         self.redraw_sticky_notes()
#     def on_mouse_scroll(self, event):
#         self.canvas.yview_scroll(-1 * (event.delta // 120), "units")
#     def on_shift_mouse_scroll(self, event):
#         self.canvas.xview_scroll(-1 * (event.delta // 120), "units")
#     def on_thumbnail_scroll(self, event):
#         self.thumbnail_canvas.yview_scroll(-1 * (event.delta // 120), "units")
#     def prev_page(self):
#         if self.current_page > 0:
#             self.current_page -= 1
#             self.render_page(self.current_page)
#     def next_page(self):
#         if self.current_page < len(self.pdf_document) - 1:
#             self.current_page += 1
#             self.render_page(self.current_page)
#     def rotate_90clockwise(self):
#         """Rotate the current page clockwise."""
#         if not self.pdf_document:
#             return
#         page = self.pdf_document[self.current_page]
#         page.set_rotation((page.rotation + 90) % 360)  # Rotate clockwise
#         self.render_page(self.current_page)  # Re-render the page
#     def toggle_invert_colors(self):
#         """Toggle color inversion for the PDF."""
#         if not self.pdf_document:
#             return
#         self.is_inverted = not self.is_inverted
#         self.render_page(self.current_page)
#         self.redraw_sticky_notes()
# if __name__ == "__main__":
#     try:
#         handler = ProtocolHandler()
#         success, message = handler.register()
#         if success:
#             print(message)
#         else:
#             print(f"Warning: {message}")
#     except Exception as e:
#         print(f"Failed to register protocol handler: {e}")
#     root = tk.Tk()
#     app = StickyNotesPDFApp(root)
#     root.mainloop()





































































































# # pyinstaller --hidden-import=win32timezone  --add-data "src\pdfeditor.py;." --add-data "src\protocol_handler.py;." --name "PDFEditor"  --onefile --noconsole --icon=assets\pdfedi.ico src\servicefile.py