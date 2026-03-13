
import io
import tkinter as tk
import tkinter.ttk as ttk
from tkinter import filedialog, messagebox, Toplevel
import fitz
from PIL import Image, ImageTk, ImageOps
from urllib.parse import urlparse


def create_duplicate_window(self):
        """Creates a duplicate window to display a PDF independently."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF is loaded to view in secondary window.")
            return
        
        duplicate_window = Toplevel(self.root)
        duplicate_window.title("Secondary PDF Viewer")
        duplicate_window.geometry("900x650")
        self.duplicate_windows.append(duplicate_window)
        duplicate_change_history = []
        duplicate_highlights = []
        duplicate_sticky_notes = {}
        # Toolbar
        toolbar = tk.Frame(duplicate_window)
        toolbar.pack(fill=tk.X, pady=8)

        # Thumbnail Scroll Area
        thumbnail_frame = tk.Frame(duplicate_window)
        thumbnail_frame.pack(side=tk.LEFT, fill=tk.Y)
        thumbnail_canvas = tk.Canvas(thumbnail_frame, bg="lightgray", width=200)
        thumbnail_scrollbar = tk.Scrollbar(
            thumbnail_frame, orient=tk.VERTICAL, command=thumbnail_canvas.yview
        )
        thumbnail_canvas.configure(yscrollcommand=thumbnail_scrollbar.set)
        thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        inner_thumbnail_frame = tk.Frame(thumbnail_canvas, bg="lightgray")
        thumbnail_canvas.create_window((0, 0), window=inner_thumbnail_frame, anchor="nw")

        # Main Canvas for PDF Rendering
        pdf_frame = tk.Frame(duplicate_window)
        pdf_frame.pack(fill=tk.BOTH, expand=True, side=tk.RIGHT)
        pdf_canvas = tk.Canvas(pdf_frame, bg="lightgray", width=700, height=600)
        pdf_h_scrollbar = tk.Scrollbar(pdf_frame, orient=tk.HORIZONTAL, command=pdf_canvas.xview)
        pdf_v_scrollbar = tk.Scrollbar(pdf_frame, orient=tk.VERTICAL, command=pdf_canvas.yview)

        # Configure canvas scroll commands
        pdf_canvas.configure(
            xscrollcommand=pdf_h_scrollbar.set, 
            yscrollcommand=pdf_v_scrollbar.set
        )

        # Pack canvas and scrollbars ensuring proper layout
        pdf_canvas.grid(row=0, column=0, sticky="nsew")  # Canvas fills the available space
        pdf_h_scrollbar.grid(row=1, column=0, sticky="ew")  # Horizontal scrollbar below the canvas
        pdf_v_scrollbar.grid(row=0, column=1, sticky="ns")  # Vertical scrollbar to the right of the canvas

        # Configure grid weights for resizing
        pdf_frame.grid_rowconfigure(0, weight=1)
        pdf_frame.grid_columnconfigure(0, weight=1)

        # Variables for duplicate window state
        duplicate_pdf_document = self.pdf_document
        duplicate_current_page = self.current_page
        duplicate_zoom_factor = self.zoom_factor
        duplicate_is_inverted = self.is_inverted
        self.start_x, self.start_y, self.rectangle_id = None, None, None

        def render_duplicate_page(page_number):
            if not duplicate_pdf_document:
                return
            page = duplicate_pdf_document.load_page(page_number)
            matrix = fitz.Matrix(duplicate_zoom_factor, duplicate_zoom_factor)
            pix = page.get_pixmap(matrix=matrix)
            img = Image.open(io.BytesIO(pix.tobytes("png")))
            if duplicate_is_inverted:
                img = ImageOps.invert(img.convert("RGB"))
            img_tk = ImageTk.PhotoImage(img)
            pdf_canvas.delete("all")
            pdf_canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
            pdf_canvas.img_tk = img_tk
            pdf_canvas.config(scrollregion=(0, 0, pix.width, pix.height))
            # Re-apply highlights
            for hl in duplicate_highlights:
                if hl["page"] == page_number:
                    pdf_canvas.create_rectangle(
                        hl["coords"], outline="yellow", width=2, tag="highlight"
                    )
            for (page, x, y), note in duplicate_sticky_notes.items():
                if page == page_number:
                    x_position = x * duplicate_zoom_factor
                    y_position = y * duplicate_zoom_factor
                    pdf_canvas.create_text(
                        x_position, y_position, text="📌", font=("Arial", 16), fill="black", tags="sticky_note"
                    )

        def duplicate_render_thumbnails():
            if not self.pdf_document:
                return
            for widget in inner_thumbnail_frame.winfo_children():
                widget.destroy()
            thumbnail_width = 150
            thumbnail_height = 200
            for page_number in range(len(self.pdf_document)):
                page = self.pdf_document.load_page(page_number)
                pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
                img = Image.open(io.BytesIO(pix.tobytes("png")))
                img_resized = ImageOps.fit(
                    img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS
                )
                img_tk = ImageTk.PhotoImage(img_resized)
                frame = tk.Frame(inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
                frame.pack(pady=5, padx=20)
                frame.bind("<Button-1>", lambda e, p=page_number: select_page(p))
                label = tk.Label(frame, image=img_tk, bg="lightgray")
                label.pack()
                label.bind("<Button-1>", lambda e, p=page_number: select_page(p))
                frame.img_tk = img_tk
                frame.tag = page_number  # Tag for highlighting
            inner_thumbnail_frame.update_idletasks()
            thumbnail_canvas.configure(scrollregion=thumbnail_canvas.bbox("all"))

        def highlight_thumbnail(page_number):
            for frame in inner_thumbnail_frame.winfo_children():
                if hasattr(frame, "tag") and frame.tag == page_number:
                    frame.config(bg="orange", highlightbackground="orange")
                else:
                    frame.config(bg="lightgray", highlightbackground="lightgray")

        def enable_dup_sticky_note_mode():
            """Activate sticky note mode for duplicate viewer."""
            pdf_canvas.bind("<Button-1>", on_canvas_click)

        def on_canvas_click(event):
            """Add a sticky note at the clicked position on the canvas."""
            x = pdf_canvas.canvasx(event.x)
            y = pdf_canvas.canvasy(event.y)
            x_scaled = x / duplicate_zoom_factor
            y_scaled = y / duplicate_zoom_factor
            note_text = self.ask_for_note_text(x, y)
            if not note_text:
                return
            duplicate_sticky_notes[(duplicate_current_page, x_scaled, y_scaled)] = note_text
            duplicate_change_history.append(("sticky_note", duplicate_current_page, x_scaled, y_scaled, note_text))
            marker_id = pdf_canvas.create_oval(x-5, y-5, x+5, y+5, fill="blue", outline="blue", tags="sticky_note")
            pdf_canvas.tag_bind(marker_id, "<Enter>", lambda e, text=note_text: show_tooltip(e.x_root, e.y_root, text))
            pdf_canvas.tag_bind(marker_id, "<Leave>", hide_tooltip)
            render_duplicate_page(duplicate_current_page)

        def show_tooltip(event, text):
            """Display a tooltip."""
            x = event.x_root + 10
            y = event.y_root + 10
            if hasattr(self, "tooltip_window") and self.tooltip_window:
                self.tooltip_window.destroy()  # Remove any existing tooltip
            self.tooltip_window = tk.Toplevel()
            self.tooltip_window.wm_overrideredirect(True)
            self.tooltip_window.geometry(f"+{x}+{y}")
            label = tk.Label(self.tooltip_window, text=text, background="yellow", relief="solid", borderwidth=1)
            label.pack()

        def hide_tooltip():
            """Hide the tooltip."""
            if hasattr(self, 'tooltip_window') and self.tooltip_window:
                self.tooltip_window.destroy()
                self.tooltip_window = None
               
        # Page selection in duplicate window
        def select_page(page_number):
            render_duplicate_page(page_number)
            highlight_thumbnail(page_number)

        # Toolbar Buttons
        def zoom_in():
            nonlocal duplicate_zoom_factor
            duplicate_zoom_factor += 0.2
            render_duplicate_page(duplicate_current_page)

        def zoom_out():
            nonlocal duplicate_zoom_factor
            if duplicate_zoom_factor > 0.4:
                duplicate_zoom_factor -= 0.2
                render_duplicate_page(duplicate_current_page)

        def toggle_invert_colors():
            nonlocal duplicate_is_inverted
            duplicate_is_inverted = not duplicate_is_inverted
            render_duplicate_page(duplicate_current_page)

        def prev_page():
            nonlocal duplicate_current_page
            if duplicate_current_page > 0:
                duplicate_current_page -= 1
                render_duplicate_page(duplicate_current_page)

        def next_page():
            nonlocal duplicate_current_page
            if duplicate_current_page < len(duplicate_pdf_document) - 1:
                duplicate_current_page += 1
                render_duplicate_page(duplicate_current_page)

        def rotate_90clockwise():
            nonlocal duplicate_current_page
            if not self.pdf_document:
                return
            page = self.pdf_document[duplicate_current_page]
            page.set_rotation((page.rotation + 90) % 360) 
            render_duplicate_page(duplicate_current_page) 

        def rotate_180clockwise():
            """Rotate the current page clockwise."""
            if not self.pdf_document:
                return
            page = self.pdf_document[duplicate_current_page]
            page.set_rotation((page.rotation + 180) % 360)
            render_duplicate_page(duplicate_current_page)

        def rotate_270clockwise():
            """Rotate the current page clockwise."""
            if not self.pdf_document:
                return
            page = self.pdf_document[duplicate_current_page]
            page.set_rotation((page.rotation + 270) % 360)
            render_duplicate_page(duplicate_current_page)

        def best_fit():
            canvas_width = pdf_canvas.winfo_width()
            canvas_height = pdf_canvas.winfo_height()
            page = duplicate_pdf_document.load_page(duplicate_current_page)
            page_width, page_height = page.rect.width, page.rect.height
            width_scale = canvas_width / page_width
            height_scale = canvas_height / page_height
            nonlocal duplicate_zoom_factor
            duplicate_zoom_factor = min(width_scale, height_scale)
            render_duplicate_page(duplicate_current_page)

        def best_width():
            canvas_width = pdf_canvas.winfo_width()
            page = duplicate_pdf_document.load_page(duplicate_current_page)
            page_width = page.rect.width
            nonlocal duplicate_zoom_factor
            duplicate_zoom_factor = canvas_width / page_width
            render_duplicate_page(duplicate_current_page)

        def enable_dup_highlight_mode():
            """Activate highlight mode for duplicate viewer."""
            pdf_canvas.unbind("<Button-1>")
            pdf_canvas.bind("<Button-1>", start_rectangle)
            pdf_canvas.bind("<B1-Motion>", draw_rectangle)
            pdf_canvas.bind("<ButtonRelease-1>", finalize_highlight)
            self.start_x, self.start_y = None, None

        def dup_undo_change():
            """Undo the last change in the duplicate window."""
            if not duplicate_change_history:
                print("No actions to undo.")
                return
            last_action = duplicate_change_history.pop()
            action_type, page_number, *details = last_action

            if action_type == "highlight":
                rect = details[0]
                for item in pdf_canvas.find_withtag("highlight"):
                    coords = pdf_canvas.coords(item)
                    # Convert canvas coordinates to PDF coordinates for comparison
                    scaled_coords = (
                        coords[0] / duplicate_zoom_factor, coords[1] / duplicate_zoom_factor,
                        coords[2] / duplicate_zoom_factor, coords[3] / duplicate_zoom_factor
                    )
                    if scaled_coords == (rect.x0, rect.y0, rect.x1, rect.y1):
                        pdf_canvas.delete(item)
                        break
                duplicate_highlights[:] = [hl for hl in duplicate_highlights if hl["coords"] != (rect.x0, rect.y0, rect.x1, rect.y1)]

            elif action_type == "sticky_note":
                x, y = details[:2]
                duplicate_sticky_notes.pop((page_number, x, y), None)
                render_duplicate_page(page_number)

            render_duplicate_page(page_number)

        def start_rectangle(event):
            """Start a rectangle selection for highlighting."""
            self.start_x = pdf_canvas.canvasx(event.x)
            self.start_y = pdf_canvas.canvasy(event.y)
            self.rectangle_id = pdf_canvas.create_rectangle(
                self.start_x, self.start_y, self.start_x, self.start_y, outline="yellow"
            )

        def draw_rectangle(event):
            """Draw the rectangle dynamically as the mouse is dragged."""
            if self.rectangle_id:
                current_x = pdf_canvas.canvasx(event.x)
                current_y = pdf_canvas.canvasy(event.y)
                pdf_canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)

        def finalize_highlight(event):
            """Finalize the highlight and save it to the PDF."""
            if self.start_x is None or self.start_y is None:
                return  # No valid starting point

            end_x = pdf_canvas.canvasx(event.x) / duplicate_zoom_factor
            end_y = pdf_canvas.canvasy(event.y) / duplicate_zoom_factor
            start_x = self.start_x / duplicate_zoom_factor
            start_y = self.start_y / duplicate_zoom_factor

            rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
            page = duplicate_pdf_document[duplicate_current_page]
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


            try:
                # Add the highlight annotation
                annot = page.add_highlight_annot(rect)
                annot.update()  # Save the annotation to the document
                # Save the annotation for undo functionality
                duplicate_change_history.append(("highlight", duplicate_current_page, rect))
            except Exception as e:
                messagebox.showerror("Error", f"Failed to add highlight: {e}")
                return

            # Refresh the page to display the highlight
            render_duplicate_page(duplicate_current_page)

            # Reset highlight mode
            pdf_canvas.unbind("<B1-Motion>")
            pdf_canvas.unbind("<ButtonRelease-1>")        

        def create_button(parent, text, command, tooltip_text):
            button = ttk.Button(parent, text=text, style="Modern.TButton", command=command, width=6)
            button.pack(side=tk.LEFT, padx=2)
            button.bind("<Enter>", lambda event: show_tooltip(event, tooltip_text))
            button.bind("<Leave>", hide_tooltip)

        create_button(toolbar, "🔍 -", zoom_out, "Zoom Out")
        create_button(toolbar, "🔍 +", zoom_in, "Zoom In")
        create_button(toolbar, "⬅️", prev_page, "Previous Page")
        create_button(toolbar, "➡️", next_page, "Next Page")
        create_button(toolbar, "🌓", toggle_invert_colors, "Invert Colors")
        create_button(toolbar, "❖", best_fit, "Best Fit")
        create_button(toolbar, "↔", best_width, "Best Width")
        create_button(toolbar, "✒️", enable_dup_highlight_mode, "Highlight")
        create_button(toolbar, "📌", enable_dup_sticky_note_mode, "Add Sticky Note")
        create_button(toolbar, "↩️", dup_undo_change, "Undo")
        create_button(toolbar, "⮧", rotate_90clockwise, "Rotate 90° Right")
        create_button(toolbar, "⮠ ", rotate_180clockwise, "Rotate 180° Right")
        create_button(toolbar, "⮤", rotate_270clockwise, "Rotate 270° Right")       
        duplicate_render_thumbnails()
        render_duplicate_page(duplicate_current_page)
        def close_duplicate_window():
            self.duplicate_windows.remove(duplicate_window)
            duplicate_window.destroy()

        duplicate_window.protocol("WM_DELETE_WINDOW", close_duplicate_window)