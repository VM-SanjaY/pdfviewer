import os
import math
import textwrap
import io
import cv2
import fitz
from PIL import Image, ImageTk, ImageOps
import requests
from urllib.parse import urlparse
import customtkinter as ctk
from tkinter import filedialog, messagebox
class StickyNotesPDFApp:
    def __init__(self, root):
        self.root = root
        self.zoom_factor = 1.0
        self.page_rotation = 0
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.is_drawing_hollow_rect = False  # For hollow rectangle tool
        self.is_drawing_filled_rect = False
        self.is_drawing_hollow_circle = False  # Initialize the attribute
        self.is_drawing_filled_circle = False  # Initialize for filled circle too
        self.rectangle_id = None
        self.change_history = []
        self.thumbnails = []
        self.pdf_document = None
        self.current_page = None
        self.is_inverted = False
        self.is_drawing = False
        self.redactions = []
        self.redaction_mode = False
        self.sticky_notes = {}
        self.text_annotations = {}
        self.text_annotations_bg = {}
        self.last_x, self.last_y = None, None
        self.icons = {}
        self.create_widgets()
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<Motion>", self.on_mouse_hover)
        self.active_tooltip = None
        self.page_width = 0
        self.page_height = 0
        self.load_pdf(pdf_url)
    def create_widgets(self):
        toolbar = ctk.CTkFrame(self.root)
        toolbar.pack(fill=ctk.X, pady=8)
        def create_button(parent, text="", image=None, command=None, tooltip_text=""):
            button = ctk.CTkButton(
                parent,text=text,
                image=image,command=command,
                fg_color="#00498f",text_color="white",
                hover_color="#023261",font=("Arial", 12),width=45)
            button.pack(side=ctk.LEFT, padx=3, pady=2)
            button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
            button.bind("<Leave>", self.hide_tooltip)
            return button
        create_button(toolbar, text="Undo", image=self.icons['undo'], command=self.undo_change, tooltip_text="Undo last action")
        create_button(toolbar, text="Free", image=self.icons['Free'], command=self.toggle_drawing, tooltip_text="drawing")
        create_button(toolbar, image=self.icons['rotate 90'], command=self.rotate_90clockwise, tooltip_text="rotate")
        self.rotation_slider = ctk.CTkSlider(toolbar, from_=0, to=360, command=self.update_rotation)
        self.rotation_slider.pack(side=ctk.LEFT, padx=5, pady=2)
    def update_rotation(self, value):
        """Rotate the current page dynamically based on the slider value."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        rotation_angle = int(float(value))
        self.render_page(self.current_page, rotation_angle)   
    def load_pdf(self, file_path=None):
        if not file_path:
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        try:
            parsed = urlparse(file_path)
            if parsed.scheme in ('http', 'https'):
                response = requests.get(file_path)
                response.raise_for_status()  # Raise an exception for bad status codes
                pdf_data = response.content
                self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
            else:
                self.pdf_document = fitz.open(file_path)
            
            if len(self.pdf_document) == 0:
                raise ValueError("The PDF has no pages.")
            self.current_page = 0
            self.is_inverted = False
            self.text_annotations.clear()  # Clear annotations to avoid mismatches
            self.render_thumbnails()
            self.render_page(self.current_page)
            self.update_thumbnail_selection()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
            self.pdf_document = None
            self.current_page = None
    def render_page(self, page_number, rotation_angle=0):
        """Render a PDF page to the canvas with the current zoom factor and rotation."""
        if not self.pdf_document or page_number >= len(self.pdf_document):
            messagebox.showerror("Error", "No valid page to render.")
            return
        try:
            page = self.pdf_document.load_page(page_number)
            matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor) * fitz.Matrix(rotation_angle)
            pix = page.get_pixmap(matrix=matrix)
            img = Image.open(io.BytesIO(pix.tobytes("png")))
            if self.is_inverted:
                img = ImageOps.invert(img.convert("RGB"))
            img_tk = ImageTk.PhotoImage(img)
            self.canvas.delete("all")
            self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
            self.canvas.img_tk = img_tk  # Prevent garbage collection
            self.page_width, self.page_height = pix.width, pix.height
            self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
            self.redraw_sticky_notes()
            self.redraw_freehand_drawing()
            self.redraw_polygons()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to render page: {str(e)}")
    def zoom_in(self):
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.zoom_factor += 0.2
        self.render_page(self.current_page)
    def rotate_90clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 90) % 360)
        self.render_page(self.current_page)
    def toggle_sticky_note_mode(self):
        """Toggle sticky note mode"""
        if self.sticky_note_mode:
            self.sticky_note_mode = False
            self.canvas.unbind("<Button-1>")
        else:
            self.enable_sticky_note_mode()
    def enable_sticky_note_mode(self):
        """Activate sticky note mode."""
        self.sticky_note_mode = True
        self.highlight_mode = False
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

                self.canvas.create_image(
                    rotated_x, rotated_y,
                    image=self.icons['thumb_pin'],
                    anchor="center",
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
        sticky_icon = self.icons.get("thumb_pin")
        if sticky_icon:
            self.canvas.create_image(x, y, image=sticky_icon, anchor="center", tags="sticky_note")
        else:
            print("Warning: 'sticky_note' icon not found.")  # Refresh to apply the changes
    def on_mouse_hover(self, event):
        """Change cursor when hovering over a polygon or sticky note."""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        tooltip_shown = False
        for drawing in self.page_drawings.get(self.current_page, []):
            if isinstance(drawing, tuple):
                if len(drawing) == 3:  # Polygon (id, points, color)
                    _, points, _ = drawing
                    if self.is_point_inside_polygon(x, y, points):
                        self.canvas.config(cursor="hand2")
                        return
        for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
            if page_num == self.current_page:
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                if abs(x - x_position) < 20 and abs(y - y_position) < 20:  # Adjust hover sensitivity
                    if not tooltip_shown:
                        self.show_tooltip(event.x_root, event.y_root, text)  # Use root coordinates for tooltip
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
        wrapped_text = textwrap.fill(text, width=50)  # Ensuring the line ends at 50 characters
        tooltip = ctk.CTkToplevel(self.root)
        tooltip.overrideredirect(True)
        tooltip.geometry(f"+{int(x) + 10}+{int(y) + 10}")  # Ensure integer coordinates
        label = ctk.CTkLabel(
            tooltip, text=wrapped_text, bg_color="light yellow", text_color="black", padx=10, pady=5)
        label.pack()
        if getattr(self, "active_tooltip", None):
            self.active_tooltip.destroy()
        self.active_tooltip = tooltip
    def toggle_filled_polygon_mode(self):
        """Toggle filled polygon drawing mode."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return

        if self.polygon_mode == "filled":
            self.filled_polygon_button.configure(text="")
            self.polygon_mode = None
            self.start_point = None
            self.polygon_created = False  # Reset creation flag
            self.canvas.unbind("<Button-1>")
            self.embed_polygons_in_pdf()
        else:
            if self.polygon_mode == "hollow":
                self.hollow_polygon_button.configure(text="")
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
            self.hollow_polygon_button.configure(text="")
            self.polygon_mode = None
            self.start_point = None
            self.polygon_created = False  # Reset creation flag
            self.canvas.unbind("<Button-1>")
            self.embed_polygons_in_pdf()
        else:
            if self.polygon_mode == "filled":
                self.filled_polygon_button.configure(text="")
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
        for idx, drawing in enumerate(self.page_drawings[self.current_page]):
            if len(drawing) != 3:
                print(f"Skipping invalid entry at index {idx}: {drawing}")
                continue
            mode, points, polygon_id = drawing

            if self.is_point_inside_polygon(x, y, points):
                self.canvas.config(cursor="hand2")  # Change cursor when hovering over polygon
                zoom_adjusted_radius = max(10, 15 * self.zoom_factor)
                for i in range(0, len(points), 2):
                    vx, vy = points[i], points[i + 1]
                    if abs(vx - x) < zoom_adjusted_radius and abs(vy - y) < zoom_adjusted_radius:
                        self.dragging_polygon = (idx, i // 2)
                        self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
                        self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                        self.canvas.config(cursor="fleur")  # Change cursor to grabbing hand when dragging
                        return
                self.dragging_polygon = (idx, None)
                self.start_drag_x, self.start_drag_y = x, y
                self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
                self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                self.canvas.config(cursor="fleur")  # Change cursor to grabbing hand when dragging
                return
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
        for i in range(0, len(points), 2):
            points[i] += dx
            points[i + 1] += dy
        self.canvas.coords(polygon_id, points)
        self.start_drag_x, self.start_drag_y = x, y

    def on_polygon_drag_vertex(self, event):
        """Handle dragging a single vertex of the polygon smoothly."""
        if not hasattr(self, 'dragging_polygon'):
            return
        idx, vertex_idx = self.dragging_polygon
        mode, points, polygon_id = self.page_drawings[self.current_page][idx]
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        snap_threshold = 5  # Pixels
        original_x, original_y = points[vertex_idx * 2], points[vertex_idx * 2 + 1]
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

































































































































import os
import math
import textwrap
import io
import cv2
import fitz
from PIL import Image, ImageTk, ImageOps
import requests
from urllib.parse import urlparse
import customtkinter as ctk
from tkinter import filedialog, messagebox
class StickyNotesPDFApp:
    def __init__(self, root):
        self.root = root
        self.zoom_factor = 1.0
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.is_drawing_hollow_rect = False  # For hollow rectangle tool
        self.is_drawing_filled_rect = False
        self.is_drawing_hollow_circle = False  # Initialize the attribute
        self.is_drawing_filled_circle = False  # Initialize for filled circle too
        self.rectangle_id = None
        self.change_history = []
        self.thumbnails = []
        self.pdf_document = None
        self.current_page = None
        self.is_inverted = False
        self.is_drawing = False
        self.redactions = []
        self.redaction_mode = False
        self.sticky_notes = {}
        self.text_annotations = {}
        self.text_annotations_bg = {}
        self.last_x, self.last_y = None, None
        self.icons = {}
        self.create_widgets()
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<Motion>", self.on_mouse_hover)
        self.active_tooltip = None
        self.page_width = 0
        self.page_height = 0
        self.load_pdf(pdf_url)
    def create_widgets(self):
        toolbar = ctk.CTkFrame(self.root)
        toolbar.pack(fill=ctk.X, pady=8)
        def create_button(parent, text="", image=None, command=None, tooltip_text=""):
            button = ctk.CTkButton(
                parent,text=text,
                image=image,command=command,
                fg_color="#00498f",text_color="white",
                hover_color="#023261",font=("Arial", 12),width=45)
            button.pack(side=ctk.LEFT, padx=3, pady=2)
            button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
            button.bind("<Leave>", self.hide_tooltip)
            return button
        create_button(toolbar, text="Undo", image=self.icons['undo'], command=self.undo_change, tooltip_text="Undo last action")
        create_button(toolbar, text="Text", image=self.icons['text'], command=self.add_text_to_pdf, tooltip_text="Add plain text")
        create_button(toolbar, text="TextBg", image=self.icons['undo react'], command=self.add_text_with_background, tooltip_text="Add text with BG")
        create_button(toolbar, image=self.icons['rotate 90'], command=self.rotate_90clockwise, tooltip_text="rotate")
        self.rotation_slider = ctk.CTkSlider(toolbar, from_=0, to=360, command=self.update_rotation)
        self.rotation_slider.pack(side=ctk.LEFT, padx=5, pady=2)
    def update_rotation(self, value):
        """Rotate the current page dynamically based on the slider value."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        rotation_angle = int(float(value))
        self.render_page(self.current_page, rotation_angle)   
    def load_pdf(self, file_path=None):
        if not file_path:
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        try:
            parsed = urlparse(file_path)
            if parsed.scheme in ('http', 'https'):
                response = requests.get(file_path)
                response.raise_for_status()  # Raise an exception for bad status codes
                pdf_data = response.content
                self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
            else:
                self.pdf_document = fitz.open(file_path)
            
            if len(self.pdf_document) == 0:
                raise ValueError("The PDF has no pages.")
            self.current_page = 0
            self.is_inverted = False
            self.text_annotations.clear()  # Clear annotations to avoid mismatches
            self.render_thumbnails()
            self.render_page(self.current_page)
            self.update_thumbnail_selection()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
            self.pdf_document = None
            self.current_page = None
    def render_page(self, page_number, rotation_angle=0):
        """Render a PDF page to the canvas with the current zoom factor and rotation."""
        if not self.pdf_document or page_number >= len(self.pdf_document):
            messagebox.showerror("Error", "No valid page to render.")
            return
        try:
            page = self.pdf_document.load_page(page_number)
            matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor) * fitz.Matrix(rotation_angle)
            pix = page.get_pixmap(matrix=matrix)
            img = Image.open(io.BytesIO(pix.tobytes("png")))
            if self.is_inverted:
                img = ImageOps.invert(img.convert("RGB"))
            img_tk = ImageTk.PhotoImage(img)
            self.canvas.delete("all")
            self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
            self.canvas.img_tk = img_tk  # Prevent garbage collection
            self.page_width, self.page_height = pix.width, pix.height
            self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
            self.redraw_sticky_notes()
            self.redraw_freehand_drawing()
            self.redraw_polygons()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to render page: {str(e)}")
    def rotate_90clockwise(self):
        """Rotate the current page clockwise."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document[self.current_page]
        page.set_rotation((page.rotation + 90) % 360)
        self.render_page(self.current_page)
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
        text = self.ask_for_note_text(x, y)
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
        text = self.ask_for_note_text(x, y)
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



















# def finish_zoom_area(self, event):
    #     """Zoom into the selected area with precise centering and performance optimization."""
    #     if not self.zoom_rectangle:
    #         return

    #     # Get final selection coordinates in canvas space
    #     end_x = self.canvas.canvasx(event.x)
    #     end_y = self.canvas.canvasy(event.y)
    #     x1, y1 = min(self.start_x, end_x), min(self.start_y, end_y)
    #     x2, y2 = max(self.start_x, end_x), max(self.start_y, end_y)

    #     # Convert to PDF coordinates
    #     x1_pdf, y1_pdf = x1 / self.zoom_factor, y1 / self.zoom_factor
    #     x2_pdf, y2_pdf = x2 / self.zoom_factor, y2 / self.zoom_factor

    #     # Compute selection width and height
    #     selection_width = x2_pdf - x1_pdf
    #     selection_height = y2_pdf - y1_pdf
    #     canvas_width = self.canvas.winfo_width()
    #     canvas_height = self.canvas.winfo_height()

    #     # Determine new zoom factor, keeping aspect ratio intact
    #     zoom_x = canvas_width / selection_width
    #     zoom_y = canvas_height / selection_height
    #     new_zoom_factor = min(zoom_x, zoom_y)

    #     # Ensure zoom factor stays within limits
    #     max_zoom = 5.0
    #     min_zoom = 0.5
    #     self.zoom_factor = max(min(new_zoom_factor, max_zoom), min_zoom)

    #     # Compute the new center position in PDF space
    #     center_x_pdf = (x1_pdf + x2_pdf) / 2
    #     center_y_pdf = (y1_pdf + y2_pdf) / 2

    #     # Convert new center to canvas coordinates
    #     new_center_x = center_x_pdf * self.zoom_factor
    #     new_center_y = center_y_pdf * self.zoom_factor

    #     # Compute new scroll offsets relative to canvas size
    #     scroll_x = (new_center_x - canvas_width / 2) / self.page_width
    #     scroll_y = (new_center_y - canvas_height / 2) / self.page_height

    #     # Apply scrolling (ensuring it stays within bounds)
    #     self.canvas.xview_moveto(max(0, min(scroll_x, 1)))
    #     self.canvas.yview_moveto(max(0, min(scroll_y, 1)))
    #     # Re-render the page with new zoom
    #     self.render_page(self.current_page)

    #     # Remove selection rectangle
    #     self.canvas.delete(self.zoom_rectangle)
    #     self.canvas.unbind("<Button-1>")
    #     self.canvas.unbind("<B1-Motion>")
    #     self.canvas.unbind("<ButtonRelease-1>")
    #     self.is_zooming_area = False































































































































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
    def add_text_to_pdf(self):
        """Add plain text to the PDF at a clicked position."""
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
        text = self.ask_for_note_text(x, y)
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

    def on_add_text_with_bg_click(self, event):
        """Handle adding text with a background to the clicked position."""
        if not self.pdf_document or not self.add_text_bg_mode:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
            return
        text = self.ask_for_note_text(x, y)
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
                        x_scaled, y_scaled, x_scaled + max_width + 20, y_scaled + text_height + 15
                    ),
                    color=(0, 1, 1),
                    fill=(0, 1, 1),)
        page.insert_textbox(
            (x_scaled, y_scaled, x_scaled + 100, y_scaled + 30),  # Box dimensions
            wrapped_text,
            fontsize=16,
            color=(0, 0, 0),)  # Text color
        self.change_history.append(("add_text_bg", self.current_page, x_scaled, y_scaled, text))
        self.render_page(self.current_page)
        self.add_text_bg_mode = False
        self.canvas.unbind("<Button-1>")




































    def ask_for_note_textbox(self, prompt="Enter your note:"):
        dialog = ctk.CTkToplevel(self.root)
        dialog.title("Enter Note")
        dialog.geometry("400x250")
        dialog.resizable(False, False)
        label = ctk.CTkLabel(dialog, text=prompt, font=ctk.CTkFont(size=14, weight="bold"))
        label.pack(pady=(15, 10))
        text_box = ctk.CTkTextbox(dialog, wrap="word", height=100, width=360)
        text_box.pack(padx=15, pady=5, fill="x")
        text_box.focus_set()
        note_text_var = ctk.StringVar()
        def on_ok_click():
            txt = text_box.get("1.0", "end").strip()
            if txt:
                note_text_var.set(txt)
                dialog.destroy()
            else:
                messagebox.showerror("Empty Note", "You must enter some text for the note.")
        buttons_frame = ctk.CTkFrame(dialog)
        buttons_frame.pack(side="bottom", pady=15)
        ok_button = ctk.CTkButton( buttons_frame, text="Apply", command=on_ok_click, fg_color="#00498f", text_color="white")
        ok_button.pack(side="left", padx=10)
        cancel_button = ctk.CTkButton(buttons_frame, text="Cancel", command=dialog.destroy,fg_color="#6c757d", text_color="white")
        cancel_button.pack(side="left", padx=10)
        dialog.grab_set()
        dialog.wait_window()
        self.sticky_note_mode = False
        return note_text_var.get() or None
    def activate_text_mode(self):
        """Activate the text annotation mode."""
        if not self.pdf_document or self.current_page is None:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        self.current_shape = 'text'
        self.highlight_mode = False
        self.sticky_note_mode = False
        self.canvas.config(cursor="xterm")
        self.canvas.unbind("<Button-1>")
        self.canvas.bind("<Button-1>", self.add_text_annotation)
    def activate_filled_text_mode(self):
        """Activate the filled text annotation mode."""
        self.current_shape = 'filled_text'
        self.highlight_mode = False
        self.sticky_note_mode = False
        self.canvas.config(cursor="xterm")
        self.canvas.unbind("<Button-1>")
        self.canvas.bind("<Button-1>", self.add_filled_text_annotation)
    def add_text_annotation(self, event):
        """Handle adding a text annotation."""
        if not self.pdf_document:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        text = self.ask_for_note_textbox(prompt="Enter your text annotation:")
        if not text:
            return
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        self.text_annotations[(self.current_page, x_scaled, y_scaled)] = text
        self.change_history.append(("text", self.current_page, x_scaled, y_scaled, text))
        self.render_page(self.current_page)
        self.canvas.unbind("<Button-1>")
        self.canvas.config(cursor="arrow")
    def add_filled_text_annotation(self, event):
        """Handle adding a filled text annotation."""
        if not self.pdf_document:
            return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        text = self.ask_for_note_textbox(prompt="Enter your filled text annotation:")
        if not text:
            return
        x_scaled = x / self.zoom_factor
        y_scaled = y / self.zoom_factor
        self.filled_text_annotations[(self.current_page, x_scaled, y_scaled)] = {'text': text, 'filled': True}
        self.change_history.append(("filled_text", self.current_page, x_scaled, y_scaled, text))
        self.render_page(self.current_page)
        self.canvas.unbind("<Button-1>")
        self.canvas.config(cursor="arrow")
    def redraw_text_annotations(self):
        """Embed and redraw text annotations directly on the PDF canvas."""
        current_page = self.pdf_document[self.current_page]
        for (page_num, x_scaled, y_scaled), text in self.text_annotations.items():
            if page_num == self.current_page:
                wrapped_text = "\n".join(textwrap.wrap(text, width=30))
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                
                current_page.insert_text(
                            (x_position, y_position),
                            wrapped_text,
                            fontsize=16,
                            color=(0, 0, 0)
                        ) 
       
        # for filled text
        for (page_num, x_scaled, y_scaled), data in self.filled_text_annotations.items():
            if page_num == self.current_page:
                text = data.get('text', '')
                wrapped_text = "\n".join(textwrap.wrap(text, width=30))
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                fontsize = 12
                text_lines = wrapped_text.split("\n")
                max_width = max(len(line) for line in text_lines) * fontsize * 0.6
                text_height = fontsize * 1.2 * len(text_lines)
                current_page.draw_rect(
                        fitz.Rect(x_position, y_position, x_position + max_width + 20, y_position + text_height + 15),
                        color=(0, 0, 1),
                        fill=(0, 0, 1)
                    )
                current_page.insert_text(
                        (x_position + 7, y_position + 20),
                        wrapped_text,
                        fontsize=16,
                        color=(1, 1, 1)
                    )
    def redraw_text_annotations(self):
        """Embed and redraw text annotations directly on the PDF document."""
        for (page_num, x_scaled, y_scaled), text in self.text_annotations.items():
            if page_num == self.current_page:
                wrapped_text = "\n".join(textwrap.wrap(text, width=50))
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                page = self.pdf_document.load_page(page_num)
                page.insert_text((x_scaled, y_scaled), wrapped_text, fontsize=12, color=(0, 0, 0))
                self.canvas.create_text(
                    x_position, y_position,
                    text=wrapped_text, fill="black", font=("Arial", 12),
                    anchor="nw", tags="text_annotation")
        for (page_num, x_scaled, y_scaled), data in self.filled_text_annotations.items():
            if page_num == self.current_page:
                text = data.get('text', '')
                wrapped_text = "\n".join(textwrap.wrap(text, width=50))
                x_position = x_scaled * self.zoom_factor
                y_position = y_scaled * self.zoom_factor
                page = self.pdf_document.load_page(page_num)
                page.insert_text((x_scaled, y_scaled), wrapped_text, fontsize=12, color=(1, 1, 1), fill_opacity=1)
                fontsize = 12
                text_lines = wrapped_text.split("\n")
                max_width = max(len(line) for line in text_lines) * fontsize * 0.6
                text_height = fontsize * 1.2 * len(text_lines)
                self.canvas.create_rectangle(
                    x_position, y_position,
                    x_position + max_width + 10, y_position + text_height + 5,
                    fill="blue", outline="")
                self.canvas.create_text(
                    x_position + 5, y_position + 2,
                    text=wrapped_text, fill="white", font=("Arial", 12, "bold"),
                    anchor="nw", tags="text_annotation")

















































import os
import math
import io
import fitz
from PIL import Image, ImageTk, ImageOps
import requests
from urllib.parse import urlparse
import customtkinter as ctk
from tkinter import filedialog, messagebox
class StickyNotesPDFApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Atic PDF Editor Screen")
        self.zoom_factor = 1.0
        self.sticky_note_mode = False
        self.highlight_mode = False
        self.change_history = []
        self.sticky_notes = {}
        self.thumbnails = []
        self.pdf_document = None
        self.current_page = None
        self.is_inverted = False
        self.is_drawing = False 
        self.page_drawings = {}
        self.last_x, self.last_y = None, None
        self.icons = {}
        self.polygon_mode = None  
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
        self.load_pdf(pdf_url)
        self.temp_file_path = None
        self.server_url = "https://idms-backend.blockchaincloudapps.com/api/v1/uploads/file-annotations"
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
                width=45)
            button.pack(side=ctk.LEFT, padx=3, pady=2)
            button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
            button.bind("<Leave>", self.hide_tooltip)
            return button
        def load_image(relative_path, size=(25, 25)):
            base_dir = os.path.dirname(os.path.abspath(__file__))
            full_path = os.path.join(base_dir, relative_path)
            image = Image.open(full_path)
            image = image.resize(size, Image.LANCZOS)
            return ImageTk.PhotoImage(image)
        self.icons = {
            "zoom_out": load_image("assets/zoom_out.svg"),
            "zoom_in": load_image("assets/zoom_in.svg"),
            "prev_page": load_image("assets/prev_page.svg"),
            "next_page": load_image("assets/next_page.svg"),
            "sticky_note": load_image("assets/note.svg"),
            "thumb_pin": load_image("assets/thumb_pin_yellow.svg"),
            "rotate_90": load_image("assets/rotate_90.svg"),
            "filled_polygon": load_image("assets/filledpolygon.svg"),
            "hollow_polygon": load_image("assets/hollowpolygon.svg"),}
        create_button(toolbar, image=self.icons['zoom_out'], command=self.zoom_out, tooltip_text="Zoom Out")
        create_button(toolbar, image=self.icons['zoom_in'], command=self.zoom_in, tooltip_text="Zoom In")
        create_button(toolbar, image=self.icons['prev_page'], command=self.prev_page, tooltip_text="Previous Page")
        create_button(toolbar, image=self.icons['next_page'], command=self.next_page, tooltip_text="Next Page")
        create_button(toolbar, image=self.icons['rotate_90'], command=self.rotate_90clockwise, tooltip_text="Rotate 90° Right")
        self.filled_polygon_button = create_button(toolbar, image=self.icons['filled_polygon'],command=self.toggle_filled_polygon_mode,tooltip_text="Draw a filled polygon")
        self.hollow_polygon_button = create_button(toolbar, image=self.icons['hollow_polygon'],command=self.toggle_hollow_polygon_mode,tooltip_text="Draw a hollow polygon")  
        canvas_frame = ctk.CTkFrame(self.root)
        canvas_frame.pack(fill=ctk.BOTH, expand=True)
        self.canvas = ctk.CTkCanvas(canvas_frame, bg="lightgray", width=1250, height=750)
        self.h_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="horizontal", command=self.canvas.xview)
        self.v_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="vertical", command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
        self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
        self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        self.canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
        self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
        self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
    def load_pdf(self, file_path=None):
        if not file_path:
            file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        try:
            parsed = urlparse(file_path)
            if parsed.scheme in ('http', 'https'):
                response = requests.get(file_path)
                response.raise_for_status() 
                pdf_data = response.content
                self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
            else:
                self.pdf_document = fitz.open(file_path)
            self.pdf_path = file_path
            self.current_page = 0
            self.is_inverted = False
            self.render_page(self.current_page)
            save_url = self.server_url+file_path
            print(save_url)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
            return
    def zoom_in(self):
        self.zoom_factor += 0.2
        self.render_page(self.current_page)
    def zoom_out(self):
        if self.zoom_factor > 0.4:
            self.zoom_factor -= 0.2
            self.render_page(self.current_page)
    def render_page(self, page_number):
        """Render a PDF page to the canvas with the current zoom factor."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        page = self.pdf_document.load_page(page_number)
        matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
        pix = page.get_pixmap(matrix=matrix)
        img = Image.open(io.BytesIO(pix.tobytes("png")))
        if self.is_inverted:
            img = ImageOps.invert(img.convert("RGB"))
        img_tk = ImageTk.PhotoImage(img)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
        self.canvas.img_tk = img_tk 
        self.page_width, self.page_height = pix.width, pix.height
        self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
        self.redraw_polygons()
    def on_mouse_scroll(self, event):
        """Handles vertical scrolling."""
        if self.page_height > self.canvas.winfo_height():  # Scroll only if page is taller
            self.canvas.yview_scroll(-1 * (event.delta // 120), "units")
    def on_shift_mouse_scroll(self, event):
        """Handles horizontal scrolling when Shift is held."""
        if self.page_width > self.canvas.winfo_width():  # Scroll only if page is wider
            self.canvas.xview_scroll(-1 * (event.delta // 120), "units")
    def toggle_drawing(self):
        """Toggle the drawing mode on or off."""
        self.is_drawing = not getattr(self, "is_drawing", False) 
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
        line = (x1 / self.zoom_factor, y1 / self.zoom_factor, x2 / self.zoom_factor, y2 / self.zoom_factor)
        if current_page not in self.page_drawings:
            self.page_drawings[current_page] = []
        self.page_drawings[current_page].append(line)
        self.canvas.create_line(x1, y1, x2, y2, fill="black", width=2)
        self.drawing_start = (x2, y2)
    def start_drawing(self, event):
        """Initialize the start point for drawing."""
        self.drawing_start = (event.x, event.y)
    def redraw_freehand_drawing(self):
        """Redraw lines for the current page."""
        if self.current_page not in self.page_drawings:
            return
        lines = self.page_drawings[self.current_page]
        for line in lines:
            if not all(isinstance(coord, (int, float)) for coord in line):
                continue
            scaled_line = [coord * self.zoom_factor for coord in line]
            self.canvas.create_line(*scaled_line, fill="black", width=2)
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
    def toggle_filled_polygon_mode(self):
        """Toggle filled polygon drawing mode."""
        if self.polygon_mode == "filled":
            self.filled_polygon_button.configure(text="")
            self.polygon_mode = None
            self.start_point = None
            self.canvas.unbind("<Button-1>")
            self.embed_polygons_in_pdf()
        else:
            self.filled_polygon_button.configure(text="#")
            self.polygon_mode = "filled"
            self.start_point = None
            self.canvas.bind("<Button-1>", self.on_canvas_polygon_click)
    def toggle_hollow_polygon_mode(self):
        """Toggle hollow polygon drawing mode."""
        if self.polygon_mode == "hollow":
            self.hollow_polygon_button.configure(text="")
            self.polygon_mode = None
            self.start_point = None
            self.canvas.unbind("<Button-1>")
            self.embed_polygons_in_pdf()
        else:
            self.hollow_polygon_button.configure(text="#")
            self.polygon_mode = "hollow"
            self.start_point = None
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
        for idx, (mode, points, polygon_id) in enumerate(self.page_drawings[self.current_page]):
            if self.is_point_inside_polygon(x, y, points):
                for i in range(0, len(points), 2):
                    vx, vy = points[i], points[i + 1]
                    if abs(vx - x) < 10 and abs(vy - y) < 10:
                        self.dragging_polygon = (idx, i // 2)
                        self.canvas.bind("<B1-Motion>", self.on_polygon_drag_vertex)
                        self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                        return
                self.dragging_polygon = (idx, None)
                self.start_drag_x, self.start_drag_y = x, y
                self.canvas.bind("<B1-Motion>", self.on_polygon_drag_entire)
                self.canvas.bind("<ButtonRelease-1>", self.on_polygon_drag_release)
                return
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
    def embed_polygons_in_pdf(self):
        """Embed polygons directly as vector graphics in the PDF."""
        if not self.pdf_document:
            messagebox.showerror("Error", "No PDF loaded.")
            return
        try:
            page = self.pdf_document[self.current_page]
            for mode, points, _ in self.page_drawings[self.current_page]:
                path = page.new_shape()
                for i in range(0, len(points), 2):
                    p1 = (points[i], points[i + 1])
                    p2 = (points[(i + 2) % len(points)], points[(i + 3) % len(points)])
                    path.draw_line(p1, p2)
                if mode == "filled":
                    path.finish(fill=(0, 0, 1), color=None)
                elif mode == "hollow":
                    path.finish(color=(1, 0, 0), fill=None)
                path.commit()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to embed polygons: {str(e)}")
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
    def on_polygon_drag_entire(self, event):
        """Handle dragging to move the entire polygon."""
        if not hasattr(self, 'dragging_polygon'):
            return
        idx, _ = self.dragging_polygon
        mode, points, polygon_id = self.page_drawings[self.current_page][idx]
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        dx, dy = x - self.start_drag_x, y - self.start_drag_y
        for i in range(0, len(points), 2):
            points[i] += dx
            points[i + 1] += dy
        self.canvas.coords(polygon_id, points)
        self.start_drag_x, self.start_drag_y = x, y
    def on_polygon_drag_vertex(self, event):
        """Handle dragging a single vertex of the polygon."""
        if not hasattr(self, 'dragging_polygon'):
            return
        idx, vertex_idx = self.dragging_polygon
        mode, points, polygon_id = self.page_drawings[self.current_page][idx]
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
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
if __name__ == "__main__":
    root = ctk.CTk()
    app = StickyNotesPDFApp(root)
    root.mainloop()






































































































# import os
# import tempfile
# import io
# import cairosvg
# import fitz
# from PIL import Image, ImageTk, ImageOps
# import requests
# from xml.etree import ElementTree as ET
# from urllib.parse import urlparse
# from duplicate_window import DuplicateStickyNotesPDFApp
# import sys
# from protocol_handler import ProtocolHandler
# import customtkinter as ctk
# from tkinter import filedialog, messagebox

# class StickyNotesPDFApp:
#     SOCKET_PORT = 65432
#     def __init__(self, root):
#         self.root = root
#         self.root.title("Atic PDF Editor Screen")
#         self.zoom_factor = 1.0
#         self.sticky_note_mode = False
#         self.highlight_mode = False
#         self.change_history = []
#         self.sticky_notes = {}
#         self.thumbnails = []
#         self.pdf_document = None
#         self.current_page = None
#         self.is_inverted = False
#         self.icons = {}
#         self.polygon_mode = None  # 'filled' or 'hollow'
#         self.polygon_size = 50
#         self.start_point = None
#         self.polygons = []  # Store polygon details (type, points, id, options)
#         self.active_polygon = None
#         self.dragging_point_index = None
#         self.hollow_line_thickness = 2
#         self.create_widgets()
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
#         self.canvas.bind("<Motion>", self.on_mouse_hover)
#         self.active_tooltip = None
#         self.page_width = 0
#         self.page_height = 0
#         self.duplicate_windows = []
#         self.root.protocol("WM_DELETE_WINDOW", self.close_main_window)
#         pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
#         self.load(pdf_url)
#         self.temp_file_path = None
#     def create_widgets(self):
#         toolbar = ctk.CTkFrame(self.root)
#         toolbar.pack(fill=ctk.X, pady=8)
#         def create_button(parent, text="", image=None, command=None, tooltip_text=""):
#             button = ctk.CTkButton(
#                 parent,text=text,
#                 image=image,command=command,
#                 fg_color="#378cde",
#                 text_color="white",
#                 hover_color="#023261",
#                 font=("Arial", 12),
#                 width=45)
#             button.pack(side=ctk.LEFT, padx=3, pady=2)
#             button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
#             button.bind("<Leave>", self.hide_tooltip)
#             return button
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
#         def change_svg_color(file_path, new_color, output_path=None):
#             if getattr(sys, 'frozen', False):
#                 base_dir = sys._MEIPASS
#             else:
#                 base_dir = os.path.dirname(os.path.abspath(__file__))
#             full_file_path = os.path.join(base_dir, file_path)
#             if not os.path.exists(full_file_path):
#                 raise FileNotFoundError(f"File not found: {full_file_path}")
#             tree = ET.parse(full_file_path)
#             root = tree.getroot()
#             namespace = {'svg': 'http://www.w3.org/2000/svg'}
#             for elem in root.findall(".//svg:path", namespace):
#                 elem.set('fill', new_color)
#             if not output_path:
#                 temp_dir = tempfile.gettempdir()
#                 output_path = os.path.join(temp_dir, os.path.basename(file_path))
#             tree.write(output_path)
#             return output_path
#         self.icons = {
#             "load_pdf": load_image("assets/folder.svg"),
#             "new_window": load_image("assets/new_window.svg"),
#             "zoom_out": load_image("assets/zoom_out.svg"),
#             "zoom_in": load_image("assets/zoom_in.svg"),
#             "prev_page": load_image("assets/prev_page.svg"),
#             "next_page": load_image("assets/next_page.svg"),
#             "undo": load_image("assets/undo.svg"),
#             "highlight": load_image("assets/highlight.svg"),
#             "sticky_note": load_image("assets/note.svg"),
#             "thumb_pin": load_image("assets/note.svg"),
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
#             "filled_polygon": load_image("assets/filledpolygon.svg"),
#             "hollow_polygon": load_image("assets/hollowpolygon.svg"),
#         }
#         icon_files = [
#             "assets/folder.svg",
#             "assets/new_window.svg",
#             "assets/zoom_out.svg",
#             "assets/zoom_in.svg",
#             "assets/prev_page.svg",
#             "assets/next_page.svg",
#             "assets/undo.svg",
#             "assets/highlight.svg",
#             "assets/note.svg",
#             "assets/rotate_90.svg",
#             "assets/rotate_180.svg",
#             "assets/rotate_270.svg",
#             "assets/fit_to_page.svg",
#             "assets/width.svg",
#             "assets/height.svg",
#             "assets/ying_yang.svg",
#             "assets/save.svg",
#             "assets/Area.svg",
#             "assets/line.svg",
#             "assets/filledpolygon.svg",
#             "assets/hollowpolygon.svg",
#         ]
#         for icon_file in icon_files:
#             change_svg_color(icon_file, new_color="white")
#         change_svg_color("assets/note.svg", new_color="yellow", output_path="assets/thumb_pin_yellow.svg")
#         self.icons["thumb_pin"] = load_image("assets/thumb_pin_yellow.svg", size=(24, 24))
#         create_button(toolbar, image=self.icons['load_pdf'], command=self.load_pdf, tooltip_text="Load PDF")  #  text that is visible when hovered
#         create_button(toolbar, image=self.icons['new_window'], command=lambda: self.create_duplicate_window(fileurl), tooltip_text="New Window")
#         create_button(toolbar, image=self.icons['zoom_out'], command=self.zoom_out, tooltip_text="Zoom Out")
#         create_button(toolbar, image=self.icons['zoom_in'], command=self.zoom_in, tooltip_text="Zoom In")
#         create_button(toolbar, image=self.icons['zoom_area'], command=self.toggle_zoom_in_area_mode, tooltip_text="Zoom Area")
#         create_button(toolbar, image=self.icons['best_width'], command=self.best_width, tooltip_text="Best Width")
#         create_button(toolbar, image=self.icons['best_height'], command=self.best_height, tooltip_text="Best Height")
#         create_button(toolbar, image=self.icons['zoom_area'], command=self.toggle_zoom_in_area_mode, tooltip_text="Zoom Area")
#         self.draw_button = create_button(toolbar, image=self.icons['free_line'], command=self.toggle_drawing, tooltip_text="Free Hand Line")
#         self.filled_polygon_button = create_button(toolbar, image=self.icons['filled_polygon'],command=self.toggle_filled_polygon_mode,tooltip_text="Draw a filled polygon")
#         self.hollow_polygon_button = create_button(toolbar, image=self.icons['hollow_polygon'],command=self.toggle_hollow_polygon_mode,tooltip_text="Draw a hollow polygon") 
#         canvas_frame = ctk.CTkFrame(self.root)
#         canvas_frame.pack(fill=ctk.BOTH, expand=True)
#         self.thumbnail_frame = ctk.CTkFrame(canvas_frame, width=150, fg_color="lightgray")
#         self.thumbnail_frame.pack(side=ctk.LEFT, fill=ctk.Y)
#         self.thumbnail_canvas = ctk.CTkCanvas(self.thumbnail_frame, bg="lightgray", width=200)
#         self.thumbnail_scrollbar = ctk.CTkScrollbar(self.thumbnail_frame, orientation="vertical", command=self.thumbnail_canvas.yview)
#         self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
#         self.thumbnail_canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
#         self.thumbnail_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
#         self.inner_thumbnail_frame = ctk.CTkFrame(self.thumbnail_canvas, fg_color="lightgray")
#         self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
#         self.canvas = ctk.CTkCanvas(canvas_frame, bg="lightgray", width=1250, height=750)
#         self.h_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="horizontal", command=self.canvas.xview)
#         self.v_scrollbar = ctk.CTkScrollbar(canvas_frame, orientation="vertical", command=self.canvas.yview)
#         self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
#         self.h_scrollbar.pack(side=ctk.BOTTOM, fill=ctk.X)
#         self.v_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
#         self.canvas.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
#         self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
#         self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
#     def button_tooltip(self, event, button_text, tooltip_text):
#         """Display tooltip when hovering over a button."""
#         if self.active_tooltip:
#             self.active_tooltip.destroy() # to destroy automatiacally each second
#         tooltip = ctk.CTkToplevel(self.root)
#         tooltip.wm_overrideredirect(True) # it used for closing tooltip
#         tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")  # text Position near the mouse hover
#         label = ctk.CTkLabel(tooltip, text=tooltip_text, fg_color="light yellow",text_color="black", padx=5, pady=5)
#         label.pack()
#         if self.active_tooltip:
#             self.active_tooltip.destroy()
#         self.active_tooltip = tooltip
#     def handle_url(self, url):
#         """Handle a new URL (load the PDF)."""
#         try:
#             self.load_pdf(url)
#         except Exception as e:
#             print(f"Failed to load PDF: {e}")
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
#             global fileurl
#             fileurl = file_path
#             self.pdf_path = file_path
#             self.current_page = 0
#             self.is_inverted = False
#             self.render_thumbnails()
#             self.render_page(self.current_page)
#             self.update_thumbnail_selection()
#         except Exception as e:
#             ctk.CTkMessagebox.show_error("Error", f"Failed to load PDF: {str(e)}")
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
#             frame = ctk.CTkFrame(self.inner_thumbnail_frame, fg_color="lightgray", corner_radius=10)
#             frame.pack(pady=5, padx=20)
#             label = ctk.CTkLabel(frame, image=img_tk, text="")
#             label.pack()
#             frame.bind("<Button-1>", self.create_page_selection_handler(page_number))
#             label.bind("<Button-1>", self.create_page_selection_handler(page_number))
#             self.thumbnail_labels.append(frame)
#         self.update_thumbnail_selection()
#         self.inner_thumbnail_frame.update_idletasks()
#         self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
#     def create_page_selection_handler(self, page_number):
#         """Return a handler function to navigate to the selected page."""
#         def handler(event):
#             print(f"Thumbnail {page_number} clicked.")  # Debug log
#             self.select_page(page_number)
#         return handler
#     def update_thumbnail_selection(self):
#         """Update the highlight of the selected thumbnail."""
#         if not self.thumbnail_labels:
#             print("No thumbnails to update.")  # Debug log
#             return
#         if self.thumbnail_labels:
#             self.thumbnail_labels[0].configure(border_color="#FFA500", border_width=3)
#         for i, frame in enumerate(self.thumbnail_labels):
#             if i == self.current_page:
#                 frame.configure(border_color="#FFA500", border_width=3)  # Highlight
#             else:
#                 frame.configure(border_color="lightgray", border_width=1)
#         self.inner_thumbnail_frame.update_idletasks()
#     def select_page(self, page_number):
#         """Navigate to the selected page."""
#         self.current_page = page_number
#         self.render_page(page_number)
#         self.update_thumbnail_selection()
#     def create_duplicate_window(self, fileurl):
#         """Creates a duplicate window to display a PDF independently."""
#         if not fileurl:
#             ctk.CTkMessagebox.show_error("Error", "No PDF is currently loaded to duplicate.")
#             return
#         duplicate_root = ctk.CTkToplevel(self.root) 
#         duplicate_window = DuplicateStickyNotesPDFApp(duplicate_root, fileurl)
#         self.duplicate_windows.append(duplicate_root)
#         def on_close():
#             self.duplicate_windows.remove(duplicate_root)
#             duplicate_root.destroy()
#         duplicate_root.protocol("WM_DELETE_WINDOW", on_close)
#     def close_main_window(self):
#         """Closes the main window only if there are no duplicate windows open."""
#         if self.duplicate_windows:
#             ctk.CTkMessagebox.show_warning("Warning", "Please close all duplicate windows before exiting the main window.")
#         else:
#             self.root.destroy()
#     def zoom_in(self):
#         self.zoom_factor += 0.2
#         self.render_page(self.current_page)
#     def zoom_out(self):
#         if self.zoom_factor > 0.4:
#             self.zoom_factor -= 0.2
#             self.render_page(self.current_page)
#     def best_width(self):
#         """Adjust the zoom level to fit the entire PDF page to the canvas width."""
#         if not self.pdf_document or self.current_page is None:
#             ctk.CTkMessagebox.show_error("Error", "No PDF loaded.")
#             return
#         canvas_width = self.canvas.winfo_width()
#         page = self.pdf_document.load_page(self.current_page)
#         page_width = page.rect.width
#         self.zoom_factor = canvas_width / page_width
#         self.render_page(self.current_page)
#     def best_height(self):
#         """Adjust the zoom level to fit the entire PDF page to the canvas height."""
#         if not self.pdf_document or self.current_page is None:
#             ctk.CTkMessagebox.show_error("Error", "No PDF loaded.")
#             return
#         canvas_height = self.canvas.winfo_height()
#         page = self.pdf_document.load_page(self.current_page)
#         page_height = page.rect.height
#         self.zoom_factor = canvas_height / page_height
#         self.render_page(self.current_page)
#     def render_page(self, page_number):
#         """Render a PDF page to the canvas with the current zoom factor."""
#         if not self.pdf_document:
#             ctk.CTkMessagebox.show_error("Error", "No PDF loaded.")
#             return
#         page = self.pdf_document.load_page(page_number)
#         matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
#         pix = page.get_pixmap(matrix=matrix)
#         img = Image.open(io.BytesIO(pix.tobytes("png")))
#         if self.is_inverted:
#             img = ImageOps.invert(img.convert("RGB"))
#         img_tk = ImageTk.PhotoImage(img)
#         self.canvas.delete("all")
#         self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
#         self.canvas.img_tk = img_tk 
#         self.page_width, self.page_height = pix.width, pix.height
#         self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))     
#         self.redraw_sticky_notes()
#         self.redraw_freehand_drawing()
#         for mode, points, polygon_id in self.polygons:
#             if mode == "filled":
#                 self.canvas.create_polygon(points, fill="blue", outline="black")
#             elif mode == "hollow":
#                 self.canvas.create_polygon(points, fill="", outline="red")    
#     def redraw_freehand_drawing(self):
#         """Redraw all freehand lines based on stored coordinates and zoom factor."""
#         if not hasattr(self, "drawings"):
#             self.drawings = []
#         for line in self.drawings:
#             scaled_line = [coord * self.zoom_factor for coord in line]
#             self.canvas.create_line(*scaled_line, fill="black", width=2)
#     def toggle_filled_polygon_mode(self):
#         """Toggle the filled polygon drawing mode."""
#         if self.polygon_mode == "filled":
#             self.polygon_mode = None
#             self.filled_polygon_button.configure(fg_color="#00498f")
#         else:
#             self.polygon_mode = "filled"
#             self.filled_polygon_button.configure(fg_color="#FFA500")
#             self.hollow_polygon_button.configure(fg_color="#00498f")
#     def toggle_hollow_polygon_mode(self):
#         """Toggle the hollow polygon drawing mode."""
#         if self.polygon_mode == "hollow":
#             self.polygon_mode = None
#             self.hollow_polygon_button.configure(fg_color="#00498f")
#         else:
#             self.polygon_mode = "hollow"
#             self.hollow_polygon_button.configure(fg_color="#FFA500")
#             self.filled_polygon_button.configure(fg_color="#00498f")
#     def on_canvas_click(self, event):
#         """Handle canvas clicks for drawing polygons."""
#         if not self.polygon_mode:
#             return
#         self.start_point = (event.x, event.y)
#         polygon_points = self.calculate_polygon_points(event.x, event.y, self.polygon_size)
#         if self.polygon_mode == "filled":
#             polygon_id = self.canvas.create_polygon(
#                 polygon_points, fill="blue", outline="black")
#         elif self.polygon_mode == "hollow":
#             polygon_id = self.canvas.create_polygon(
#                 polygon_points, fill="", outline="red")
#         self.polygons.append((self.polygon_mode, polygon_points, polygon_id))
#     def calculate_polygon_points(self, x, y, size):
#         """Calculate the vertices of a polygon centered at (x, y)."""
#         import math
#         num_sides = 6  # Example: Hexagon
#         angle = 2 * math.pi / num_sides
#         points = [
#             (x + size * math.cos(i * angle),
#             y + size * math.sin(i * angle))
#             for i in range(num_sides)
#         ]
#         return points
#     def increase_polygon_size(self):
#         """Increase the size of the polygon."""
#         self.polygon_size += 10
#     def decrease_polygon_size(self):
#         """Decrease the size of the polygon."""
#         if self.polygon_size > 10:
#             self.polygon_size -= 10    
#     def toggle_drawing(self):
#         """Toggle the drawing mode on or off."""
#         self.is_drawing = not getattr(self, "is_drawing", False)  # Ensure is_drawing defaults to False
#         if self.is_drawing:
#             self.draw_button.config(text="Stop Drawing")
#             self.canvas.bind("<Button-1>", self.start_drawing)
#             self.canvas.bind("<B1-Motion>", self.draw_line)
#         else:
#             self.draw_button.config(text="Draw Freehand Line")
#             self.canvas.unbind("<Button-1>")
#             self.canvas.unbind("<B1-Motion>")
#     def start_drawing(self, event):
#         """Start the drawing process."""
#         if not self.is_drawing:
#             return
#         self.last_x, self.last_y = event.x, event.y
#     def draw_line(self, event):
#         """Draw a line on the canvas and store its coordinates."""
#         if not self.is_drawing:
#             return
#         x, y = event.x, event.y
#         self.canvas.create_line(self.last_x, self.last_y, x, y, fill="black", width=2)
#         if not hasattr(self, "drawings"):
#             self.drawings = []
#         self.drawings.append(
#             [self.last_x / self.zoom_factor, self.last_y / self.zoom_factor, x / self.zoom_factor, y / self.zoom_factor])
#         self.last_x, self.last_y = x, y

#     def zoom_in_area(self, event):
#         """Zoom into a specific area of the canvas based on mouse click."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         canvas_x, canvas_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
#         zoom_area_size = 150
#         left = max(0, canvas_x - zoom_area_size // 2)
#         top = max(0, canvas_y - zoom_area_size // 2)
#         right = min(self.page_width, canvas_x + zoom_area_size // 0.9)
#         bottom = min(self.page_height, canvas_y + zoom_area_size // 2)
#         canvas_width = self.canvas.winfo_width()
#         canvas_height = self.canvas.winfo_height()
#         zoom_width_factor = canvas_width / (right - left)
#         zoom_height_factor = canvas_height / (bottom - top)
#         self.zoom_factor = min(zoom_width_factor, zoom_height_factor)
#         page = self.pdf_document.load_page(self.current_page)
#         matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
#         translation_matrix = fitz.Matrix(1, 0, 0, 1, -left, -top)  # Translation matrix
#         matrix = matrix * translation_matrix  # Combine scaling and translation
#         pix = page.get_pixmap(matrix=matrix, clip=(left, top, right, bottom))
#         img = Image.open(io.BytesIO(pix.tobytes("png")))
#         if self.is_inverted:
#             img = ImageOps.invert(img.convert("RGB"))
#         img_tk = ImageTk.PhotoImage(img)
#         self.canvas.delete("all")
#         self.canvas.create_image(0, 0, anchor="nw", image=img_tk)
#         self.canvas.img_tk = img_tk  # Keep a reference to prevent garbage collection
#         self.page_width, self.page_height = pix.width, pix.height
#         self.canvas.configure(scrollregion=(0, 0, self.page_width, self.page_height))
#         self.toggle_zoom_in_area_mode()
#     def toggle_zoom_in_area_mode(self):
#         """Toggle the mode to allow zooming into a specific area."""
#         if hasattr(self, "zoom_in_area_enabled") and self.zoom_in_area_enabled:
#             self.canvas.unbind("<Button-1>")
#             self.zoom_in_area_enabled = False
#         else:
#             self.canvas.bind("<Button-1>", self.zoom_in_area)
#             self.zoom_in_area_enabled = True


#     def on_mouse_scroll(self, event):
#         """Handle vertical scrolling with the mouse wheel."""
#         self.canvas.yview_scroll(-1 * (event.delta // 120), "units")
#     def on_shift_mouse_scroll(self, event):
#         """Handle horizontal scrolling with Shift + mouse wheel."""
#         self.canvas.xview_scroll(-1 * (event.delta // 120), "units")
#     def on_thumbnail_scroll(self, event):
#         """Handle vertical scrolling in the thumbnail panel using the mouse wheel."""
#         self.thumbnail_canvas.yview_scroll(-1 * (event.delta // 120), "units")
#     def enable_sticky_note_mode(self):
#         """Activate sticky note mode."""
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
#                 self.canvas.create_image(
#                     x_position, y_position,
#                     image=self.icons['thumb_pin'],  # Use the sticky note icon
#                     anchor="center",  # Center the image
#                     tags="sticky_note"
#                 )
#     def on_canvas_click(self, event):
#         """Add a sticky note at the clicked position on the canvas."""
#         if not self.pdf_document or not self.sticky_note_mode:
#             return
#         x = self.canvas.canvasx(event.x)
#         y = self.canvas.canvasy(event.y)
#         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
#             return
#         note_text = self.ask_for_note_text(x, y)
#         if not note_text:
#             return
#         x_scaled = x / self.zoom_factor
#         y_scaled = y / self.zoom_factor
#         self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
#         self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
#         self.canvas.create_image(
#             x, y, image=self.icons['sticky_note'], anchor="center", tags="sticky_note")
#         self.sticky_note_mode = False
#     def ask_for_note_text(self, x, y):
#         """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
#         dialog = ctk.CTkToplevel(self.root)
#         dialog.title("Enter Sticky Note")
#         dialog.geometry("400x250")
#         dialog.resizable(False, False)
#         label = ctk.CTkLabel(
#             dialog, text="Enter your note:", font=ctk.CTkFont(size=14, weight="bold"))
#         label.pack(pady=(15, 10))
#         text_box = ctk.CTkTextbox(dialog, wrap="word", height=100, width=360)
#         text_box.pack(padx=15, pady=5, fill="x")
#         text_box.focus_set()
#         note_text_var = ctk.StringVar()
#         def on_ok_click():
#             note_text = text_box.get("1.0", "end").strip()
#             if note_text:
#                 note_text_var.set(note_text)
#                 dialog.destroy()
#             else:
#                 ctk.CTkMessagebox.show_warning("Empty Note", "You must enter some text to save the sticky note.")
#         buttons_frame = ctk.CTkFrame(dialog)
#         buttons_frame.pack(side="bottom", pady=15)
#         ok_button = ctk.CTkButton(
#             buttons_frame, text="OK", command=on_ok_click, fg_color="#4CAF50", text_color="white")
#         ok_button.pack(side="left", padx=10)
#         cancel_button = ctk.CTkButton(
#             buttons_frame, text="Cancel", command=dialog.destroy, fg_color="#F44336", text_color="white")
#         cancel_button.pack(side="left", padx=10)
#         dialog.grab_set()
#         dialog.wait_window()
#         self.sticky_note_mode = False
#         return note_text_var.get() or None
    

















# # import os
# # import tempfile
# # import base64
# # import io
# # import tkinter as tk
# # import tkinter.ttk as ttk
# # from tkinter import filedialog, messagebox, Toplevel
# # import fitz
# # import textwrap
# # from PIL import Image, ImageTk, ImageOps
# # import requests
# # from urllib.parse import urlparse
# # from duplicate_window import DuplicateStickyNotesPDFApp
# # import socket
# # import threading
# # import sys
# # from protocol_handler import ProtocolHandler

# # class StickyNotesPDFApp:
# #     SOCKET_PORT = 65432
# #     def __init__(self, root):
# #         self.root = root
# #         self.root.title("Atic PDF Editor Screen")
# #         self.zoom_factor = 1.0
# #         self.sticky_note_mode = False 
# #         self.highlight_mode = False 
# #         self.change_history = [] 
# #         self.sticky_notes = {} 
# #         self.thumbnails = [] 
# #         self.pdf_document = None
# #         self.current_page = None
# #         self.is_inverted = False
# #         self.create_widgets()
# #         self.canvas.bind("<Button-1>", self.on_canvas_click)
# #         self.canvas.bind("<Motion>", self.on_mouse_hover) 
# #         self.active_tooltip = None 
# #         self.page_width = 0
# #         self.page_height = 0
# #         self.duplicate_windows = []
# #         self.root.protocol("WM_DELETE_WINDOW", self.close_main_window)
# #         self.setup_ipc_server()      
# #         if len(sys.argv) > 1:
# #             pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
# #             self.handle_url(pdf_url)
# #         self.temp_file_path = None 
# #         self.server_url = "https://idms-api.blockchaincloudapps.com/upload/file" 
# #     def create_widgets(self):
# #         style = ttk.Style()
# #         style.configure(
# #             "Modern.TButton",
# #             font=("Arial", 12),padding=(2, 2),
# #             relief="flat",background="#00498f",
# #             foreground="white",borderwidth=1,
# #             highlightthickness=0, )
# #         style.map(
# #             "Modern.TButton",
# #             background=[("active", "#00498f"), ("!disabled", "#00498f")],
# #             foreground=[("active", "white")],)
# #         toolbar = tk.Frame(self.root)
# #         toolbar.pack(fill=tk.X, pady=8)
# #         def create_button(parent, text, command, tooltip_text=""):
# #             button_frame = tk.Frame(parent, width=50, height=30)
# #             button_frame.pack_propagate(False)
# #             button_frame.pack(side=tk.LEFT, padx=3)
# #             button = ttk.Button(
# #                 button_frame,text=text,
# #                 style="Modern.TButton",command=command)
# #             button.pack(fill=tk.BOTH, expand=True)
# #             button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
# #             button.bind("<Leave>", self.hide_tooltip)
# #             return button
# #         create_button(toolbar, "📂", self.load_pdf, "Load PDF")  #  text that is visible when hovered
# #         create_button(toolbar, "📄+", lambda: self.create_duplicate_window(fileurl), "New Window")
# #         create_button(toolbar, "🔍-", self.zoom_out, "Zoom Out")
# #         create_button(toolbar, "🔍+", self.zoom_in, "Zoom In")
# #         create_button(toolbar, "⬅️", self.prev_page, "Previous Page")
# #         create_button(toolbar, "➡️", self.next_page, "Next Page")
# #         create_button(toolbar, "↩️", self.undo_change, "Undo")
# #         create_button(toolbar, "✒️", self.enable_highlight_mode, "Highlight")
# #         create_button(toolbar, "📌", self.toggle_sticky_note_mode, "Sticky Note")
# #         create_button(toolbar, "⮧", self.rotate_90clockwise, "Rotate 90° Right")
# #         create_button(toolbar, "⮠ ", self.rotate_180clockwise, "Rotate 180° Right")
# #         create_button(toolbar, "⮤", self.rotate_270clockwise, "Rotate 270° Right")
# #         create_button(toolbar, "❖", self.best_fit, "Best Fit")
# #         create_button(toolbar, "↔", self.best_width, "Best Width")
# #         create_button(toolbar, "↕", self.best_height, "Best Height")
# #         create_button(toolbar, "🌓", self.toggle_invert_colors, "Invert Colors")
# #         create_button(toolbar, "💾", self.save_pdf, "Save PDF")
# #         canvas_frame = tk.Frame(self.root)
# #         canvas_frame.pack(fill=tk.BOTH, expand=True)
# #         self.thumbnail_frame = tk.Frame(canvas_frame, width=150, bg="lightgray")
# #         self.thumbnail_frame.pack(side=tk.LEFT, fill=tk.Y)
# #         self.thumbnail_canvas = tk.Canvas(self.thumbnail_frame, bg="lightgray", width=200)
# #         self.thumbnail_scrollbar = tk.Scrollbar(self.thumbnail_frame, orient=tk.VERTICAL, command=self.thumbnail_canvas.yview)
# #         self.thumbnail_canvas.configure(yscrollcommand=self.thumbnail_scrollbar.set)
# #         self.thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
# #         self.thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
# #         self.inner_thumbnail_frame = tk.Frame(self.thumbnail_canvas, bg="lightgray")
# #         self.thumbnail_canvas.create_window((0, 0), window=self.inner_thumbnail_frame, anchor="nw")
# #         self.canvas = tk.Canvas(canvas_frame, bg="lightgray", width=900, height=650)
# #         self.h_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
# #         self.v_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
# #         self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
# #         self.h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
# #         self.v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
# #         self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
# #         self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
# #         self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
# #     def button_tooltip(self, event, button_text, tooltip_text):
# #         """Display tooltip when hovering over a button."""
# #         if self.active_tooltip:
# #             self.active_tooltip.destroy()
# #         tooltip = tk.Toplevel(self.root)
# #         tooltip.wm_overrideredirect(True)
# #         tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")
# #         label = tk.Label(tooltip, text=tooltip_text, background="light yellow", relief="solid", padx=5, pady=5)
# #         label.pack()
# #         self.active_tooltip = tooltip
# #     def hide_tooltip(self, event):
# #         """Hide tooltip when the mouse leaves the button."""
# #         if self.active_tooltip: 
# #             self.active_tooltip.destroy()
# #             self.active_tooltip = None
# #     def setup_ipc_server(self):
# #         """Set up a socket server for inter-process communication."""
# #         self.ipc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
# #         try:
# #             self.ipc_socket.bind(("localhost", self.SOCKET_PORT))
# #             self.ipc_socket.listen(1)
# #             threading.Thread(target=self.ipc_listener, daemon=True).start()
# #         except socket.error:
# #             if len(sys.argv) > 1:
# #                 pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
# #                 self.send_to_running_instance(pdf_url)
# #             sys.exit()
# #     def ipc_listener(self):
# #         """Listen for incoming URLs and handle them."""
# #         while True:
# #             conn, _ = self.ipc_socket.accept()
# #             with conn:
# #                 data = conn.recv(1024).decode("utf-8")
# #                 if data:
# #                     self.root.after(0, self.handle_url, data)
# #     def send_to_running_instance(self, url):
# #         """Send the URL to the running instance."""
# #         try:
# #             with socket.create_connection(("localhost", self.SOCKET_PORT)) as client_socket:
# #                 client_socket.sendall(url.encode("utf-8"))
# #         except socket.error:
# #             print("Failed to send URL to running instance.")
# #     def handle_url(self, url):
# #         """Handle a new URL (load the PDF)."""
# #         try:
# #             self.load_pdf(url)
# #         except Exception as e:
# #             print(f"Failed to load PDF: {e}")
# #     def load_pdf(self, file_path=None):
# #         if not file_path:
# #             file_path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
# #         try:
# #             parsed = urlparse(file_path)
# #             if parsed.scheme in ('http', 'https'):
# #                 response = requests.get(file_path)
# #                 response.raise_for_status()
# #                 pdf_data = response.content       
# #                 self.pdf_document = fitz.open(stream=pdf_data, filetype="pdf")
# #             else:
# #                 self.pdf_document = fitz.open(file_path)
# #             global fileurl
# #             fileurl = file_path
# #             self.pdf_path = file_path  
# #             self.current_page = 0
# #             self.is_inverted = False
# #             self.render_thumbnails()
# #             self.render_page(self.current_page)
# #             self.update_thumbnail_selection()
# #             print("PDF loaded successfully.",fileurl)
# #         except Exception as e:
# #             messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
# #             return
# #         global filename
# #         global edit_file_name
# #         try:
# #             filename = file_path.split('/')[-1]
# #             edit_file_name = filename+"_edited"
# #         except:
# #             filename = file_path.split('\\')[-1]
# #             edit_file_name = filename+"_edited"
# #     def render_thumbnails(self):
# #         """Render the thumbnails of all PDF pages with fixed dimensions."""
# #         if not self.pdf_document:
# #             return
# #         for widget in self.inner_thumbnail_frame.winfo_children():
# #             widget.destroy()
# #         self.thumbnails = [] 
# #         self.thumbnail_labels = []
# #         thumbnail_width = 150 
# #         thumbnail_height = 200
# #         for page_number in range(len(self.pdf_document)):
# #             page = self.pdf_document.load_page(page_number)
# #             pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
# #             img = Image.open(io.BytesIO(pix.tobytes("png")))
# #             img_resized = ImageOps.fit(img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS)
# #             img_tk = ImageTk.PhotoImage(img_resized)
# #             self.thumbnails.append(img_tk)
# #             frame = tk.Frame(self.inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
# #             frame.pack(pady=5, padx=20)
# #             frame.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
# #             label = tk.Label(frame, image=img_tk, bg="lightgray")
# #             label.pack()
# #             label.bind("<Button-1>", lambda e, p=page_number: self.select_page(p))
# #             self.thumbnail_labels.append(frame)
# #         self.update_thumbnail_selection()
# #         self.inner_thumbnail_frame.update_idletasks()
# #         self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all"))
# #     def update_thumbnail_selection(self):
# #         """Update the highlight of the selected thumbnail."""
# #         for i, frame in enumerate(self.thumbnail_labels):
# #             if i == self.current_page:
# #                 frame.config(highlightbackground="orange", highlightcolor="orange")
# #             else:
# #                 frame.config(highlightbackground="lightgray", highlightcolor="lightgray")
# #     def select_page(self, page_number):
# #         """Navigate to the selected page."""
# #         self.current_page = page_number
# #         self.render_page(page_number)
# #         self.update_thumbnail_selection()
# #     def create_duplicate_window(self, fileurl):
# #         """Creates a duplicate window to display a PDF independently."""
# #         if not fileurl:
# #             messagebox.showerror("Error", "No PDF is currently loaded to duplicate.")
# #             return
# #         duplicate_root = Toplevel(self.root)  
# #         duplicate_window = DuplicateStickyNotesPDFApp(duplicate_root, fileurl)
# #         self.duplicate_windows.append(duplicate_root)
# #         def on_close():
# #             self.duplicate_windows.remove(duplicate_root)
# #             duplicate_root.destroy()
# #         duplicate_root.protocol("WM_DELETE_WINDOW", on_close)
# #     def close_main_window(self):
# #         """Closes the main window only if there are no duplicate windows open."""
# #         if self.duplicate_windows:
# #             messagebox.showwarning("Warning", "Please close all duplicate windows before exiting the main window.")
# #         else:
# #             self.root.destroy()
# #     def zoom_in(self):
# #         self.zoom_factor += 0.2
# #         self.render_page(self.current_page)
# #     def zoom_out(self):
# #         if self.zoom_factor > 0.4:
# #             self.zoom_factor -= 0.2
# #             self.render_page(self.current_page)
# #     def best_fit(self):
# #         """Adjust the zoom level to fit the entire PDF page within the canvas."""
# #         if not self.pdf_document or self.current_page is None:
# #             messagebox.showerror("Error", "No PDF loaded.")
# #             return
# #         canvas_width = self.canvas.winfo_width()
# #         canvas_height = self.canvas.winfo_height()       
# #         page = self.pdf_document.load_page(self.current_page)
# #         page_width, page_height = page.rect.width, page.rect.height      
# #         width_scale = canvas_width / page_width
# #         height_scale = canvas_height / page_height
# #         self.zoom_factor = min(width_scale, height_scale)        
# #         self.render_page(self.current_page)
# #     def best_width(self):
# #         """Adjust the zoom level to fit the entire PDF page to the canvas width."""
# #         if not self.pdf_document or self.current_page is None:
# #             messagebox.showerror("Error", "No PDF loaded.")
# #             return
# #         canvas_width = self.canvas.winfo_width()
# #         page = self.pdf_document.load_page(self.current_page)
# #         page_width = page.rect.width
# #         self.zoom_factor = canvas_width / page_width
# #         self.render_page(self.current_page)
# #     def best_height(self):
# #         """Adjust the zoom level to fit the entire PDF page to the canvas height."""
# #         if not self.pdf_document or self.current_page is None:
# #             messagebox.showerror("Error", "No PDF loaded.")
# #             return
# #         canvas_height = self.canvas.winfo_height()
# #         page = self.pdf_document.load_page(self.current_page)
# #         page_height = page.rect.height
# #         self.zoom_factor = canvas_height / page_height
# #         self.render_page(self.current_page)
# #     def render_page(self, page_number):
# #         """Render a PDF page to the canvas with the current zoom factor."""
# #         if not self.pdf_document:
# #             messagebox.showerror("Error", "No PDF loaded.")
# #             return
# #         page = self.pdf_document.load_page(page_number)
# #         matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
# #         pix = page.get_pixmap(matrix=matrix)
# #         img = Image.open(io.BytesIO(pix.tobytes("png")))
# #         if self.is_inverted:
# #             img = ImageOps.invert(img.convert("RGB"))
# #         img_tk = ImageTk.PhotoImage(img)
# #         self.canvas.delete("all")
# #         self.canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
# #         self.canvas.img_tk = img_tk 
# #         self.page_width, self.page_height = pix.width, pix.height
# #         self.canvas.config(scrollregion=(0, 0, self.page_width, self.page_height))
# #         self.redraw_sticky_notes()
# #     def on_mouse_scroll(self, event):
# #         """Handle vertical scrolling with the mouse wheel."""
# #         self.canvas.yview_scroll(-1 * (event.delta // 120), "units")
# #     def on_shift_mouse_scroll(self, event):
# #         """Handle horizontal scrolling with Shift + mouse wheel."""
# #         self.canvas.xview_scroll(-1 * (event.delta // 120), "units")
# #     def on_thumbnail_scroll(self, event):
# #         """Handle vertical scrolling in the thumbnail panel using the mouse wheel."""
# #         self.thumbnail_canvas.yview_scroll(-1 * (event.delta // 120), "units")
# #     def enable_sticky_note_mode(self):
# #         """ Activate sticky note mode """
# #         self.sticky_note_mode = True 
# #         self.highlight_mode = False 
# #         self.canvas.unbind("<B1-Motion>")
# #         self.canvas.unbind("<ButtonRelease-1>")
# #         self.canvas.bind("<Button-1>", self.on_canvas_click)
# #     def redraw_sticky_notes(self):
# #         """Redraw sticky notes after rendering the page."""
# #         self.canvas.delete("sticky_note")
# #         emoji_fill = "white" if self.is_inverted else "black"
# #         for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
# #             if page_num == self.current_page:
# #                 x_position = x_scaled * self.zoom_factor
# #                 y_position = y_scaled * self.zoom_factor
# #                 self.canvas.create_text(
# #                     x_position + 1, y_position + 1, text="📌", font=("Arial", 16),
# #                     fill="white", tags="sticky_note_shadow")
# #                 self.canvas.create_text(
# #                     x_position, y_position, text="📌", font=("Arial", 16),
# #                     fill=emoji_fill, tags="sticky_note")
# #     def on_canvas_click(self, event):
# #         """Add a sticky note at the clicked position on the canvas."""
# #         if not self.pdf_document or not self.sticky_note_mode:
# #             return
# #         x = self.canvas.canvasx(event.x)
# #         y = self.canvas.canvasy(event.y)
# #         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
# #             return
# #         note_text = self.ask_for_note_text(x, y)
# #         if not note_text:
# #             return
# #         x_scaled = x / self.zoom_factor
# #         y_scaled = y / self.zoom_factor
# #         self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
# #         self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
# #         self.canvas.create_text(x, y, text="📌", font=("Arial", 16))
# #         self.sticky_note_mode = False
# #     def ask_for_note_text(self, x, y):
# #         """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
# #         dialog = tk.Toplevel(self.root)
# #         dialog.title("Enter Sticky Note")
# #         dialog.geometry("400x250")
# #         dialog.configure(bg="#f9f9f9")
# #         dialog.resizable(False, False)
# #         label = tk.Label(
# #             dialog, text="Enter your note:", font=("Arial", 14, "bold"), bg="#f9f9f9"
# #         )
# #         label.pack(pady=(15, 10))
# #         text_box = tk.Text(dialog, wrap=tk.WORD, height=6, width=40, font=("Arial", 12), relief="solid")
# #         text_box.pack(padx=15, pady=5, fill=tk.X)
# #         text_box.focus_set()
# #         note_text_var = tk.StringVar()
# #         # button functionality
# #         def on_ok_click():
# #             note_text = text_box.get("1.0", tk.END).strip()
# #             if note_text:
# #                 note_text_var.set(note_text)
# #                 dialog.destroy()
# #             else:
# #                 messagebox.showwarning("Empty Note", "You must enter some text to save the sticky note.")
# #         def create_rounded_button(parent, text, bg_color, fg_color, command):
# #             canvas = tk.Canvas(parent, width=120, height=40, bg="#f9f9f9", highlightthickness=0)
# #             canvas.pack(side=tk.LEFT, padx=10)
# #             canvas.create_oval(10, 10, 40, 40, fill=bg_color, outline=bg_color)
# #             canvas.create_oval(80, 10, 110, 40, fill=bg_color, outline=bg_color)
# #             canvas.create_rectangle(25, 10, 95, 40, fill=bg_color, outline=bg_color)
# #             button_text = canvas.create_text(60, 25, text=text, fill=fg_color, font=("Arial", 12, "bold"))
# #             def on_click(event):
# #                 command()
# #             canvas.tag_bind(button_text, "<Button-1>", on_click)
# #             canvas.tag_bind("all", "<Enter>", lambda e: canvas.configure(cursor="hand2"))
# #             canvas.tag_bind("all", "<Button-1>", on_click)
# #             return canvas
# #         buttons_frame = tk.Frame(dialog, bg="#f9f9f9")
# #         buttons_frame.pack(side=tk.BOTTOM, pady=15)
# #         create_rounded_button(buttons_frame, "OK", bg_color="#4CAF50", fg_color="white", command=on_ok_click)
# #         create_rounded_button(buttons_frame, "Cancel", bg_color="#F44336", fg_color="white", command=dialog.destroy)
# #         dialog.grab_set()
# #         dialog.wait_window()
# #         self.sticky_note_mode = False
# #         return note_text_var.get() or None
# #     def undo_change(self):
# #         if not self.change_history:
# #             return
# #         last_action = self.change_history.pop()
# #         action_type = last_action[0]
# #         if action_type == "sticky_note":
# #             _, page, x_scaled, y_scaled, _ = last_action
# #             if (page, x_scaled, y_scaled) in self.sticky_notes:
# #                 del self.sticky_notes[(page, x_scaled, y_scaled)]
# #                 self.render_page(self.current_page)
# #         elif action_type == "highlight":
# #             _, page, annot_id = last_action
# #             page_obj = self.pdf_document[page]
# #             annot = page_obj.first_annot
# #             while annot:
# #                 if annot.info.get('id') == annot_id:
# #                     page_obj.delete_annot(annot)
# #                     self.render_page(self.current_page)
# #                     print(f"Highlight with ID {annot_id} removed.")
# #                     break
# #                 annot = annot.next
# #             else:
# #                 print(f"No annotation found with ID {annot_id}. Undo failed.")
# #         else:
# #             print(f"Unknown action type: {action_type}")
# #     def enable_highlight_mode(self):
# #         """ Activate highlight mode """
# #         self.highlight_mode = True
# #         self.sticky_note_mode = False
# #         self.canvas.unbind("<Button-1>")
# #         self.canvas.bind("<Button-1>", self.start_rectangle)
# #         self.canvas.bind("<B1-Motion>", self.draw_rectangle)
# #         self.canvas.bind("<ButtonRelease-1>", self.finalize_highlight)
# #         self.start_x, self.start_y = None, None
# #     def start_rectangle(self, event):
# #         """Start a rectangle selection for highlighting"""
# #         self.start_x = self.canvas.canvasx(event.x)
# #         self.start_y = self.canvas.canvasy(event.y)
# #         self.rectangle_id = self.canvas.create_rectangle(
# #             self.start_x, self.start_y, self.start_x, self.start_y, outline="yellow")
# #     def draw_rectangle(self, event):
# #         """Draw the rectangle dynamically as the mouse is dragged"""
# #         current_x = self.canvas.canvasx(event.x)
# #         current_y = self.canvas.canvasy(event.y)
# #         self.canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)
# #     def finalize_highlight(self, event):
# #         """Finalize the highlight and save it to the PDF."""
# #         if self.start_x is None or self.start_y is None:
# #             return 
# #         end_x = self.canvas.canvasx(event.x) / self.zoom_factor
# #         end_y = self.canvas.canvasy(event.y) / self.zoom_factor
# #         start_x = self.start_x / self.zoom_factor
# #         start_y = self.start_y / self.zoom_factor
# #         rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
# #         page = self.pdf_document[self.current_page]
# #         rotation = page.rotation
# #         page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor
# #         if rotation == 90:
# #             rect = fitz.Rect(
# #                 rect.y0,
# #                 page_width - rect.x1,
# #                 rect.y1,
# #                 page_width - rect.x0)
# #         elif rotation == 180:
# #             rect = fitz.Rect(
# #                 page_width - rect.x1,
# #                 page_height - rect.y1,
# #                 page_width - rect.x0,
# #                 page_height - rect.y0)
# #         elif rotation == 270:
# #             rect = fitz.Rect(
# #                 page_height - rect.y1,
# #                 rect.x0,
# #                 page_height - rect.y0,
# #                 rect.x1)
# #         try:
# #             highlight = page.add_highlight_annot(rect)
# #             highlight.update()
# #             highlight.set_border(width=0, dashes=(0, 0))
# #             annot_id = highlight.info.get('id')
# #             if annot_id:
# #                 self.change_history.append(("highlight", self.current_page, annot_id))
# #         except Exception as e:
# #             messagebox.showerror("Error", f"Failed to add highlight: {e}")
# #             return
# #         self.render_page(self.current_page)
# #         self.canvas.unbind("<B1-Motion>")
# #         self.canvas.unbind("<ButtonRelease-1>")
# #     def on_mouse_hover(self, event):
# #         """Show sticky note text when hovering over emoji."""
# #         if not self.pdf_document:
# #             return
# #         x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)  # Adjust for scrolling
# #         tooltip_shown = False
# #         for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
# #             if page_num == self.current_page:
# #                 x_position = x_scaled * self.zoom_factor
# #                 y_position = y_scaled * self.zoom_factor
# #                 if abs(x - x_position) < 20 and abs(y - y_position) < 20:  # Adjust hover sensitivity
# #                     if not tooltip_shown:
# #                         self.show_tooltip(event.x_root, event.y_root, text)  # Use root coordinates for tooltip
# #                         tooltip_shown = True
# #                     break
# #         if not tooltip_shown and getattr(self, "active_tooltip", None):
# #             self.active_tooltip.destroy()
# #             self.active_tooltip = None
# #     def show_tooltip(self, x, y, text):
# #         """ Display the sticky note text as a tooltip """
# #         if getattr(self, "active_tooltip", None):
# #             self.active_tooltip.destroy()
# #         wrapped_text = textwrap.fill(text, width=50) # ensuring that the line end at 50 characters 
# #         tooltip = tk.Toplevel(self.root)
# #         tooltip.wm_overrideredirect(True)
# #         tooltip.wm_geometry(f"+{int(x) + 10}+{int(y) + 10}")  # Ensure integer coordinates
# #         label = tk.Label(tooltip, text=wrapped_text, background="light yellow", relief="solid", padx=5, pady=5)
# #         label.pack()
# #         self.active_tooltip = tooltip
# #     def toggle_sticky_note_mode(self):
# #         """Toggle sticky note mode"""
# #         if self.sticky_note_mode:
# #             self.sticky_note_mode = False
# #             self.canvas.unbind("<Button-1>")
# #         else:
# #             self.enable_sticky_note_mode()
# #     def save_pdf(self):
# #         """Save the PDF with embedded sticky notes to a file."""
# #         if not self.pdf_document:
# #             return
# #         temp_pdf = fitz.open()  
# #         for page in self.pdf_document:
# #             temp_pdf.insert_pdf(self.pdf_document, from_page=page.number, to_page=page.number)
# #         max_line_length = 50
# #         for (page_num, x_scaled, y_scaled), text in self.sticky_notes.items():
# #             page = temp_pdf[page_num]
# #             x_position = x_scaled
# #             y_position = y_scaled
# #             marker_size = 12 
# #             text_size = 10
# #             page.insert_text(
# #                 point=(x_position, y_position),text="📌",
# #                 fontsize=marker_size,color=(1, 0, 0))
# #             lines = self.wrap_text(text, max_line_length)
# #             text_offset = 15
# #             max_text_width = max(len(line) for line in lines) * text_size * 0.6  
# #             max_text_height = len(lines) * text_size * 1.5  
# #             padding = 10
# #             background_width = max_text_width + padding * 2  
# #             background_height = max_text_height + padding * 2  
# #             page.draw_rect(
# #                 rect=(x_position - padding, y_position + text_offset - padding, x_position + background_width, y_position + text_offset + background_height),
# #                 color=(1, 1, 0), overlay=True,
# #                 fill_opacity=0.5,fill=(1, 1, 0))
# #             for i, line in enumerate(lines):
# #                 page.insert_text(
# #                     point=(x_position, y_position + text_offset + (i * text_size * 1.5)),  # Vertical spacing between lines
# #                     text=line,
# #                     fontsize=text_size,color=(0, 0, 0))
# #         if temp_pdf:
# #             encoded_pdf_data = self.encode_pdf_data(temp_pdf.write())
# #             unreadable_filename = "temp_file.temp"  # Can choose a random or actual/unique filename to handle multiprocessing
# #             self.temp_file_path = self.save_pdf_as_temp(unreadable_filename, encoded_pdf_data) # encoding is not rquired, then can pass the temp_pdf directly.
# #             if self.temp_file_path:
# #                 files = {'file': (edit_file_name, open(fileurl, 'rb'))}
# #                 response = requests.post(self.server_url, files=files)
# #                 if response.status_code == 200 or response.status_code == 201:
# #                     print("File successfully uploaded to server.")
# #                 else:
# #                     print(f"Failed to upload file. Status code: {response.status_code, response.text}")
# #             else:
# #                 print("No file to send.")
# #         else:
# #             print("No PDF data to save.")
# #     def decode_pdf_data(self, encoded_pdf_data):
# #         """Decode the base64-encoded PDF data."""
# #         return base64.b64decode(encoded_pdf_data)
# #     def encode_pdf_data(self, pdf_data):
# #         """Encode the PDF data to an unreadable format (base64)."""
# #         return base64.b64encode(pdf_data)
# #     def save_pdf_as_temp(self, unreadable_filename, pdf_data):
# #         """Save the base64-encoded PDF as a temporary file."""
# #         temp_dir = tempfile.gettempdir()
# #         temp_file_path = os.path.join(temp_dir, unreadable_filename)
# #         with open(temp_file_path, 'wb') as temp_file:
# #             temp_file.write(pdf_data)
# #         return temp_file_path
# #     def delete_temp_file(self):
# #         """Delete the temporary file."""
# #         try:
# #             if self.temp_file_path:
# #                 os.remove(self.temp_file_path)
# #                 print(f"Temporary file {self.temp_file_path} deleted successfully.")
# #         except Exception as e:
# #             print(f"Error while deleting temp file: {e}")
# #     def on_close(self):
# #         """Handle window close event, cleanup, and exit."""
# #         if self.temp_file_path:
# #             self.delete_temp_file() 
# #         self.root.quit()
# #     def wrap_text(self, text, max_line_length):
# #         """Wrap the text into lines with a maximum number of characters per line."""
# #         words = text.split(" ")
# #         lines = []
# #         current_line = ""
# #         for word in words:
# #             if len(current_line) + len(word) + 1 <= max_line_length:
# #                 current_line += (word + " ")
# #             else:
# #                 lines.append(current_line.strip())
# #                 current_line = word + " "
# #         if current_line:
# #             lines.append(current_line.strip())
# #         return lines
# #     def prev_page(self):
# #         if self.current_page > 0:
# #             self.current_page -= 1
# #             self.render_page(self.current_page)
# #     def next_page(self):
# #         if self.current_page < len(self.pdf_document) - 1:
# #             self.current_page += 1
# #             self.render_page(self.current_page)
# #     def rotate_90clockwise(self):
# #         """Rotate the current page clockwise."""
# #         if not self.pdf_document:
# #             return
# #         page = self.pdf_document[self.current_page]
# #         page.set_rotation((page.rotation + 90) % 360)
# #         self.render_page(self.current_page)
# #     def rotate_180clockwise(self):
# #         """Rotate the current page clockwise."""
# #         if not self.pdf_document:
# #             return
# #         page = self.pdf_document[self.current_page]
# #         page.set_rotation((page.rotation + 180) % 360)
# #         self.render_page(self.current_page)
# #     def rotate_270clockwise(self):
# #         """Rotate the current page clockwise."""
# #         if not self.pdf_document:
# #             return
# #         page = self.pdf_document[self.current_page]
# #         page.set_rotation((page.rotation + 270) % 360)
# #         self.render_page(self.current_page)
# #     def toggle_invert_colors(self):
# #         """Toggle color inversion for the PDF."""
# #         if not self.pdf_document:
# #             return
# #         self.is_inverted = not self.is_inverted
# #         self.render_page(self.current_page)
# #         self.redraw_sticky_notes()
# #     def verify_protocol_registration(self):
# #         """Check and display the protocol registration status"""
# #         handler = ProtocolHandler()
# #         is_registered = handler.verify_registration()
# #         if is_registered:
# #             status_msg = (
# #                 "Protocol handler is properly registered.\n\n"
# #                 f"Protocol: {handler.protocol}\n"
# #                 f"OS: {handler.os_type}\n"
# #                 f"App Path: {handler.app_path}\n\n"
# #                 "The application will open automatically when clicking PDF links.")
# #             messagebox.showinfo("Protocol Registration", status_msg)
# #         else:
# #             status_msg = (
# #                 "Protocol handler is not registered or registration is incomplete.\n\n"
# #                 f"Protocol: {handler.protocol}\n"
# #                 f"OS: {handler.os_type}\n"
# #                 f"App Path: {handler.app_path}\n\n"
# #                 "Would you like to attempt registration now?")
# #             result = messagebox.askquestion(
# #                 "Protocol Registration", 
# #                 status_msg,
# #                 icon='warning')
# #             if result == 'yes':
# #                 try:
# #                     success, message = handler.register()
# #                     if success:
# #                         messagebox.showinfo(
# #                             "Registration Success", 
# #                             f"{message}\n\n"
# #                             f"Protocol: {handler.protocol}\n"
# #                             f"OS: {handler.os_type}\n"
# #                             f"App Path: {handler.app_path}")
# #                     else:
# #                         messagebox.showerror(
# #                             "Registration Failed", 
# #                             f"{message}\n\n"
# #                             "Please check the console for more details.")
# #                 except Exception as e:
# #                     messagebox.showerror(
# #                         "Registration Error", 
# #                         f"Failed to register protocol handler:\n{str(e)}")

# # if __name__ == "__main__":
# #     try:
# #         handler = ProtocolHandler()
# #         success, message = handler.register()
# #         if success:
# #             print(message)
# #         else:
# #             print(f"Warning: {message}")
# #     except Exception as e:
# #         print(f"Failed to register protocol handler: {e}")

# #     root = tk.Tk()
# #     app = StickyNotesPDFApp(root)
# #     root.mainloop()

























































































# canvas_frame = ctk.CTkFrame(self.root)
# tooltip = ctk.CTkToplevel(self.root)
# self.thumbnail_frame = ctk.CTkFrame(canvas_frame, width=150, fg_color="lightgray")
# label = ctk.CTkLabel(tooltip, text=tooltip_text, fg_color="light yellow", corner_radius=5, padx=5, pady=5)


























# # def create_duplicate_window(self):
# #         """Creates a duplicate window to display a PDF independently."""
# #         if not self.pdf_document:
# #             messagebox.showerror("Error", "No PDF is loaded to view in secondary window.")
# #             return
        
# #         duplicate_window = Toplevel(self.root)
# #         duplicate_window.title("Secondary PDF Viewer")
# #         duplicate_window.geometry("900x650")
# #         self.duplicate_windows.append(duplicate_window)
# #         duplicate_change_history = []
# #         duplicate_highlights = []
# #         duplicate_sticky_notes = {}
# #         # Toolbar
# #         toolbar = tk.Frame(duplicate_window)
# #         toolbar.pack(fill=tk.X, pady=8)

# #         # Thumbnail Scroll Area
# #         thumbnail_frame = tk.Frame(duplicate_window)
# #         thumbnail_frame.pack(side=tk.LEFT, fill=tk.Y)
# #         thumbnail_canvas = tk.Canvas(thumbnail_frame, bg="lightgray", width=200)
# #         thumbnail_scrollbar = tk.Scrollbar(
# #             thumbnail_frame, orient=tk.VERTICAL, command=thumbnail_canvas.yview
# #         )
# #         thumbnail_canvas.configure(yscrollcommand=thumbnail_scrollbar.set)
# #         thumbnail_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
# #         thumbnail_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
# #         inner_thumbnail_frame = tk.Frame(thumbnail_canvas, bg="lightgray")
# #         thumbnail_canvas.create_window((0, 0), window=inner_thumbnail_frame, anchor="nw")

# #         # Main Canvas for PDF Rendering
# #         pdf_frame = tk.Frame(duplicate_window)
# #         pdf_frame.pack(fill=tk.BOTH, expand=True, side=tk.RIGHT)
# #         pdf_canvas = tk.Canvas(pdf_frame, bg="lightgray", width=700, height=600)
# #         pdf_h_scrollbar = tk.Scrollbar(pdf_frame, orient=tk.HORIZONTAL, command=pdf_canvas.xview)
# #         pdf_v_scrollbar = tk.Scrollbar(pdf_frame, orient=tk.VERTICAL, command=pdf_canvas.yview)

# #         # Configure canvas scroll commands
# #         pdf_canvas.configure(
# #             xscrollcommand=pdf_h_scrollbar.set, 
# #             yscrollcommand=pdf_v_scrollbar.set
# #         )

# #         # Pack canvas and scrollbars ensuring proper layout
# #         pdf_canvas.grid(row=0, column=0, sticky="nsew")  # Canvas fills the available space
# #         pdf_h_scrollbar.grid(row=1, column=0, sticky="ew")  # Horizontal scrollbar below the canvas
# #         pdf_v_scrollbar.grid(row=0, column=1, sticky="ns")  # Vertical scrollbar to the right of the canvas

# #         # Configure grid weights for resizing
# #         pdf_frame.grid_rowconfigure(0, weight=1)
# #         pdf_frame.grid_columnconfigure(0, weight=1)

# #         # Variables for duplicate window state
# #         duplicate_pdf_document = self.pdf_document
# #         duplicate_current_page = self.current_page
# #         duplicate_zoom_factor = self.zoom_factor
# #         duplicate_is_inverted = self.is_inverted
# #         self.start_x, self.start_y, self.rectangle_id = None, None, None

# #         def render_duplicate_page(page_number):
# #             if not duplicate_pdf_document:
# #                 return
# #             page = duplicate_pdf_document.load_page(page_number)
# #             matrix = fitz.Matrix(duplicate_zoom_factor, duplicate_zoom_factor)
# #             pix = page.get_pixmap(matrix=matrix)
# #             img = Image.open(io.BytesIO(pix.tobytes("png")))
# #             if duplicate_is_inverted:
# #                 img = ImageOps.invert(img.convert("RGB"))
# #             img_tk = ImageTk.PhotoImage(img)
# #             pdf_canvas.delete("all")
# #             pdf_canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
# #             pdf_canvas.img_tk = img_tk
# #             pdf_canvas.config(scrollregion=(0, 0, pix.width, pix.height))
# #             # Re-apply highlights
# #             for hl in duplicate_highlights:
# #                 if hl["page"] == page_number:
# #                     pdf_canvas.create_rectangle(
# #                         hl["coords"], outline="yellow", width=2, tag="highlight"
# #                     )
# #             for (page, x, y), note in duplicate_sticky_notes.items():
# #                 if page == page_number:
# #                     x_position = x * duplicate_zoom_factor
# #                     y_position = y * duplicate_zoom_factor
# #                     pdf_canvas.create_text(
# #                         x_position, y_position, text="📌", font=("Arial", 16), fill="black", tags="sticky_note"
# #                     )

# #         def duplicate_render_thumbnails():
# #             if not self.pdf_document:
# #                 return
# #             for widget in inner_thumbnail_frame.winfo_children():
# #                 widget.destroy()
# #             thumbnail_width = 150
# #             thumbnail_height = 200
# #             for page_number in range(len(self.pdf_document)):
# #                 page = self.pdf_document.load_page(page_number)
# #                 pix = page.get_pixmap(matrix=fitz.Matrix(0.27, 0.27))
# #                 img = Image.open(io.BytesIO(pix.tobytes("png")))
# #                 img_resized = ImageOps.fit(
# #                     img, (thumbnail_width, thumbnail_height), method=Image.LANCZOS
# #                 )
# #                 img_tk = ImageTk.PhotoImage(img_resized)
# #                 frame = tk.Frame(inner_thumbnail_frame, bg="lightgray", highlightthickness=2)
# #                 frame.pack(pady=5, padx=20)
# #                 frame.bind("<Button-1>", lambda e, p=page_number: select_page(p))
# #                 label = tk.Label(frame, image=img_tk, bg="lightgray")
# #                 label.pack()
# #                 label.bind("<Button-1>", lambda e, p=page_number: select_page(p))
# #                 frame.img_tk = img_tk
# #                 frame.tag = page_number  # Tag for highlighting
# #             inner_thumbnail_frame.update_idletasks()
# #             thumbnail_canvas.configure(scrollregion=thumbnail_canvas.bbox("all"))

# #         def highlight_thumbnail(page_number):
# #             for frame in inner_thumbnail_frame.winfo_children():
# #                 if hasattr(frame, "tag") and frame.tag == page_number:
# #                     frame.config(bg="orange", highlightbackground="orange")
# #                 else:
# #                     frame.config(bg="lightgray", highlightbackground="lightgray")

# #         def enable_dup_sticky_note_mode():
# #             """Activate sticky note mode for duplicate viewer."""
# #             pdf_canvas.bind("<Button-1>", on_canvas_click)

# #         def on_canvas_click(event):
# #             """Add a sticky note at the clicked position on the canvas."""
# #             x = pdf_canvas.canvasx(event.x)
# #             y = pdf_canvas.canvasy(event.y)
# #             x_scaled = x / duplicate_zoom_factor
# #             y_scaled = y / duplicate_zoom_factor
# #             note_text = self.ask_for_note_text(x, y)
# #             if not note_text:
# #                 return
# #             duplicate_sticky_notes[(duplicate_current_page, x_scaled, y_scaled)] = note_text
# #             duplicate_change_history.append(("sticky_note", duplicate_current_page, x_scaled, y_scaled, note_text))
# #             marker_id = pdf_canvas.create_oval(x-5, y-5, x+5, y+5, fill="blue", outline="blue", tags="sticky_note")
# #             pdf_canvas.tag_bind(marker_id, "<Enter>", lambda e, text=note_text: show_tooltip(e.x_root, e.y_root, text))
# #             pdf_canvas.tag_bind(marker_id, "<Leave>", hide_tooltip)
# #             render_duplicate_page(duplicate_current_page)

# #         def show_tooltip(event, text):
# #             """Display a tooltip."""
# #             x = event.x_root + 10
# #             y = event.y_root + 10
# #             if hasattr(self, "tooltip_window") and self.tooltip_window:
# #                 self.tooltip_window.destroy()  # Remove any existing tooltip
# #             self.tooltip_window = tk.Toplevel()
# #             self.tooltip_window.wm_overrideredirect(True)
# #             self.tooltip_window.geometry(f"+{x}+{y}")
# #             label = tk.Label(self.tooltip_window, text=text, background="yellow", relief="solid", borderwidth=1)
# #             label.pack()

# #         def hide_tooltip():
# #             """Hide the tooltip."""
# #             if hasattr(self, 'tooltip_window') and self.tooltip_window:
# #                 self.tooltip_window.destroy()
# #                 self.tooltip_window = None
               
# #         # Page selection in duplicate window
# #         def select_page(page_number):
# #             render_duplicate_page(page_number)
# #             highlight_thumbnail(page_number)

# #         # Toolbar Buttons
# #         def zoom_in():
# #             nonlocal duplicate_zoom_factor
# #             duplicate_zoom_factor += 0.2
# #             render_duplicate_page(duplicate_current_page)

# #         def zoom_out():
# #             nonlocal duplicate_zoom_factor
# #             if duplicate_zoom_factor > 0.4:
# #                 duplicate_zoom_factor -= 0.2
# #                 render_duplicate_page(duplicate_current_page)

# #         def toggle_invert_colors():
# #             nonlocal duplicate_is_inverted
# #             duplicate_is_inverted = not duplicate_is_inverted
# #             render_duplicate_page(duplicate_current_page)

# #         def prev_page():
# #             nonlocal duplicate_current_page
# #             if duplicate_current_page > 0:
# #                 duplicate_current_page -= 1
# #                 render_duplicate_page(duplicate_current_page)

# #         def next_page():
# #             nonlocal duplicate_current_page
# #             if duplicate_current_page < len(duplicate_pdf_document) - 1:
# #                 duplicate_current_page += 1
# #                 render_duplicate_page(duplicate_current_page)

# #         def rotate_90clockwise():
# #             nonlocal duplicate_current_page
# #             if not self.pdf_document:
# #                 return
# #             page = self.pdf_document[duplicate_current_page]
# #             page.set_rotation((page.rotation + 90) % 360) 
# #             render_duplicate_page(duplicate_current_page) 

# #         def rotate_180clockwise():
# #             """Rotate the current page clockwise."""
# #             if not self.pdf_document:
# #                 return
# #             page = self.pdf_document[duplicate_current_page]
# #             page.set_rotation((page.rotation + 180) % 360)
# #             render_duplicate_page(duplicate_current_page)

# #         def rotate_270clockwise():
# #             """Rotate the current page clockwise."""
# #             if not self.pdf_document:
# #                 return
# #             page = self.pdf_document[duplicate_current_page]
# #             page.set_rotation((page.rotation + 270) % 360)
# #             render_duplicate_page(duplicate_current_page)

# #         def best_fit():
# #             canvas_width = pdf_canvas.winfo_width()
# #             canvas_height = pdf_canvas.winfo_height()
# #             page = duplicate_pdf_document.load_page(duplicate_current_page)
# #             page_width, page_height = page.rect.width, page.rect.height
# #             width_scale = canvas_width / page_width
# #             height_scale = canvas_height / page_height
# #             nonlocal duplicate_zoom_factor
# #             duplicate_zoom_factor = min(width_scale, height_scale)
# #             render_duplicate_page(duplicate_current_page)

# #         def best_width():
# #             canvas_width = pdf_canvas.winfo_width()
# #             page = duplicate_pdf_document.load_page(duplicate_current_page)
# #             page_width = page.rect.width
# #             nonlocal duplicate_zoom_factor
# #             duplicate_zoom_factor = canvas_width / page_width
# #             render_duplicate_page(duplicate_current_page)

# #         def enable_dup_highlight_mode():
# #             """Activate highlight mode for duplicate viewer."""
# #             pdf_canvas.unbind("<Button-1>")
# #             pdf_canvas.bind("<Button-1>", start_rectangle)
# #             pdf_canvas.bind("<B1-Motion>", draw_rectangle)
# #             pdf_canvas.bind("<ButtonRelease-1>", finalize_highlight)
# #             self.start_x, self.start_y = None, None

# #         def dup_undo_change():
# #             """Undo the last change in the duplicate window."""
# #             if not duplicate_change_history:
# #                 print("No actions to undo.")
# #                 return
# #             last_action = duplicate_change_history.pop()
# #             action_type, page_number, *details = last_action

# #             if action_type == "highlight":
# #                 rect = details[0]
# #                 for item in pdf_canvas.find_withtag("highlight"):
# #                     coords = pdf_canvas.coords(item)
# #                     # Convert canvas coordinates to PDF coordinates for comparison
# #                     scaled_coords = (
# #                         coords[0] / duplicate_zoom_factor, coords[1] / duplicate_zoom_factor,
# #                         coords[2] / duplicate_zoom_factor, coords[3] / duplicate_zoom_factor
# #                     )
# #                     if scaled_coords == (rect.x0, rect.y0, rect.x1, rect.y1):
# #                         pdf_canvas.delete(item)
# #                         break
# #                 duplicate_highlights[:] = [hl for hl in duplicate_highlights if hl["coords"] != (rect.x0, rect.y0, rect.x1, rect.y1)]

# #             elif action_type == "sticky_note":
# #                 x, y = details[:2]
# #                 duplicate_sticky_notes.pop((page_number, x, y), None)
# #                 render_duplicate_page(page_number)

# #             render_duplicate_page(page_number)

# #         def start_rectangle(event):
# #             """Start a rectangle selection for highlighting."""
# #             self.start_x = pdf_canvas.canvasx(event.x)
# #             self.start_y = pdf_canvas.canvasy(event.y)
# #             self.rectangle_id = pdf_canvas.create_rectangle(
# #                 self.start_x, self.start_y, self.start_x, self.start_y, outline="yellow"
# #             )

# #         def draw_rectangle(event):
# #             """Draw the rectangle dynamically as the mouse is dragged."""
# #             if self.rectangle_id:
# #                 current_x = pdf_canvas.canvasx(event.x)
# #                 current_y = pdf_canvas.canvasy(event.y)
# #                 pdf_canvas.coords(self.rectangle_id, self.start_x, self.start_y, current_x, current_y)

# #         def finalize_highlight(event):
# #             """Finalize the highlight and save it to the PDF."""
# #             if self.start_x is None or self.start_y is None:
# #                 return  # No valid starting point

# #             end_x = pdf_canvas.canvasx(event.x) / duplicate_zoom_factor
# #             end_y = pdf_canvas.canvasy(event.y) / duplicate_zoom_factor
# #             start_x = self.start_x / duplicate_zoom_factor
# #             start_y = self.start_y / duplicate_zoom_factor

# #             rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
# #             page = duplicate_pdf_document[duplicate_current_page]
# #             rotation = page.rotation
# #             page_width, page_height = self.page_width / self.zoom_factor, self.page_height / self.zoom_factor

# #             if rotation == 90:
# #                 rect = fitz.Rect(
# #                     rect.y0,
# #                     page_width - rect.x1,
# #                     rect.y1,
# #                     page_width - rect.x0
# #                 )
# #             elif rotation == 180:
# #                 rect = fitz.Rect(
# #                     page_width - rect.x1,
# #                     page_height - rect.y1,
# #                     page_width - rect.x0,
# #                     page_height - rect.y0
# #                 )
# #             elif rotation == 270:
# #                 rect = fitz.Rect(
# #                     page_height - rect.y1,
# #                     rect.x0,
# #                     page_height - rect.y0,
# #                     rect.x1
# #                 )


# #             try:
# #                 # Add the highlight annotation
# #                 annot = page.add_highlight_annot(rect)
# #                 annot.update()  # Save the annotation to the document
# #                 # Save the annotation for undo functionality
# #                 duplicate_change_history.append(("highlight", duplicate_current_page, rect))
# #             except Exception as e:
# #                 messagebox.showerror("Error", f"Failed to add highlight: {e}")
# #                 return

# #             # Refresh the page to display the highlight
# #             render_duplicate_page(duplicate_current_page)

# #             # Reset highlight mode
# #             pdf_canvas.unbind("<B1-Motion>")
# #             pdf_canvas.unbind("<ButtonRelease-1>")        

# #         def create_button(parent, text, command, tooltip_text):
# #             button = ttk.Button(parent, text=text, style="Modern.TButton", command=command, width=6)
# #             button.pack(side=tk.LEFT, padx=2)
# #             button.bind("<Enter>", lambda event: show_tooltip(event, tooltip_text))
# #             button.bind("<Leave>", hide_tooltip)

# #         create_button(toolbar, "🔍 -", zoom_out, "Zoom Out")
# #         create_button(toolbar, "🔍 +", zoom_in, "Zoom In")
# #         create_button(toolbar, "⬅️", prev_page, "Previous Page")
# #         create_button(toolbar, "➡️", next_page, "Next Page")
# #         create_button(toolbar, "🌓", toggle_invert_colors, "Invert Colors")
# #         create_button(toolbar, "❖", best_fit, "Best Fit")
# #         create_button(toolbar, "↔", best_width, "Best Width")
# #         create_button(toolbar, "✒️", enable_dup_highlight_mode, "Highlight")
# #         create_button(toolbar, "📌", enable_dup_sticky_note_mode, "Add Sticky Note")
# #         create_button(toolbar, "↩️", dup_undo_change, "Undo")
# #         create_button(toolbar, "⮧", rotate_90clockwise, "Rotate 90° Right")
# #         create_button(toolbar, "⮠ ", rotate_180clockwise, "Rotate 180° Right")
# #         create_button(toolbar, "⮤", rotate_270clockwise, "Rotate 270° Right")       
# #         duplicate_render_thumbnails()
# #         render_duplicate_page(duplicate_current_page)
# #         def close_duplicate_window():
# #             self.duplicate_windows.remove(duplicate_window)
# #             duplicate_window.destroy()

# #         duplicate_window.protocol("WM_DELETE_WINDOW", close_duplicate_window)














# #     def enable_sticky_note_mode(self):
# #         """ Activate sticky note mode """
# #         self.sticky_note_mode = True  
# #         self.highlight_mode = False 
# #         self.canvas.unbind("<B1-Motion>") 
# #         self.canvas.unbind("<ButtonRelease-1>")
# #         self.canvas.bind("<Button-1>", self.on_canvas_click)
# #     def redraw_sticky_notes(self):
# #         """Redraw sticky notes after rendering the page."""
# #         self.canvas.delete("sticky_note") 
# #         emoji_fill = "white" if self.is_inverted else "black" 
# #         for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
# #             if page_num == self.current_page:
# #                 x_position = x_scaled * self.zoom_factor
# #                 y_position = y_scaled * self.zoom_factor
# #                 self.canvas.create_text(
# #                     x_position + 1, y_position + 1, text="📌", font=("Arial", 16),
# #                     fill="white", tags="sticky_note_shadow"
# #                 )
# #                 self.canvas.create_text(
# #                     x_position, y_position, text="📌", font=("Arial", 16),
# #                     fill=emoji_fill, tags="sticky_note"
# #                 )
# #     def on_canvas_click(self, event):
# #         """Add a sticky note at the clicked position on the canvas."""
# #         if not self.pdf_document or not self.sticky_note_mode:
# #             return
# #         x = self.canvas.canvasx(event.x)
# #         y = self.canvas.canvasy(event.y)
# #         print(f"Clicked coordinates (adjusted): {x}, {y}")
# #         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
# #             print("Click outside page bounds.")
# #             return  # Clicked outside the PDF page area
# #         note_text = self.ask_for_note_text(x, y)
# #         if not note_text:
# #             print("No note text entered.")
# #             return  # No text entered
# #         x_scaled = x / self.zoom_factor
# #         y_scaled = y / self.zoom_factor
# #         print(f"Scaled coordinates: {x_scaled}, {y_scaled}")
# #         self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
# #         self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
# #         print(f"Added sticky note: {('sticky_note', self.current_page, x_scaled, y_scaled, note_text)}")
# #         self.canvas.create_text(x, y, text="📌", font=("Arial", 16))
# #         self.sticky_note_mode = False
# #         print("Sticky note mode disabled.")
# #     def ask_for_note_text(self, x, y):
# #         """Prompt the user to enter sticky note text with a modern UI and return the entered text."""
# #         dialog = tk.Toplevel(self.root) 
# #         dialog.title("Enter Sticky Note")
# #         dialog.geometry("400x250")
# #         dialog.configure(bg="#f9f9f9")
# #         dialog.resizable(False, False)
# #         label = tk.Label(
# #             dialog, text="Enter your note:", font=("Arial", 14, "bold"), bg="#f9f9f9"
# #         )
# #         label.pack(pady=(15, 10))
# #         text_box = tk.Text(dialog, wrap=tk.WORD, height=6, width=40, font=("Arial", 12), relief="solid")
# #         text_box.pack(padx=15, pady=5, fill=tk.X)
# #         text_box.focus_set()  
# #         note_text_var = tk.StringVar()
# #         def on_ok_click():
# #             note_text = text_box.get("1.0", tk.END).strip() 
# #             if note_text:
# #                 note_text_var.set(note_text) 
# #                 dialog.destroy()
# #             else:
# #                 messagebox.showwarning(
# #                     "Empty Note", "You must enter some text to save the sticky note.")
# #         def create_rounded_button(parent, text, bg_color, fg_color, command):
# #             canvas = tk.Canvas(parent, width=120, height=40, bg="#f9f9f9", highlightthickness=0)
# #             canvas.pack(side=tk.LEFT, padx=10)
# #             canvas.create_oval(10, 10, 40, 40, fill=bg_color, outline=bg_color)
# #             canvas.create_oval(80, 10, 110, 40, fill=bg_color, outline=bg_color)
# #             canvas.create_rectangle(25, 10, 95, 40, fill=bg_color, outline=bg_color)
# #             button_text = canvas.create_text(60, 25, text=text, fill=fg_color, font=("Arial", 12, "bold"))
# #             def on_click(event):
# #                 command()
# #             canvas.tag_bind(button_text, "<Button-1>", on_click)
# #             canvas.tag_bind("all", "<Enter>", lambda e: canvas.configure(cursor="hand2"))
# #             canvas.tag_bind("all", "<Button-1>", on_click)
# #             return canvas
# #         buttons_frame = tk.Frame(dialog, bg="#f9f9f9")
# #         buttons_frame.pack(side=tk.BOTTOM, pady=15)
# #         create_rounded_button(buttons_frame, "OK", bg_color="#4CAF50", fg_color="white", command=on_ok_click)
# #         create_rounded_button(buttons_frame, "Cancel", bg_color="#F44336", fg_color="white", command=dialog.destroy)
# #         dialog.grab_set()
# #         dialog.wait_window()
# #         self.sticky_note_mode = False
# #         return note_text_var.get() or None