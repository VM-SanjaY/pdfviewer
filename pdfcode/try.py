import os
import sys
import subprocess
import platform
import ctypes
from pathlib import Path
class ProtocolHandler:
    def __init__(self, protocol_name="idmspdf", app_path=None):
        self.protocol = protocol_name
        self.os_type = platform.system().lower()
        self.app_path = app_path or self._get_app_path()
    def _get_app_path(self):
        """Get the path to the PDF editor executable"""
        if getattr(sys, 'frozen', False):
            app_path = Path(sys.executable)
            if self.os_type == "darwin":
                return str(app_path.parent.parent.parent)
            return str(app_path)
        else:
            return os.path.abspath(sys.argv[0])
    def is_admin(self):
        """Check if the program has admin privileges"""
        try:
            if self.os_type == "windows":
                return ctypes.windll.shell32.IsUserAnAdmin()
            return False
        except Exception:
            return False
    def elevate_privileges(self):
        """Attempt to elevate privileges if needed"""
        if self.is_admin():
            return True
        try:
            if self.os_type == "windows":
                ctypes.windll.shell32.ShellExecuteW(
                    None, "runas", sys.executable, " ".join(sys.argv), None, 1)
            return True
        except Exception as e:
            print(f"Failed to elevate privileges: {e}")
            return False
    def register(self):
        """Register protocol handler and verify registration"""
        try:
            if self.verify_registration():
                return True, "Protocol handler is already registered"
            if self.os_type == "windows":
                if not self.is_admin() and not self.elevate_privileges():
                    return False, "Administrator privileges required for Windows registration"
                success = self._register_windows()
            if success:
                is_verified = self.verify_registration()
                if is_verified:
                    return True, "Protocol handler registered successfully"
                else:
                    return False, "Registration verification failed"
            return False, "Registration failed"          
        except Exception as e:
            return False, f"Registration error: {str(e)}"
    def _register_windows(self):
        """Windows registry-based protocol registration"""
        import winreg
        try:
            with winreg.CreateKey(winreg.HKEY_CLASSES_ROOT, self.protocol) as key:
                winreg.SetValue(key, "", winreg.REG_SZ, f"URL:{self.protocol} Protocol")
                winreg.SetValueEx(key, "URL Protocol", 0, winreg.REG_SZ, "")              
                with winreg.CreateKey(key, r"shell\open\command") as cmd_key:
                    cmd_path = f'"{self.app_path}" "%1"'
                    winreg.SetValue(cmd_key, "", winreg.REG_SZ, cmd_path)
            return True
        except Exception as e:
            return False
    def verify_registration(self):
        """Verify if the protocol handler is properly registered"""
        try:         
            if self.os_type == "windows":
                result = self._verify_windows()
            else:
                result = False
            return result            
        except Exception as e:
            return False
    def _verify_windows(self):
        """Verify Windows registry entries"""
        import winreg
        try:
            with winreg.OpenKey(winreg.HKEY_CLASSES_ROOT, self.protocol) as key:
                protocol_value = winreg.QueryValue(key, "")
                with winreg.OpenKey(key, r"shell\open\command") as cmd_key:
                    cmd_value = winreg.QueryValue(cmd_key, "")
                    expected_cmd = f'"{self.app_path}" "%1"'
                    return (protocol_value == f"URL:{self.protocol} Protocol" and 
                           cmd_value == expected_cmd)
        except WindowsError:
            return False
    @staticmethod
    def handle_protocol_url(url):
        """Handle incoming protocol URLs"""
        try:
            from urllib.parse import unquote, quote
            if url.startswith(('idmspdf://', 'idmspdf:')):
                url = url.replace('idmspdf://', '').replace('idmspdf:', '')
            while url.startswith('//'):
                url = url[1:]
            url = unquote(url)
            url = unquote(url)
            url = url.rstrip('/')
            if not url.startswith(('http://', 'https://')):
                url = 'https://' + url
            parts = url.split('//')
            if len(parts) > 1:
                domain = parts[0] + '//' + parts[1].split('/')[0]
                path = '/'.join(parts[1].split('/')[1:])
                if path:
                    encoded_path = quote(path, safe='/')
                    url = f"{domain}/{encoded_path}"
            return url           
        except Exception as e:
            return url
import io
import tkinter as tk
import tkinter.ttk as ttk
from tkinter import filedialog, messagebox
import fitz
import textwrap
from PIL import Image, ImageTk, ImageOps
import requests
from urllib.parse import urlparse
import sys
from protocol_handler import ProtocolHandler
class StickyNotesPDFApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Atic PDF Editor")
        self.zoom_factor = 1.0
        self.sticky_note_mode = False  # default set to deactive after each use.
        self.highlight_mode = False # default set to deactive after each use.
        self.change_history = []  # to remove all change in order.
        self.sticky_notes = {}  # to coordinate and text storing
        self.thumbnails = [] # for listing the thumnails
        self.pdf_document = None
        self.current_page = None
        self.create_widgets()  # design and alignment for buttons.
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<Motion>", self.on_mouse_hover)  # to view tooltip
        self.active_tooltip = None 
        self.page_width = 0
        self.page_height = 0      
        if len(sys.argv) > 1:
            pdf_url = ProtocolHandler.handle_protocol_url(sys.argv[1])
            try:
                self.load_pdf(pdf_url)
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
    def create_widgets(self):
        style = ttk.Style()
        style.configure(
            "Modern.TButton",
            font=("Arial", 12),
            padding=(2, 2),  # Minimize padding for a compact look
            relief="flat",
            background="lightgray",
            foreground="black",
            borderwidth=1,)
        style.map(
            "Modern.TButton",
            background=[("active", "darkgray"), ("!disabled", "lightgray")],
            foreground=[("active", "white")],)
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
                command=command)
            button.pack(fill=tk.BOTH, expand=True)  # Fill the frame
            button.bind("<Enter>", lambda event, b=text, t=tooltip_text: self.button_tooltip(event, b, t))
            button.bind("<Leave>", self.hide_tooltip)
            return button
        create_button(toolbar, "📂", self.load_pdf, "Load PDF")  #  text that is visible when hovered
        create_button(toolbar, "❄️", self.freeze_page, "Freeze Page")
        canvas_frame = tk.Frame(self.root)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        self.canvas = tk.Canvas(canvas_frame, bg="lightgray", width=900, height=650)
        self.h_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
        self.v_scrollbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)
        self.h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.canvas.bind("<MouseWheel>", self.on_mouse_scroll)
        self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_scroll)
    def button_tooltip(self, event, button_text, tooltip_text):
        """Display tooltip when hovering over a button."""
        if self.active_tooltip:
            self.active_tooltip.destroy() # to destroy automatiacally each second
        tooltip = tk.Toplevel(self.root)
        tooltip.wm_overrideredirect(True) # it used for closing tooltip
        tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")  # text Position near the mouse hover
        label = tk.Label(tooltip, text=tooltip_text, background="light yellow", relief="solid", padx=5, pady=5)
        label.pack()
        self.active_tooltip = tooltip
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
            self.pdf_path = file_path  
            self.current_page = 0
            self.render_page(self.current_page)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF: {str(e)}")
            return
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
        self.canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
        self.canvas.img_tk = img_tk  # Store reference to avoid cache collection
        self.page_width, self.page_height = pix.width, pix.height
        self.canvas.config(scrollregion=(0, 0, self.page_width, self.page_height))
        self.redraw_sticky_notes()
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
import win32serviceutil
import win32service
import win32event
import servicemanager
import subprocess
class PDFEditorService(win32serviceutil.ServiceFramework):
    _svc_name_ = "PDFEditorService"
    _svc_display_name_ = "PDF Editor Service"
    _svc_description_ = "Service to run PDF Editor as a background process"
    def __init__(self, args):
        win32serviceutil.ServiceFramework.__init__(self, args)
        self.hWaitStop = win32event.CreateEvent(None, 0, 0, None)
        self.process = None
    def SvcStop(self):
        self.ReportServiceStatus(win32service.SERVICE_STOP_PENDING)
        win32event.SetEvent(self.hWaitStop)
        if self.process:
            self.process.terminate()
            self.process.wait()
    def SvcDoRun(self):
        servicemanager.LogMsg(servicemanager.EVENTLOG_INFORMATION_TYPE,
                              servicemanager.PYS_SERVICE_STARTED,
                              (self._svc_name_, ''))
        self.process = subprocess.Popen(['pdfeditor.exe'])
        win32event.WaitForSingleObject(self.hWaitStop, win32event.INFINITE)
if __name__ == '__main__':
    win32serviceutil.HandleCommandLine(PDFEditorService)















































# import io
# import tkinter as tk
# import tkinter.ttk as ttk
# from tkinter import filedialog, messagebox, Toplevel, Canvas, Button,simpledialog
# import tkinter.colorchooser as colorchooser
# import fitz  # PyMuPDF
# import textwrap
# from PIL import Image, ImageTk, ImageOps

# class StickyNotesPDFApp:
#     def __init__(self, root):
#         self.root = root
#         self.root.title("PDF Editor")
#         self.zoom_factor = 1.0
#         self.canvas_click_mode = None
#         self.sticky_note_mode = False
#         self.highlight_mode = False
#         self.change_history = []
#         self.sticky_notes = {}
#         self.pdf_document = None
#         self.current_page = None
#         self.create_widgets()
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
#         self.canvas.bind("<Motion>", self.on_mouse_hover)
#         self.active_tooltip = None
#         self.page_width = 0
#         self.page_height = 0
#         self.sticky_note_mode = False    
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
#         create_button(toolbar, "📂", self.load_pdf, "Load PDF")
#         create_button(toolbar, "↩️", self.undo_change, "Undo")
#         create_button(toolbar, "📌", self.toggle_sticky_note_mode, "Sticky Note")
#         create_button(toolbar,"✒",self.enable_highlight_mode,"Highlighter")
#         create_button(toolbar, "📝", self.add_text_to_pdf, "Add Text to PDF")     
#         canvas_frame = tk.Frame(self.root)
#         canvas_frame.pack(fill=tk.BOTH, expand=True)
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
#             self.active_tooltip.destroy()
#         tooltip = tk.Toplevel(self.root)
#         tooltip.wm_overrideredirect(True)
#         tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")  # Position near the mouse
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
#         if not file_path:
#             return
#         self.pdf_path = file_path  # Save the file path for later use
#         self.pdf_document = fitz.open(file_path)
#         self.current_page = 0
#         self.is_inverted = False
#         self.render_page(self.current_page)
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
#         self.canvas.img_tk = img_tk  # Store reference to avoid garbage collection
#         self.page_width, self.page_height = pix.width, pix.height
#         self.canvas.config(scrollregion=(0, 0, self.page_width, self.page_height))
#         self.redraw_sticky_notes()
#     def on_mouse_scroll(self, event):
#         """Handle vertical scrolling with the mouse wheel."""
#         self.canvas.yview_scroll(-1 * (event.delta // 120), "units")
#     def on_shift_mouse_scroll(self, event):
#         """Handle horizontal scrolling with Shift + mouse wheel."""
#         self.canvas.xview_scroll(-1 * (event.delta // 120), "units")
#     def enable_sticky_note_mode(self):
#         """ Activate sticky note mode """
#         self.sticky_note_mode = True  # Enable sticky note mode
#         self.highlight_mode = False  # Disable highlight mode
#         self.canvas.unbind("<B1-Motion>")
#         self.canvas.unbind("<ButtonRelease-1>")
#         self.canvas.bind("<Button-1>", self.on_canvas_click)
#     def redraw_sticky_notes(self):
#         """Redraw sticky notes after rendering the page."""
#         self.canvas.delete("sticky_note")  # Remove any previous sticky notes
#         emoji_fill = "white" if self.is_inverted else "black"  # Contrast with background
#         for (page_num, x_scaled, y_scaled), _ in self.sticky_notes.items():
#             if page_num == self.current_page:
#                 x_position = x_scaled * self.zoom_factor
#                 y_position = y_scaled * self.zoom_factor
#                 self.canvas.create_text(
#                     x_position + 1, y_position + 1, text="📌", font=("Arial", 24),
#                     fill="white", tags="sticky_note_shadow")
#                 self.canvas.create_text(
#                     x_position, y_position, text="📌", font=("Arial", 24),
#                     fill=emoji_fill, tags="sticky_note")
#     def on_canvas_click(self, event):
#         """Add a sticky note at the clicked position on the canvas."""
#         if not self.pdf_document or not self.sticky_note_mode:
#             return       
#         if self.canvas_click_mode == "sticky_note":
#             self.handle_sticky_note_click(event)
#         elif self.canvas_click_mode == "add_text":
#             self.on_canvas_click_for_text(event)
#         x = self.canvas.canvasx(event.x)
#         y = self.canvas.canvasy(event.y)
#         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
#             return  # Clicked outside the PDF page area
#         note_text = self.ask_for_note_text(x, y)
#         if not note_text:
#             return  # No text entered
#         x_scaled = x / self.zoom_factor
#         y_scaled = y / self.zoom_factor
#         self.sticky_notes[(self.current_page, x_scaled, y_scaled)] = note_text
#         self.change_history.append(("sticky_note", self.current_page, x_scaled, y_scaled, note_text))
#         self.canvas.create_text(x, y, text="📌", font=("Arial", 24))
#         self.sticky_note_mode = False
#     def ask_for_font_settings(self):
#         """Prompt the user to select font size and font style with a modern input box and dropdown."""
#         dialog = tk.Toplevel(self.root)
#         dialog.title("Font Settings")
#         dialog.geometry("250x200")
#         dialog.configure(bg="#f9f9f9")
#         dialog.resizable(False, False)
#         font_size_var = tk.StringVar(value="")  # Default font size
#         font_style_var = tk.StringVar(value="Arial")  # Default font style        # Font size input
#         size_label = tk.Label(dialog, text="Font Size:", font=("Arial", 12), bg="#f9f9f9")
#         size_label.pack(pady=(10, 0))
#         size_entry = tk.Entry(dialog, textvariable=font_size_var, font=("Arial", 12), width=20, relief="solid")
#         size_entry.pack(pady=5)
#         style_label = tk.Label(dialog, text="Font Style:", font=("Arial", 12), bg="#f9f9f9")
#         style_label.pack(pady=(10, 0))
#         font_styles = ["Times-Roman","Times-Bold","Times-Italic","Helvetica","Helvetica-Oblique", "Courier","Courier-BoldOblique"]
#         style_dropdown = ttk.Combobox(dialog, textvariable=font_style_var, values=font_styles, state="readonly", font=("Arial", 12))
#         style_dropdown.pack(pady=5)
#         style_dropdown.current(0)  # Default to the first font style
#         def on_ok_click():
#             try:
#                 font_size = int(font_size_var.get())
#                 if font_size < 6 or font_size > 72:
#                     raise ValueError
#                 dialog.destroy()
#             except ValueError:
#                 messagebox.showerror("Invalid Input", "Font size must be a number between 6 and 72.")
#                 return
#             if not font_style_var.get().strip():
#                 messagebox.showerror("Invalid Input", "Font style cannot be empty.")
#                 return
#         def on_cancel_click():
#             font_size_var.set("0")  # Indicate cancellation
#             dialog.destroy()
#         buttons_frame = tk.Frame(dialog, bg="#f9f9f9")
#         buttons_frame.pack(side=tk.BOTTOM, pady=10)
#         tk.Button(buttons_frame, text="OK", command=on_ok_click, width=10, bg="#4CAF50", fg="white").pack(side=tk.LEFT, padx=5)
#         tk.Button(buttons_frame, text="Cancel", command=on_cancel_click, width=10, bg="#F44336", fg="white").pack(side=tk.LEFT, padx=5)
#         dialog.grab_set()
#         dialog.wait_window()
#         if font_size_var.get() == "0":
#             return None, None  # User canceled
#         return int(font_size_var.get()), font_style_var.get().strip()
#     def add_text_to_pdf(self):
#         """Activate adding text to the PDF. Deactivates automatically after one use."""
#         if not self.pdf_document:
#             messagebox.showerror("Error", "No PDF loaded.")
#             return
#         messagebox.showinfo("Info", "Click on the PDF canvas to place the text.")
#         self.canvas_click_mode = "add_text"
#         self.canvas.bind("<Button-1>", self.on_canvas_click_for_text)
#     def on_canvas_click_for_text(self, event):
#         if not self.pdf_document:
#             return
#         x = self.canvas.canvasx(event.x)
#         y = self.canvas.canvasy(event.y)
#         if x < 0 or x > self.page_width or y < 0 or y > self.page_height:
#             messagebox.showwarning("Warning", "Click inside the PDF page bounds.")
#             return
#         note_text = self.ask_for_note_text(x, y)
#         if not note_text:
#             return
#         color = colorchooser.askcolor(title="Choose Text Color")
#         if not color or not color[0]:
#             messagebox.showerror("Error", "No color selected. Please try again.")
#             return
#         rgb_color = color[0]
#         normalized_color = tuple(c / 255 for c in rgb_color)
#         font_size, font_style = self.ask_for_font_settings()
#         if not font_size or not font_style:
#             return
#         wrapped_text = "\n".join(textwrap.wrap(note_text, width=30))
#         temp_font = (font_style, font_size)
#         text_id = self.canvas.create_text(x, y, text=wrapped_text, font=temp_font, fill=color[1], anchor="nw")
#         bbox = self.canvas.bbox(text_id)
#         if bbox:
#             x1, y1, x2, y2 = bbox
#             self.canvas.delete(text_id)  # Remove temporary text
#             padding = 5
#             rect_id = self.canvas.create_rectangle(
#                 x1 - padding, y1 - padding, x2 + padding, y2 + padding,
#                 fill="#FFFFE0",  # Light yellow background
#                 outline="#D3D3D3")  # Gray border
#             text_id = self.canvas.create_text(x, y, text=wrapped_text, font=temp_font, fill=color[1], anchor="nw")
#             x_scaled = x / self.zoom_factor
#             y_scaled = y / self.zoom_factor
#             page = self.pdf_document[self.current_page]
#             text_rect = fitz.Rect(x_scaled, y_scaled, x_scaled + (x2 - x1), y_scaled + (y2 - y1))
#             page.insert_textbox(text_rect, wrapped_text, fontsize=font_size, fontname=font_style, color=normalized_color)
#             self.change_history.append(("add_text", self.current_page, rect_id, text_id))
#         self.canvas.unbind("<Button-1>")
#     def ask_for_note_text(self, x, y):
#         """Prompt the user to enter text."""
#         dialog = tk.Toplevel(self.root)
#         dialog.title("Enter Text")
#         dialog.geometry("400x250")
#         dialog.configure(bg="#f9f9f9")  # Light background color
#         dialog.resizable(False, False)
#         label = tk.Label(dialog, text="Enter your text:", font=("Arial", 14, "bold"), bg="#f9f9f9")
#         label.pack(pady=(15, 10))
#         text_box = tk.Text(dialog, wrap=tk.WORD, height=6, width=40, font=("Arial", 12), relief="solid")
#         text_box.pack(padx=15, pady=5, fill=tk.X)
#         text_box.focus_set()
#         note_text_var = tk.StringVar()
#         def on_ok_click():
#             note_text = text_box.get("1.0", tk.END).strip()
#             if note_text:
#                 note_text_var.set(note_text)
#                 dialog.destroy()
#             else:
#                 messagebox.showwarning("Empty Text", "You must enter some text.")
#         def on_cancel_click():
#             dialog.destroy()
#             self.sticky_note_mode = False
#             self.canvas.unbind("<Button-1>")
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
#         create_rounded_button(buttons_frame, "Cancel", bg_color="#F44336", fg_color="white", command=on_cancel_click)
#         dialog.grab_set()
#         dialog.wait_window()
#         return note_text_var.get() or None
#     def undo_change(self):
#         """Undo the last change made to the PDF."""
#         if not self.change_history:
#             print("No actions to undo.")
#             return
#         last_action = self.change_history.pop()
#         action_type = last_action[0]
#         if action_type == "sticky_note":
#             _, page, x_scaled, y_scaled, _ = last_action
#             if (page, x_scaled, y_scaled) in self.sticky_notes:
#                 del self.sticky_notes[(page, x_scaled, y_scaled)]
#                 self.render_page(self.current_page)
#         elif action_type == "add_text":
#             _, page, rect_id, text_id = last_action
#             self.canvas.delete(rect_id)
#             self.canvas.delete(text_id)
#             page_obj = self.pdf_document[page]
#             annots = page_obj.annots()
#             if annots:
#                 for annot in annots:
#                     page_obj.delete_annot(annot)
#                     break  # Exit after deleting one matching annotation
#             self.render_page(self.current_page)
#         elif action_type == "highlight":
#             _, page, annot_id = last_action
#             page_obj = self.pdf_document[page]
#             annot = page_obj.load_annot(annot_id)
#             if annot:
#                 page_obj.delete_annot(annot)
#                 self.render_page(self.current_page)
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
#             return  # No valid starting point
#         end_x = self.canvas.canvasx(event.x) / self.zoom_factor
#         end_y = self.canvas.canvasy(event.y) / self.zoom_factor
#         start_x = self.start_x / self.zoom_factor
#         start_y = self.start_y / self.zoom_factor
#         rect = fitz.Rect(min(start_x, end_x), min(start_y, end_y), max(start_x, end_x), max(start_y, end_y))
#         page = self.pdf_document[self.current_page]
#         try:
#             annot = page.add_highlight_annot(rect)
#             annot.update()  # Ensure annotation is saved to the document
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
#         wrapped_text = textwrap.fill(text, width=50)
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

# if __name__ == "__main__":
#     root = tk.Tk()
#     app = StickyNotesPDFApp(root)
#     root.mainloop()





















