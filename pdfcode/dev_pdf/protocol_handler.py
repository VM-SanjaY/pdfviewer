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
            # If running as compiled executable
            app_path = Path(sys.executable)
            if self.os_type == "darwin":
                # Return the .app bundle path instead of the binary
                return str(app_path.parent.parent.parent)
            return str(app_path)
        else:
            # If running from source
            return os.path.abspath(sys.argv[0])

    def is_admin(self):
        """Check if the program has admin privileges"""
        try:
            if self.os_type == "windows":
                return ctypes.windll.shell32.IsUserAnAdmin()
            elif self.os_type in ["darwin", "linux"]:
                return os.geteuid() == 0
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
                    None, "runas", sys.executable, " ".join(sys.argv), None, 1
                )
            elif self.os_type in ["darwin", "linux"]:
                if self.os_type == "darwin":
                    cmd = ["osascript", "-e", f'do shell script "{" ".join(sys.argv)}" with administrator privileges']
                else:  # linux
                    if os.path.exists("/usr/bin/pkexec"):
                        cmd = ["pkexec"] + sys.argv
                    elif os.path.exists("/usr/bin/sudo"):
                        cmd = ["sudo"] + sys.argv
                    else:
                        return False
                subprocess.run(cmd)
            return True
        except Exception as e:
            print(f"Failed to elevate privileges: {e}")
            return False

    def register(self):
        """Register protocol handler and verify registration"""
        try:
            print(f"\nAttempting registration for {self.protocol} protocol on {self.os_type}")
            print(f"Application path: {self.app_path}")
            
            # First check if already registered
            if self.verify_registration():
                print("Protocol is already registered correctly")
                return True, "Protocol handler is already registered"

            # If not registered, proceed with registration
            if self.os_type == "windows":
                if not self.is_admin() and not self.elevate_privileges():
                    return False, "Administrator privileges required for Windows registration"
                success = self._register_windows()
            elif self.os_type == "darwin":
                success = self._register_macos()
            elif self.os_type == "linux":
                success = self._register_linux()
            else:
                return False, f"Unsupported operating system: {self.os_type}"

            # Verify after registration
            if success:
                is_verified = self.verify_registration()
                if is_verified:
                    print("Registration and verification successful")
                    return True, "Protocol handler registered successfully"
                else:
                    print("Registration succeeded but verification failed")
                    return False, "Registration verification failed"
            
            print("Registration failed in OS-specific handler")
            return False, "Registration failed"
            
        except Exception as e:
            print(f"Registration error: {str(e)}")
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
            print(f"Windows registration error: {e}")
            return False

    def _register_macos(self):
        """macOS protocol registration using Launch Services"""
        try:
            print("\nStarting macOS registration...")
            
            # Get the .app bundle path
            app_bundle = Path(self.app_path)
            if not str(app_bundle).endswith('.app'):
                print("Warning: Application is not packaged as a proper .app bundle")
                return False
            
            # Register with Launch Services
            lsregister_path = "/System/Library/Frameworks/CoreServices.framework/Versions/A/Frameworks/LaunchServices.framework/Versions/A/Support/lsregister"
            
            print(f"Registering app bundle: {app_bundle}")
            subprocess.run([lsregister_path, "-f", str(app_bundle)], check=True)
            
            # Force update Launch Services database
            subprocess.run([
                "defaults", "write", 
                "com.apple.LaunchServices/com.apple.launchservices.secure",
                "LSHandlers",
                "-array-add",
                f'{{"LSHandlerURLScheme":"{self.protocol}","LSHandlerRoleAll":"com.idmspdf"}}'
            ], check=True)
            
            return True
        except Exception as e:
            print(f"macOS registration error: {e}")
            return False

    def _register_linux(self):
        """Linux protocol registration using desktop entry"""
        try:
            # Create application directory
            app_dir = Path("~/.local/share/applications").expanduser()
            app_dir.mkdir(parents=True, exist_ok=True)
            
            # Create desktop entry
            desktop_entry = self._get_linux_desktop_entry()
            entry_path = app_dir / f"{self.protocol}-handler.desktop"
            
            entry_path.write_text(desktop_entry)
            entry_path.chmod(0o755)  # Make executable
            
            # Register protocol handler
            subprocess.run([
                "xdg-mime", "default",
                f"{self.protocol}-handler.desktop",
                f"x-scheme-handler/{self.protocol}"
            ], check=True)
            
            # Update desktop database
            subprocess.run(["update-desktop-database", str(app_dir)], check=True)
            
            return True
        except Exception as e:
            print(f"Linux registration error: {e}")
            return False

    def verify_registration(self):
        """Verify if the protocol handler is properly registered"""
        try:
            print(f"\nVerifying {self.protocol} protocol registration on {self.os_type}")
            
            if self.os_type == "windows":
                result = self._verify_windows()
            elif self.os_type == "darwin":
                result = self._verify_macos()
                if not result:
                    print("Checking macOS Launch Services registration...")
                    # Additional macOS-specific checks
                    try:
                        result = subprocess.run(
                            ["lsregister", "-dump"],
                            capture_output=True,
                            text=True
                        )
                        print(f"Launch Services registration status:")
                        print(f"Protocol found in registry: {self.protocol in result.stdout}")
                    except Exception as e:
                        print(f"Failed to check Launch Services: {e}")
            elif self.os_type == "linux":
                result = self._verify_linux()
            else:
                result = False
            
            print(f"Verification result: {'Success' if result else 'Failed'}")
            print(f"Protocol: {self.protocol}")
            print(f"App Path: {self.app_path}")
            return result
            
        except Exception as e:
            print(f"Verification error: {e}")
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

    def _verify_macos(self):
        """Verify macOS protocol registration"""
        try:
            print("\nPerforming macOS verification:")
            
            # Check plist file
            plist_path = Path("~/Library/Preferences/com.idmspdf.plist").expanduser()
            print(f"Checking plist at: {plist_path}")
            print(f"Plist exists: {plist_path.exists()}")
            
            if not plist_path.exists():
                print("Plist file not found")
                return False
            
            # Check plist content
            try:
                result = subprocess.run(
                    ["plutil", "-p", str(plist_path)],
                    capture_output=True,
                    text=True,
                    check=True
                )
                print(f"Plist content check:")
                print(result.stdout)
                
                if self.protocol not in result.stdout:
                    print(f"Protocol {self.protocol} not found in plist")
                    return False
                    
            except subprocess.CalledProcessError as e:
                print(f"Error reading plist: {e}")
                return False
            
            # Check Launch Services registration
            lsregister_path = "/System/Library/Frameworks/CoreServices.framework/Versions/A/Frameworks/LaunchServices.framework/Versions/A/Support/lsregister"
            try:
                ls_check = subprocess.run(
                    [lsregister_path, "-dump"],
                    capture_output=True,
                    text=True
                )
                print("\nLaunch Services registration:")
                print(f"Protocol handler found: {self.protocol in ls_check.stdout}")
                
                # Check URL scheme registration
                defaults_check = subprocess.run(
                    ["defaults", "read", "com.apple.LaunchServices/com.apple.launchservices.secure"],
                    capture_output=True,
                    text=True
                )
                print("\nURL scheme registration:")
                print(f"Protocol scheme found: {self.protocol in defaults_check.stdout}")
                
            except Exception as e:
                print(f"Launch Services check failed: {e}")
            
            return True
            
        except Exception as e:
            print(f"Verification failed on macOS: {e}")
            return False

    def _verify_linux(self):
        """Verify Linux protocol registration"""
        try:
            entry_path = Path(f"~/.local/share/applications/{self.protocol}-handler.desktop").expanduser()
            if not entry_path.exists():
                return False
            
            result = subprocess.run(
                ["xdg-mime", "query", "default", f"x-scheme-handler/{self.protocol}"],
                capture_output=True, text=True, check=True
            )
            return f"{self.protocol}-handler.desktop" in result.stdout
        except Exception:
            return False

    def _get_macos_plist_content(self):
        """Generate macOS plist content"""
        return f"""<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>CFBundleIdentifier</key>
    <string>com.idmspdf</string>
    <key>CFBundleName</key>
    <string>IDMS PDF Editor</string>
    <key>CFBundleVersion</key>
    <string>1.0</string>
    <key>CFBundleURLTypes</key>
    <array>
        <dict>
            <key>CFBundleURLName</key>
            <string>{self.protocol}</string>
            <key>CFBundleURLSchemes</key>
            <array>
                <string>{self.protocol}</string>
            </array>
        </dict>
    </array>
</dict>
</plist>"""

    def _get_linux_desktop_entry(self):
        """Generate Linux desktop entry content"""
        return f"""[Desktop Entry]
Name=IDMS PDF Editor
Exec={self.app_path} %u
Type=Application
Terminal=false
Categories=Utility;
MimeType=x-scheme-handler/{self.protocol};
"""

    @staticmethod
    def handle_protocol_url(url):
        """Handle incoming protocol URLs"""
        try:
            from urllib.parse import unquote, quote
            
            print(f"\nDebug URL processing:")
            print(f"Original URL: {url}")
            
            # Remove protocol prefix
            if url.startswith(('idmspdf://', 'idmspdf:')):
                url = url.replace('idmspdf://', '').replace('idmspdf:', '')
                print(f"After protocol removal: {url}")
            
            # Remove extra forward slashes
            while url.startswith('//'):
                url = url[1:]
            print(f"After slash cleanup: {url}")
                
            # First decode
            url = unquote(url)
            print(f"After first decode: {url}")
            
            # Second decode (safe for already decoded URLs)
            url = unquote(url)
            print(f"After second decode: {url}")
            
            # Remove trailing slash if present
            url = url.rstrip('/')
            print(f"After removing trailing slash: {url}")
            
            # Ensure proper protocol for web URLs
            if not url.startswith(('http://', 'https://')):
                url = 'https://' + url
                print(f"After adding https: {url}")
            
            # Re-encode spaces and special characters in the path portion
            parts = url.split('//')
            if len(parts) > 1:
                domain = parts[0] + '//' + parts[1].split('/')[0]
                path = '/'.join(parts[1].split('/')[1:])
                if path:
                    # Encode only the path portion, preserving the domain
                    encoded_path = quote(path, safe='/')
                    url = f"{url}"
                    print(f"After path encoding: {url}")
            
            print(f"Final processed URL: {url}")
            return url
            
        except Exception as e:
            print(f"Error processing URL: {e}")
            print(f"Problematic URL: {url}")
            return url
