import os
import sys
import time
import ctypes
import platform
import json
import requests
from pathlib import Path
from datetime import datetime
from urllib.parse import unquote, parse_qs

if platform.system().lower() != "windows":
    raise EnvironmentError("This ProtocolHandler version is intended for Windows only.")

import winreg


class ProtocolHandler:
    def __init__(self, protocol_name="idmspdf", app_path=None):
        print("url is recieved from frontend ======= ",datetime.now())
        self.start_time = time.time()
        self.protocol = protocol_name
        self.app_path = app_path or self._get_app_path()

    def _get_app_path(self):
        if getattr(sys, 'frozen', False):
            return str(Path(sys.executable))
        return os.path.abspath(sys.argv[0])

    def is_admin(self):
        try:
            return ctypes.windll.shell32.IsUserAnAdmin()
        except Exception:
            return False

    def elevate_privileges(self):
        if self.is_admin():
            return True

        try:
            params = " ".join([f'"{arg}"' for arg in sys.argv])
            ctypes.windll.shell32.ShellExecuteW(None, "runas", sys.executable, params, None, 1)
            return False
        except Exception as e:
            print(f"Privilege elevation failed: {e}")
            return False

    def register(self):
        if not self.is_admin():
            if not self.elevate_privileges():
                return False, "Administrator privileges required"

        if self.verify_registration():
            return True, "Protocol already registered"

        try:
            with winreg.CreateKey(winreg.HKEY_CLASSES_ROOT, self.protocol) as key:
                winreg.SetValue(key, "", winreg.REG_SZ, f"URL:{self.protocol} Protocol")
                winreg.SetValueEx(key, "URL Protocol", 0, winreg.REG_SZ, "")
                with winreg.CreateKey(key, r"shell\open\command") as cmd_key:
                    command = f'"{self.app_path}" "%1"'
                    winreg.SetValue(cmd_key, "", winreg.REG_SZ, command)
            return True, "Protocol handler registered successfully"
        except Exception as e:
            return False, f"Windows registration error: {e}"

    def verify_registration(self):
        try:
            with winreg.OpenKey(winreg.HKEY_CLASSES_ROOT, self.protocol) as key:
                value = winreg.QueryValue(key, "")
                with winreg.OpenKey(key, r"shell\open\command") as cmd_key:
                    command = winreg.QueryValue(cmd_key, "")
                    expected_cmd = f'"{self.app_path}" "%1"'
                    return (value == f"URL:{self.protocol} Protocol" and command == expected_cmd)
        except FileNotFoundError:
            return False

    def handle_protocol_url(self, url):
        """Clean and decode incoming protocol URL and log the usage."""
        try:
            print(f"Processing URL: {url}")

            url = url.replace('idmspdf://', '').replace('idmspdf:', '').lstrip('/')
            url = unquote(unquote(url)).rstrip('/')

            if not url.startswith(('http://', 'https://')):
                url = 'https://' + url

            pdf_url, query_part = self.split_url(url)
            query = query_part.lstrip("?")
            params = parse_qs(query)

            account_name = params.get("account_name", [""])[0]
            display_name = params.get("display_name", [""])[0]
            file_date_time = params.get("date_time", [""])[0]
            timer_id = params.get("timer_id", [""])[0]
            protocol_timer_url = pdf_url.split('.com/')[0] +".com/api/v1/pdf-timer/" + timer_id

            end_time = time.time()
            total_time = end_time - self.start_time
            protocol_execution = f"Complete time taken for protocol to execute: {total_time:.4f} seconds"
            actiondone = "Protocol handler"
            action_description = f"{display_name} {file_date_time} loaded. {protocol_execution}"
            print("Protocol timer ........................",protocol_timer_url)
            self.protocol_timer(protocol_timer_url)
            self.loggerIssue_function(
                url="https://idms-dev.blockchaincloudapps.com/api/v1/insert-pdf-viewer-audit",  # Replace with your real endpoint
                accountname=account_name,
                actiondone=actiondone,
                actiondescription=action_description
            )

            return url
        except Exception as e:
            print(f"URL handling error: {e}")
            return url

    def split_url(self, url):
        pdf_index = url.lower().find('.pdf')
        if pdf_index == -1:
            return url, ''
        part1 = url[:pdf_index + 4]
        part2 = url[pdf_index + 4:]
        return part1.strip(), part2.strip()
    
    def protocol_timer(self, url):
        try:
            now = datetime.now().isoformat(timespec='milliseconds')
            payload = json.dumps({
            "protocal_hit_time": now
            })
            headers = {
            'Content-Type': 'application/json',
            }
            response = requests.request("PATCH", url, headers=headers, data=payload)
            print("Logger response:", response.status_code, response.text)
        except Exception as e:
            print(f"Protocol timer error: {e}")

    def loggerIssue_function(self, url, accountname, actiondone, actiondescription):
        try:
            payload = json.dumps({
                "user": accountname,
                "viewer_version": "1.8.2",
                "action": actiondone,
                "description": actiondescription
            })
            headers = {'Content-Type': 'application/json'}
            response = requests.post(url, headers=headers, data=payload)
            print("Logger response:", response.status_code, response.text)
        except Exception as e:
            print(f"Logging failed: {e}")