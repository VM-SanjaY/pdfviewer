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