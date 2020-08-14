import importlib
CURRENT_FORMAT = None

def setFormat(format_name):
    mod = importlib.import_module(format_name)
    global CURRENT_FORMAT
    CURRENT_FORMAT = mod
