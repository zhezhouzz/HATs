class color:
   PURPLE = '\033[95m'
   CYAN = '\033[96m'
   DARKCYAN = '\033[36m'
   BLUE = '\033[94m'
   GREEN = '\033[92m'
   YELLOW = '\033[93m'
   RED = '\033[91m'
   BOLD = '\033[1m'
   UNDERLINE = '\033[4m'
   END = '\033[0m'

def bold_text(string):
    return color.BOLD + string + color.END

def underline_text(string):
    return color.UNDERLINE + string + color.END

def purple_text(string):
    return color.PURPLE + string + color.END
