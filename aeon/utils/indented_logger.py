import os


class IndentedLogger:
    indents: list[str]
    file = ""

    def __init__(self, indents=[], file: str = "logs/default.log"):
        self.indents = indents
        self.file = file
        dir = os.path.dirname(file)
        if not os.path.exists(dir):
            os.makedirs(dir)
        os.remove(file) if os.path.exists(file) else None

    def indent(self, i="  "):
        self.indents = self.indents + [i]
        return self

    def dedent(self):
        if self.indents:
            self.indents = self.indents[:-1]
        return self

    def write(self, message: str):
        with open(self.file, "a", encoding="utf-8") as f:
            f.write("".join(self.indents) + message + "\n")
        return self
