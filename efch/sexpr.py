"""
Lector e impresor de expresiones S para el núcleo EFCH 0.1.

Átomos: símbolos, enteros (decimal, #x hexadecimal, #b binario) y cadenas
entre comillas. Comentarios con «;» hasta fin de línea. Cada nodo conserva
su posición (línea, columna) para los mensajes de error.
"""

from dataclasses import dataclass, field


class SyntaxError_(Exception):
    def __init__(self, msg, pos):
        super().__init__(f"{pos[0]}:{pos[1]}: {msg}" if pos else msg)
        self.pos = pos


@dataclass(frozen=True)
class Sym:
    name: str
    pos: tuple = field(default=None, compare=False)


@dataclass(frozen=True)
class Num:
    value: int
    pos: tuple = field(default=None, compare=False)


@dataclass(frozen=True)
class Str:
    value: str
    pos: tuple = field(default=None, compare=False)


@dataclass(frozen=True)
class SList:
    items: tuple
    pos: tuple = field(default=None, compare=False)

    def head(self):
        return self.items[0].name if self.items and isinstance(self.items[0], Sym) else None


def _tokens(text):
    i, line, col = 0, 1, 1
    n = len(text)
    while i < n:
        c = text[i]
        if c == "\n":
            i, line, col = i + 1, line + 1, 1
        elif c.isspace():
            i, col = i + 1, col + 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c in "()":
            yield c, (line, col)
            i, col = i + 1, col + 1
        elif c == '"':
            j = i + 1
            buf = []
            while j < n and text[j] != '"':
                if text[j] == "\\" and j + 1 < n:
                    j += 1
                buf.append(text[j])
                j += 1
            if j >= n:
                raise SyntaxError_("cadena sin cerrar", (line, col))
            yield Str("".join(buf), (line, col)), (line, col)
            col += j + 1 - i
            i = j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in '();"':
                j += 1
            yield _atom(text[i:j], (line, col)), (line, col)
            col += j - i
            i = j


def _atom(tok, pos):
    try:
        if tok.startswith("#x"):
            return Num(int(tok[2:], 16), pos)
        if tok.startswith("#b"):
            return Num(int(tok[2:], 2), pos)
        if tok.lstrip("-").isdigit():
            return Num(int(tok), pos)
        if tok.count(".") == 1 and tok.replace(".", "", 1).lstrip("-").isdigit():
            return Num(float(tok), pos)  # solo válido en secciones como (budget ...)
    except ValueError:
        raise SyntaxError_(f"número inválido {tok!r}", pos) from None
    return Sym(tok, pos)


def parse(text):
    """Devuelve la lista de expresiones de nivel superior."""
    stack = [[]]
    starts = []
    for tok, pos in _tokens(text):
        if tok == "(":
            stack.append([])
            starts.append(pos)
        elif tok == ")":
            if len(stack) == 1:
                raise SyntaxError_("paréntesis de cierre sin abrir", pos)
            items = stack.pop()
            stack[-1].append(SList(tuple(items), starts.pop()))
        else:
            stack[-1].append(tok)
    if len(stack) != 1:
        missing = len(stack) - 1
        raise SyntaxError_(f"faltan {missing} paréntesis de cierre al final; el más interno sin cerrar "
                           f"se abre aquí", starts[-1])
    return stack[0]


def dumps(node):
    """Impresión canónica en una línea."""
    if isinstance(node, Sym):
        return node.name
    if isinstance(node, Num):
        return str(node.value)
    if isinstance(node, Str):
        return '"' + node.value.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(node, SList):
        return "(" + " ".join(dumps(x) for x in node.items) + ")"
    if isinstance(node, (list, tuple)):
        return "(" + " ".join(dumps(x) for x in node) + ")"
    if isinstance(node, str):
        return node
    if isinstance(node, int):
        return str(node)
    raise TypeError(node)
