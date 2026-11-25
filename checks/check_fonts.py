"""Check how HarfBuzz actually renders both Laiu fonts."""

from itertools import groupby, product
from pathlib import Path

import uharfbuzz as hb


ROOT = Path(__file__).resolve().parents[1]
ALPHABET = "аэиоупбтквсмнрл"


def shape(font, text):
    buffer = hb.Buffer()
    buffer.add_str(text)
    buffer.guess_segment_properties()
    hb.shape(font, buffer)
    return tuple(item.codepoint for item in buffer.glyph_infos)


def check_font(path):
    font = hb.Font(hb.Face(path.read_bytes()))
    signatures = {}
    for letter, count in product(ALPHABET, range(1, 4)):
        text = letter * count
        glyphs = shape(font, text)
        if len(glyphs) != 1 or glyphs[0] == 0:
            raise ValueError(f"{path.name}: «{text}» должно отображаться одним знаком")
        if glyphs in signatures.values():
            raise ValueError(f"{path.name}: «{text}» использует уже занятый знак")
        signatures[text] = glyphs

    for text in (*ALPHABET.upper(), "ии", "иИ", "ИиИ", "киив", "киурри", "и ии", "куа а"):
        expected = tuple(
            glyph
            for char, run in groupby(text.lower())
            for glyph in (shape(font, char) if char.isspace() else signatures["".join(run)])
        )
        if shape(font, text) != expected:
            raise ValueError(f"{path.name}: неожиданное начертание «{text}»")
    print(f"{path.name}: {len(signatures)} разных знаков, регистр и границы слов проверены.")


if __name__ == "__main__":
    for name in ("Laiu.ttf", "LaiuHand.ttf"):
        check_font(ROOT / "Письмо" / name)
