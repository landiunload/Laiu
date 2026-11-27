"""Check how HarfBuzz renders the Laiu fonts."""

from itertools import groupby, product
from pathlib import Path

import uharfbuzz as hb


ROOT = Path(__file__).resolve().parents[1]
ALPHABET = "аэиоупбтквсмнрл"
JOINED_PAIRS = ("ки", "ли", "эм")


def shape(font, text):
    buffer = hb.Buffer()
    buffer.add_str(text)
    buffer.guess_segment_properties()
    hb.shape(font, buffer)
    return tuple(item.codepoint for item in buffer.glyph_infos)


def check_font(path, hand=None):
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

    joined = {}
    if hand is not None:
        for text, glyphs in signatures.items():
            if shape(hand, text) != glyphs:
                raise ValueError(f"{path.name}: базовый знак «{text}» должен совпадать с Laiu Hand")
        for text in JOINED_PAIRS:
            glyphs = shape(font, text)
            if len(glyphs) != 1 or glyphs in [*signatures.values(), *joined.values(), (0,)]:
                raise ValueError(f"{path.name}: «{text}» должно получить отдельную связку")
            if font.get_glyph_h_advance(glyphs[0]) >= sum(
                hand.get_glyph_h_advance(glyph) for glyph in shape(hand, text)
            ):
                raise ValueError(f"{path.name}: связка «{text}» должна быть уже двух знаков")
            joined[text] = glyphs

    examples = (
        *ALPHABET.upper(), "ии", "иИ", "ИиИ", "киив", "киурри", "и ии", "куа а",
        "кки", "ллии", "эМлИ", "кики", "л и", "э,м", "к.и", "кИ эМ",
    )
    for text in examples:
        runs = iter("".join(run) for _, run in groupby(text.lower()))
        first = next(runs, None)
        expected = []
        while first is not None:
            second = next(runs, None)
            pair = first + (second or "")
            if pair in joined:
                expected.extend(joined[pair])
                first = next(runs, None)
            else:
                expected.extend(signatures[first] if first in signatures else shape(font, first))
                first = second
        if shape(font, text) != tuple(expected):
            raise ValueError(f"{path.name}: неожиданное начертание «{text}»")
    print(f"{path.name}: {len(signatures)} базовых форм и {len(joined)} связок, регистр и границы проверены.")
    return font


if __name__ == "__main__":
    directory = ROOT / "Письмо"
    check_font(directory / "Laiu.ttf")
    hand_font = check_font(directory / "LaiuHand.ttf")
    check_font(directory / "LaiuCompact.ttf", hand_font)
