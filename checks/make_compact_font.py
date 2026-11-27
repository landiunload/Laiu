"""Join three common pairs using contours from Laiu Hand."""

import argparse
from io import BytesIO
from pathlib import Path

from fontTools.otlLib.builder import buildLigatureSubstSubtable, buildLookup
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.ttLib import TTFont


SCRIPT = Path(__file__).resolve().parents[1] / "Письмо"
# Each bridge begins and ends inside one of the existing strokes after scaling.
PAIRS = {
    "ки": ("ki.join", (584, 454), (698, 604), 1060),
    "ли": ("li.join", (576, 530), (698, 604), 1060),
    "эм": ("em.join", (566, 379), (704, 476), 1270),
}


def draw_bridge(pen, start, end):
    x, y = start
    end_x, end_y = end
    middle_x = (x + end_x) / 2
    middle_y = (y + end_y) / 2
    pen.moveTo((x, y + 15))
    pen.qCurveTo((middle_x, y + 15), (middle_x, middle_y + 18))
    pen.qCurveTo((middle_x, end_y + 21), (end_x, end_y + 21))
    pen.lineTo((end_x, end_y - 20))
    pen.qCurveTo((middle_x, end_y - 20), (middle_x, middle_y - 18))
    pen.qCurveTo((middle_x, y - 15), (x, y - 15))
    pen.closePath()


def make_font():
    font = TTFont(SCRIPT / "LaiuHand.ttf", recalcTimestamp=False)
    cmap = font.getBestCmap()
    glyf = font["glyf"]
    pairs = {}
    for letters, (name, start, end, advance) in PAIRS.items():
        first, second = (cmap[ord(letter)] for letter in letters)
        pen = TTGlyphPen(font.getGlyphSet())
        glyf[first].draw(TransformPen(pen, (0.72, 0, 0, 1, 0, 0)), glyf)
        glyf[second].draw(TransformPen(pen, (0.84, 0, 0, 1, 580, 0)), glyf)
        draw_bridge(pen, start, end)
        glyph = pen.glyph()
        glyph.recalcBounds(glyf)
        font["hmtx"].metrics[name] = (advance, glyph.xMin)
        glyf[name] = glyph
        pairs[first, second] = name
    font.setGlyphOrder(font.getGlyphOrder())

    # Keep the original lookup first so a repeat gets its arch before pairs are joined.
    layout = font["GSUB"].table
    index = len(layout.LookupList.Lookup)
    layout.LookupList.Lookup.append(buildLookup([buildLigatureSubstSubtable(pairs)]))
    layout.LookupList.LookupCount += 1
    repeat_feature, = (record.Feature for record in layout.FeatureList.FeatureRecord if record.FeatureTag == "rlig")
    repeat_feature.LookupListIndex.append(index)
    repeat_feature.LookupCount += 1

    names = {1: "Laiu Compact", 3: "LaiuCompact-Regular-1", 4: "Laiu Compact Regular", 6: "LaiuCompact-Regular"}
    for record in font["name"].names:
        if record.nameID in names:
            record.string = names[record.nameID].encode(record.getEncoding())
    return font


def make_preview(font):
    glyphs = font.getGlyphSet()
    cmap = font.getBestCmap()

    def outline(name, x, y):
        pen = SVGPathPen(glyphs)
        glyphs[name].draw(pen)
        return f'<path transform="translate({x} {y}) scale(.092 -.092)" d="{pen.getCommands()}"/>'

    rows = []
    for index, (letters, (name, _, _, _)) in enumerate(PAIRS.items()):
        baseline = 185 + index * 95
        first, second = (cmap[ord(letter)] for letter in letters)
        rows.append(
            f'<rect x="32" y="{baseline - 72}" width="584" height="86" rx="12" fill="#fffaf3"/>\n'
            f'<text x="55" y="{baseline - 19}" font-size="26" font-weight="650">{letters}</text>\n'
            f'<g fill="#302822">{outline(first, 225, baseline - 6)}'
            f'{outline(second, 310, baseline - 6)}</g>\n'
            f'<g fill="#543a4b">{outline(name, 474, baseline - 6)}</g>'
        )
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" width="648" height="411" viewBox="0 0 648 411"'
        ' role="img" aria-labelledby="title description">\n'
        '<title id="title">Три рукописные связки Laiu</title>\n'
        '<desc id="description">Ки, ли и эм. Отдельные знаки слева, соединённые справа.</desc>\n'
        '<rect width="648" height="411" fill="#f5eee3"/>\n'
        '<rect width="648" height="8" fill="#543a4b"/>\n'
        '<g font-family="Segoe UI, Arial, sans-serif" fill="#302822">\n'
        '<text x="32" y="57" font-size="34" font-weight="680">Три связки Laiu</text>\n'
        '<text x="235" y="97" font-size="16" fill="#69564b">Два знака</text>\n'
        '<text x="486" y="97" font-size="16" fill="#69564b">Связка</text>\n'
        + "\n".join(rows)
        + "\n</g>\n</svg>\n"
    ).encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify the generated files")
    check = parser.parse_args().check
    font = make_font()
    compiled = BytesIO()
    font.save(compiled)
    outputs = {"LaiuCompact.ttf": compiled.getvalue(), "Связки.svg": make_preview(font)}
    for name, data in outputs.items():
        path = SCRIPT / name
        if check:
            if not path.is_file() or path.read_bytes() != data:
                raise SystemExit(f"{name}: regenerate with python checks/make_compact_font.py")
        else:
            path.write_bytes(data)


if __name__ == "__main__":
    main()
