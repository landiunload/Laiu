"""Check links shared by the GitHub README, Obsidian notes, and canvas."""

import json
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
WIKILINK = re.compile(r"\[\[([^\]|]+)(?:\|[^\]]+)?\]\]")
MARKDOWN_LINK = re.compile(r"(?<!\[)\[[^\]\n]+\]\((<[^>]+>|[^()\s]+)\)")
HTML_IMAGE = re.compile(r'<img\b[^>]*\bsrc="([^"]+)"')
HEADING = re.compile(r"^#{1,6}\s+(.+)$", re.MULTILINE)


def headings(path):
    return [item.replace("`", "").strip() for item in HEADING.findall(path.read_text(encoding="utf-8"))]


def github_slug(heading):
    return re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")


def missing_target(source, target, *, wiki=False):
    path, _, fragment = target.partition("#")
    if not wiki:
        if urlsplit(path).scheme or path.startswith("//"):
            return False
        path, fragment = unquote(path), unquote(fragment)
    location = ((ROOT if wiki else source.parent) / path) if path else source
    if wiki and not location.suffix:
        location = location.with_suffix(".md")
    if not location.exists():
        return True
    if not fragment or location.suffix != ".md":
        return False
    titles = headings(location)
    return fragment not in (titles if wiki else map(github_slug, titles))


def check_notes():
    errors = []
    count = 0
    for path in sorted(ROOT.glob("*.md")):
        text = path.read_text(encoding="utf-8")
        for target in WIKILINK.findall(text):
            count += 1
            if missing_target(path, target, wiki=True):
                errors.append(f"{path.name}: [[{target}]]")
        for target in MARKDOWN_LINK.findall(text) + HTML_IMAGE.findall(text):
            count += 1
            if missing_target(path, target.strip("<>")):
                errors.append(f"{path.name}: {target}")
    return count, errors


def check_canvas():
    path = ROOT / "canvas.canvas"
    canvas = json.loads(path.read_text(encoding="utf-8"))
    nodes = {node["id"] for node in canvas["nodes"]}
    errors = []
    if len(nodes) != len(canvas["nodes"]):
        errors.append("canvas.canvas: повторяющийся узел")
    for node in canvas["nodes"]:
        if node["type"] == "file":
            target = node["file"] + node.get("subpath", "")
            if missing_target(path, target, wiki=True):
                errors.append(f"canvas.canvas: {target}")
    for edge in canvas["edges"]:
        if edge["fromNode"] not in nodes or edge["toNode"] not in nodes:
            errors.append(f"canvas.canvas: связь {edge['id']} ведёт к отсутствующему узлу")
    return len(nodes), errors


if __name__ == "__main__":
    link_count, note_errors = check_notes()
    node_count, canvas_errors = check_canvas()
    if errors := note_errors + canvas_errors:
        raise SystemExit("\n".join(errors))
    print(f"Справочник: {link_count} ссылок и {node_count} узлов карты проверены.")
