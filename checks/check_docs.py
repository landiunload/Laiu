"""Check links and listening material shared by GitHub and Obsidian."""

import base64
import hashlib
import io
import json
import re
import wave
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


def check_listening_material():
    audio_dir = ROOT / "Звучание"
    notes = (ROOT / "Фонология.md").read_text(encoding="utf-8")
    pairs = re.findall(r"^\| `([^`\n]+)` \| `([^`\n]+)` \| (?:сохраняется|теряется) \|$", notes, re.MULTILINE)
    _, _, rating_section = notes.partition("\n### Оценка звучания\n")
    rating_rows = re.findall(
        r"^\| ([a-z]+) \| ([^|\n]+) \| `([^`\n]+)` \| `([^`\n]+)` \|$",
        rating_section.split("\n> [!note]", 1)[0], re.MULTILINE,
    )
    preference = [{"id": code, "title": title, "phrases": [first, second]}
                  for code, title, first, second in rating_rows]
    if not preference or len({item["id"] for item in preference}) != len(preference):
        raise ValueError("У пар оценки должны быть разные коды")
    script = (audio_dir / "practices.js").read_text(encoding="utf-8").strip()
    prefix = "window.laiuListening = "
    if not script.startswith(prefix) or not script.endswith(";"):
        raise ValueError("Немашиночитаемый набор записей practices.js")
    trial = json.loads(script[len(prefix):-1])
    if trial["source"] != "synthetic":
        raise ValueError("Публичная проба должна использовать синтетический набор")
    if [tuple(item["phrases"]) for item in trial["pairs"]] != pairs or trial["preference"] != preference:
        raise ValueError("Фразы пробы расходятся с фонологией")
    phrases = {phrase for pair in pairs for phrase in pair} | {
        phrase for item in preference for phrase in item["phrases"]
    }
    if set(trial["audio"]) != phrases:
        raise ValueError("Набор WAV не соответствует фразам пробы")
    fingerprint = hashlib.sha256()
    for phrase, uri in trial["audio"].items():
        audio_prefix = "data:audio/wav;base64,"
        if not uri.startswith(audio_prefix):
            raise ValueError(f"Фраза «{phrase}» должна содержать локальную WAV-запись")
        decoded = base64.b64decode(uri[len(audio_prefix):], validate=True)
        with wave.open(io.BytesIO(decoded)) as audio:
            if audio.getnframes() <= 0:
                raise ValueError(f"Пустая запись для «{phrase}»")
        fingerprint.update(phrase.encode("utf-8"))
        fingerprint.update(decoded)
    if trial["audioSet"] != fingerprint.hexdigest():
        raise ValueError("Идентификатор набора не совпадает с WAV-записями")
    return len(phrases)


if __name__ == "__main__":
    link_count, note_errors = check_notes()
    node_count, canvas_errors = check_canvas()
    if errors := note_errors + canvas_errors:
        raise SystemExit("\n".join(errors))
    print(f"Справочник: {link_count} ссылок и {node_count} узлов карты проверены.")
    print(f"Проба на слух: {check_listening_material()} WAV-записей совпадают со списком фраз.")
