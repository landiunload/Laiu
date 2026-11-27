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


def read_trial_script(path):
    script = path.read_text(encoding="utf-8").strip()
    prefix = "window.laiuListening = "
    if not script.startswith(prefix) or not script.endswith(";"):
        raise ValueError("Немашиночитаемый набор записей practices.js")
    return json.loads(script[len(prefix):-1])


def listening_fingerprint(audio, phrases):
    if set(audio) != set(phrases):
        raise ValueError("Набор WAV не соответствует фразам пробы")
    fingerprint = hashlib.sha256()
    audio_prefix = "data:audio/wav;base64,"
    for phrase in phrases:
        uri = audio[phrase]
        if not isinstance(uri, str) or not uri.startswith(audio_prefix):
            raise ValueError(f"Фраза «{phrase}» должна содержать локальную WAV-запись")
        decoded = base64.b64decode(uri[len(audio_prefix):], validate=True)
        with wave.open(io.BytesIO(decoded)) as wav:
            if wav.getnframes() <= 0:
                raise ValueError(f"Пустая запись для «{phrase}»")
            size = wav.getnframes() * wav.getsampwidth() * wav.getnchannels()
            if len(wav.readframes(wav.getnframes())) != size:
                raise ValueError(f"Неполная запись для «{phrase}»")
        fingerprint.update(phrase.encode("utf-8"))
        fingerprint.update(decoded)
    return fingerprint.hexdigest()


def load_listening_material():
    notes = (ROOT / "Фонология.md").read_text(encoding="utf-8")
    rows = re.findall(
        r"^\| `([^`\n]+)` \| `([^`\n]+)` \| (сохраняется|теряется) \|$",
        notes, re.MULTILINE,
    )
    pairs = [{"id": f"{index:02}", "phrases": [first, second]}
             for index, (first, second, _) in enumerate(rows, 1)]
    _, _, rating_section = notes.partition("\n### Оценка звучания\n")
    rating_rows = re.findall(
        r"^\| ([a-z]+) \| ([^|\n]+) \| `([^`\n]+)` \| `([^`\n]+)` \|$",
        rating_section.split("\n> [!note]", 1)[0], re.MULTILINE,
    )
    preference = [{"id": code, "title": title, "phrases": [first, second]}
                  for code, title, first, second in rating_rows]
    if not preference or len({item["id"] for item in preference}) != len(preference):
        raise ValueError("У пар оценки должны быть разные коды")
    trial = read_trial_script(ROOT / "Звучание" / "practices.js")
    if trial["source"] != "synthetic":
        raise ValueError("Публичная проба должна использовать синтетический набор")
    if not pairs or trial["pairs"] != pairs or trial["preference"] != preference:
        raise ValueError("Фразы пробы расходятся с фонологией")
    phrases = list(dict.fromkeys(phrase for row in pairs + preference for phrase in row["phrases"]))
    if list(trial["audio"]) != phrases or trial["audioSet"] != listening_fingerprint(trial["audio"], phrases):
        raise ValueError("Идентификатор набора не совпадает с WAV-записями")
    predictions = {pair["id"]: row[2] for pair, row in zip(pairs, rows, strict=True)}
    return trial, predictions


if __name__ == "__main__":
    link_count, note_errors = check_notes()
    node_count, canvas_errors = check_canvas()
    if errors := note_errors + canvas_errors:
        raise SystemExit("\n".join(errors))
    print(f"Справочник: {link_count} ссылок и {node_count} узлов карты проверены.")
    trial, _ = load_listening_material()
    print(f"Проба на слух: {len(trial['audio'])} WAV-записей совпадают со списком фраз.")
