"""Build a Markdown summary from completed Laiu listening trials."""

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
from statistics import median_high, median_low
import wave

from check_docs import LISTENING_STUDIES, listening_fingerprint, load_listening_material, read_trial_script


def check_voice(path, trial):
    phrases = list(trial["audio"])
    if path.suffix == ".js":
        _, target, _ = LISTENING_STUDIES[trial.get("study")]
        bundle = read_trial_script(path, target)
        if (bundle["source"] != "human" or bundle["pairs"] != trial["pairs"]
                or bundle["preference"] != trial["preference"] or bundle.get("study") != trial.get("study")):
            raise ValueError("нужен набор WAV из той же пробы")
    else:
        bundle = json.loads(path.read_text(encoding="utf-8-sig"))
        if type(bundle["version"]) is not int or bundle["version"] != 1 or bundle["phrases"] != phrases:
            raise ValueError("нужен набор с фразами из той же пробы")
    digest = listening_fingerprint(bundle["audio"], phrases)
    if digest != bundle["audioSet"] or digest == trial["audioSet"]:
        raise ValueError("записи не совпадают с идентификатором или дублируют демонстрационный набор")
    return digest


def index_entries(entries, pairs, phrase_key):
    expected = {(pair["id"], phrase) for pair in pairs for phrase in pair["phrases"]}
    indexed = {}
    for entry in entries:
        key = (entry["pair"], entry[phrase_key])
        if key not in expected or key in indexed:
            raise ValueError(f"неизвестный или повторный вариант «{key[1]}» в паре {key[0]}")
        indexed[key] = entry
    if indexed.keys() != expected:
        raise ValueError("в файле есть пропущенные фразы")
    return indexed


def in_range(value, low, high=None):
    return type(value) is int and value >= low and (high is None or value <= high)


def check_result(result, trial):
    version, source, digest = (result[key] for key in ("version", "source", "audioSet"))
    if type(version) is not int or version not in (3, 4):
        raise ValueError("неподдерживаемый формат ответов")
    if result.get("study") != trial.get("study"):
        raise ValueError("ответы относятся к другой пробе. Проверьте выбор --time или --love")
    if source not in ("human", "synthetic") or not re.fullmatch("[0-9a-f]{64}", digest):
        raise ValueError("неизвестный источник записи или неверный идентификатор набора")
    if (source == "synthetic") != (digest == trial["audioSet"]):
        raise ValueError("источник не совпадает с набором текущей демонстрационной пробы")
    if version == 4 and not re.fullmatch("[0-9a-f]{32}", result["attempt"]):
        raise ValueError("неверный идентификатор прохождения")

    answers = index_entries(result["answers"], trial["pairs"], "played")
    for pair in trial["pairs"]:
        for phrase in pair["phrases"]:
            answer = answers[pair["id"], phrase]
            if answer["answer"] not in pair["phrases"] or not in_range(answer["plays"], 1):
                raise ValueError(f"неверный ответ в паре {pair['id']}")
    ratings = index_entries(result["preference"], trial["preference"], "phrase")
    for rating in ratings.values():
        if not all(in_range(rating[metric], 1, 5) for metric in ("softness", "rating")):
            raise ValueError(f"оценка вне шкалы от 1 до 5 в паре {rating['pair']}")
    return answers, ratings


def collect_results(paths, trial):
    groups = defaultdict(list)
    attempts = {}
    copies = 0
    for path in paths:
        try:
            result = json.loads(path.read_text(encoding="utf-8-sig"))
            answers, ratings = check_result(result, trial)
            payload = json.dumps(result, sort_keys=True, ensure_ascii=False).encode("utf-8")
            fingerprint = hashlib.sha256(payload).hexdigest()
            version = result["version"]
            identity = (version, result["attempt"] if version == 4 else fingerprint)
            previous = attempts.get(identity)
            if previous is not None:
                if previous != fingerprint:
                    raise ValueError("один идентификатор прохождения содержит разные ответы")
                copies += 1
                continue
            attempts[identity] = fingerprint
            groups[result["source"], result["audioSet"]].append((answers, ratings))
        except (OSError, ValueError, TypeError, KeyError) as error:
            raise ValueError(f"{path.name}: {error}") from error
    return groups, copies


def recognition_rows(trial, predictions, runs):
    for pair in trial["pairs"]:
        code = pair["id"]
        first, second = pair["phrases"]
        left = [answers[code, first] for answers, _ in runs]
        right = [answers[code, second] for answers, _ in runs]
        first_errors = sum(answer["answer"] == second for answer in left)
        second_errors = sum(answer["answer"] == first for answer in right)
        entries = left + right
        first_pass = sum(answer["plays"] == 1 and answer["answer"] == answer["played"] for answer in entries)
        repeated = sum(answer["plays"] > 1 for answer in entries)
        yield (f"| `{first}` | `{second}` | {predictions[code]} | {first_errors}/{len(runs)} | "
               f"{second_errors}/{len(runs)} | {first_pass}/{len(entries)} | {repeated}/{len(entries)} |")


def rating_rows(trial, runs):
    for pair in trial["preference"]:
        code = pair["id"]
        first, second = pair["phrases"]
        summaries = []
        for metric in ("softness", "rating"):
            left = [ratings[code, first][metric] for _, ratings in runs]
            right = [ratings[code, second][metric] for _, ratings in runs]
            deltas = [a - b for a, b in zip(left, right, strict=True)]
            higher = sum(delta > 0 for delta in deltas)
            lower = sum(delta < 0 for delta in deltas)
            tied = len(deltas) - higher - lower
            summaries.append(f"{middle_score(left)} / {middle_score(right)} · {higher} / {tied} / {lower}")
        yield f"| {pair['title']} | `{first}` | `{second}` | {' | '.join(summaries)} |"


def middle_score(scores):
    low, high = median_low(scores), median_high(scores)
    return str(low) if low == high else f"{low}–{high}"


def render_report(trial, predictions, groups, voices, copies):
    study = trial.get("study")
    title = {"time": "Скоро и недавно", "love": "Люблю и любил"}.get(study, "Звучание Laiu")
    yield f"# {title} · результаты"
    yield ""
    yield "В отчёте посчитаны прохождения. Один слушатель может пройти пробу несколько раз."
    if copies:
        yield f"Повторных копий экспортов пропущено — {copies}."
    for index, ((source, digest), runs) in enumerate(sorted(groups.items()), 1):
        label = "Демонстрация" if source == "synthetic" else "Запись голоса"
        yield ""
        yield f"## {label} · набор {index}"
        yield ""
        yield f"Идентификатор `{digest}`. Прохождений — {len(runs)}."
        if digest in voices:
            yield "Идентификатор сверён с приложенным файлом записей."
        elif source == "human":
            yield "Источник указан в ответах. Файл с записями к отчёту не приложен."
        yield ""
        yield "### Разборчивость"
        yield ""
        if study == "love":
            yield "Модель предполагает слияние одинаковых гласных и согласных."
            yield ""
        yield "| А | Б | Различие в модели | А принято за Б | Б принято за А | Верно с первого раза | С повтором |"
        yield "| --- | --- | --- | ---: | ---: | ---: | ---: |"
        yield from recognition_rows(trial, predictions, runs)
        yield ""
        yield "### Мягкость и приятность"
        yield ""
        yield "Слева от `·` стоят срединные оценки А и Б по шкале от 1 до 5. Справа посчитаны случаи, когда А оценили выше, оценки совпали или Б оценили выше."
        yield ""
        yield "| Пара | А | Б | Мягкость | Приятность |"
        yield "| --- | --- | --- | --- | --- |"
        yield from rating_rows(trial, runs)


def main():
    parser = argparse.ArgumentParser(description="Сводка ответов из пробы Laiu")
    parser.add_argument("results", type=Path, nargs="+", help="экспорты ответов JSON")
    study = parser.add_mutually_exclusive_group()
    study.add_argument("--time", dest="study", action="store_const", const="time", help="проба «Скоро и недавно»")
    study.add_argument("--love", dest="study", action="store_const", const="love", help="проба «Люблю и любил»")
    parser.add_argument("--voice", type=Path, action="append", default=[], help="готовый набор голоса JSON или JS, собранный из WAV")
    parser.add_argument("-o", "--output", type=Path, help="куда сохранить заметку Markdown")
    options = parser.parse_args()
    try:
        trial, predictions = load_listening_material(study=options.study)
        voices = {check_voice(path, trial) for path in options.voice}
        groups, copies = collect_results(options.results, trial)
        if voices - {digest for _, digest in groups}:
            raise ValueError("для одного из приложенных наборов нет ответов")
        report = "\n".join(render_report(trial, predictions, groups, voices, copies))
        if options.output:
            with options.output.open("x", encoding="utf-8") as output:
                output.write(report + "\n")
        else:
            print(report)
    except (OSError, ValueError, TypeError, KeyError, EOFError, wave.Error) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
