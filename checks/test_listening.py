from copy import deepcopy
import base64
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import TestCase

from check_docs import listening_fingerprint, load_listening_material
from report_listening import check_result, check_voice, collect_results, render_report


class ListeningReportTests(TestCase):
    @classmethod
    def setUpClass(cls):
        cls.trial, cls.predictions = load_listening_material()

    def make_result(self, trial=None):
        trial = self.trial if trial is None else trial
        answers = [
            dict(pair=row["id"], played=phrase, answer=phrase, plays=1)
            for row in trial["pairs"] for phrase in row["phrases"]
        ]
        ratings = [
            dict(pair=row["id"], phrase=phrase, softness=5 - side, rating=3 + side)
            for row in trial["preference"] for side, phrase in enumerate(row["phrases"])
        ]
        result = dict(version=4, attempt="1" * 32, source="synthetic", audioSet=trial["audioSet"],
                      answers=answers, preference=ratings)
        if "study" in trial:
            result["study"] = trial["study"]
        return result

    def test_short_trial_reuses_clips_and_keeps_results_separate(self):
        trial, predictions = load_listening_material(timing=True)
        self.assertEqual(list(predictions.values()), ["теряется", "сохраняется"] * 2)
        self.assertEqual(len(trial["audio"]), 6)
        result = self.make_result(trial)
        answers, ratings = check_result(result, trial)
        self.assertEqual(len(answers), 8)
        self.assertEqual(len(ratings), 4)
        with self.assertRaisesRegex(ValueError, "другой пробе"):
            check_result(result, self.trial)
        with self.assertRaisesRegex(ValueError, "другой пробе"):
            check_result(self.make_result(), trial)

    def test_report_counts_errors_by_direction_and_votes_by_metric(self):
        result = self.make_result()
        result["answers"][0]["answer"] = result["answers"][1]["played"]
        checked = check_result(result, self.trial)
        groups = {("synthetic", self.trial["audioSet"]): [checked]}
        report = "\n".join(render_report(self.trial, self.predictions, groups, set(), 0))
        self.assertIn("| `и тиа ки` | `ии ки` | сохраняется | 1/1 | 0/1 |", report)
        self.assertIn("| 5 / 4 · 1 / 0 / 0 | 3 / 4 · 0 / 0 / 1 |", report)

    def test_rejects_incomplete_repeated_and_invalid_answers(self):
        result = self.make_result()
        for entry, field, value in (
            ("answers", "plays", 0),
            ("answers", "answer", "неизвестная фраза"),
            ("preference", "softness", True),
            ("preference", "rating", 6),
        ):
            with self.subTest(field=field):
                invalid = deepcopy(result)
                invalid[entry][0][field] = value
                with self.assertRaises(ValueError):
                    check_result(invalid, self.trial)
        missing = deepcopy(result)
        missing["answers"].pop()
        with self.assertRaisesRegex(ValueError, "пропущенные"):
            check_result(missing, self.trial)
        result["preference"][0] = result["preference"][1]
        with self.assertRaisesRegex(ValueError, "повторный"):
            check_result(result, self.trial)

    def test_groups_legacy_and_current_exports_without_counting_copies(self):
        demo = self.make_result()
        legacy = self.make_result()
        legacy.update(version=3)
        del legacy["attempt"]
        human = self.make_result()
        human.update(attempt="2" * 32, source="human", audioSet="a" * 64)
        with TemporaryDirectory() as folder:
            paths = [Path(folder) / f"{index}.json" for index in range(4)]
            for path, result in zip(paths, (demo, demo, legacy, human), strict=True):
                path.write_text(json.dumps(result), encoding="utf-8")
            groups, copies = collect_results(paths, self.trial)
            self.assertEqual(copies, 1)
            self.assertEqual(len(groups["synthetic", demo["audioSet"]]), 2)
            self.assertEqual(len(groups["human", human["audioSet"]]), 1)
            human["attempt"] = demo["attempt"]
            paths[-1].write_text(json.dumps(human), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "разные ответы"):
                collect_results(paths, self.trial)

    def test_checks_voice_fingerprint_against_recording_bytes(self):
        audio = self.trial["audio"].copy()
        phrases = list(audio)
        first = phrases[0]
        prefix, encoded = audio[first].split(",", 1)
        clip = bytearray(base64.b64decode(encoded))
        clip[-1] ^= 1
        audio[first] = prefix + "," + base64.b64encode(clip).decode("ascii")
        digest = listening_fingerprint(audio, phrases)
        bundle = dict(version=1, phrases=phrases, audioSet=digest, audio=audio)
        with TemporaryDirectory() as folder:
            path = Path(folder) / "voice.json"
            path.write_text(json.dumps(bundle), encoding="utf-8")
            self.assertEqual(check_voice(path, self.trial), digest)
            bundle["audioSet"] = "b" * 64
            path.write_text(json.dumps(bundle), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "идентификатор"):
                check_voice(path, self.trial)
