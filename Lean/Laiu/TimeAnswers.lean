import Laiu.Phonology
import Laiu.Syntax

namespace Laiu.TimeAnswers

open Syntax

def readQuestion : List String → Option Phrase
  | "эмлу" :: body => do
    let clause ← Syntax.parse body
    if clause.person == .listener && !clause.negative then some clause else none
  | _ => none

/-- A self-contained event in the fragment of movement and sky-position answers. -/
private def isEvent (words : List String) : Bool :=
  (Syntax.parse words).isSome ||
    match words with
    | subject :: "ри" :: rest =>
      let (_, complement) := takeTime rest
      ["ар", "ну"].contains subject && (complement == ["боу"] || complement == ["ниу"])
    | _ => false

def recover (active : Option Phrase) (answer : List String) : Option (List String) :=
  if active.isSome && isEvent answer then some ("луа" :: answer) else none

theorem recover_requires_time_question (answer : List String) :
    recover none answer = none := rfl

def compact (active : Option Phrase) (words : List String) : List String :=
  if recover active words.tail = some words then words.tail else words

theorem compact_preserves_event (active : Option Phrase) (words : List String)
    (changed : compact active words ≠ words) :
    recover active (compact active words) = some words := by
  by_cases recovered : recover active words.tail = some words
  · simp [compact, recovered]
  · exact False.elim (changed (by simp [compact, recovered]))

theorem compact_removes_only_connector (active : Option Phrase) (words : List String)
    (changed : compact active words ≠ words) :
    "луа" :: compact active words = words := by
  have recovered := compact_preserves_event active words changed
  simp only [recover] at recovered
  split at recovered <;> simp_all

theorem compact_saves_one_word (active : Option Phrase) (words : List String)
    (changed : compact active words ≠ words) :
    (compact active words).length + 1 = words.length := by
  exact congrArg List.length (compact_removes_only_connector active words changed)

theorem removing_connector_adds_no_junction (event : List String) :
    (Phonology.sharedVowelBoundaries event).length ≤
      (Phonology.sharedVowelBoundaries ("луа" :: event)).length := by
  cases event with
  | nil => decide
  | cons head tail =>
    cases boundary : Phonology.hasSameVowelBoundary "луа" head <;>
      simp [Phonology.sharedVowelBoundaries, boundary]

example : recover (readQuestion ["эмлу", "а", "ки", "лу"]) ["ар", "ри", "лу", "боу"] =
    some ["луа", "ар", "ри", "лу", "боу"] := by decide
example : compact (readQuestion ["эмбо", "а", "ки"]) ["луа", "ар", "ри", "лу", "боу"] =
    ["луа", "ар", "ри", "лу", "боу"] := by decide
example : compact (readQuestion ["эмлу", "а", "ки", "лу"]) ["луа", "тэ", "ар", "ри", "лу", "боу", "эт"] =
    ["луа", "тэ", "ар", "ри", "лу", "боу", "эт"] := by decide

end Laiu.TimeAnswers
