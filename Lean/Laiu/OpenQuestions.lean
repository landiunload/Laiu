import Laiu.Directives
import Laiu.Phonology

namespace Laiu.OpenQuestions

open Directives Syntax

def restore (active : Option Addressee) : List String → List String
  | question :: head :: tail =>
    if active == some .one && ["эмбо", "эмкуа", "эмэн"].contains question && (readPerson head).isNone then
      question :: Person.listener.word :: head :: tail
    else question :: head :: tail
  | words => words

theorem restore_requires_singular_addressee (active : Option Addressee) (words : List String)
    (different : active ≠ some .one) : restore active words = words := by
  cases words with
  | nil => rfl
  | cons question rest =>
    cases rest with
    | nil => rfl
    | cons head tail => simp [restore, different]

theorem restore_preserves_explicit_person (active : Option Addressee) (question : String)
    (person : Person) (body : List String) :
    restore active (question :: person.word :: body) = question :: person.word :: body := by
  simp [restore, readPerson_word]

private def junctions (words : List String) : Nat :=
  (Phonology.sharedVowelBoundaries words).length

def compact (active : Option Addressee) (valid : List String → Bool) (words : List String) : List String :=
  let short := words.take 1 ++ words.drop 2
  if valid words = true ∧ restore active short = words ∧ junctions short ≤ junctions words then
    short
  else words

theorem compact_restores_original (active : Option Addressee) (valid : List String → Bool)
    (words : List String) (changed : compact active valid words ≠ words) :
    restore active (compact active valid words) = words := by
  dsimp only [compact] at *
  split
  · rename_i allowed
    exact allowed.2.1
  · rename_i rejected
    exact False.elim (changed (ite_eq_right rejected))

theorem compact_adds_no_junctions (active : Option Addressee) (valid : List String → Bool)
    (words : List String) :
    (Phonology.sharedVowelBoundaries (compact active valid words)).length ≤
      (Phonology.sharedVowelBoundaries words).length := by
  change junctions (compact active valid words) ≤ junctions words
  dsimp only [compact]
  split
  · rename_i allowed
    exact allowed.2.2
  · exact Nat.le_refl _

end Laiu.OpenQuestions
