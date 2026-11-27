import Laiu.Phonology
import Laiu.Syntax

namespace Laiu.PredicateContext

open Syntax

/-- An unmarked predicate takes its subject and unmarked time from its anchor. -/
def parseBare (anchor : Phrase) (words : List String) : Option Phrase := do
  let clause ← Syntax.parse (anchor.person.word :: words)
  return if clause.time = .implicit then { clause with time := anchor.time } else clause

private def withoutRepeatedTime (anchor clause : Phrase) : List String :=
  let time := if clause.time = anchor.time then .implicit else clause.time
  (render { clause with time }).tail

private def usable (read : List String → Option Phrase) (preceding : List String) (clause : Phrase)
    (words : List String) : Prop :=
  read words = some clause ∧
  (Phonology.sharedVowelBoundaries (preceding ++ words)).length ≤
    (Phonology.sharedVowelBoundaries (preceding ++ render clause)).length ∧
  (Phonology.sharedConsonantBoundaries (preceding ++ words)).length ≤
    (Phonology.sharedConsonantBoundaries (preceding ++ render clause)).length

private instance (read : List String → Option Phrase) (preceding : List String) (clause : Phrase)
    (words : List String) : Decidable (usable read preceding clause words) := by
  unfold usable
  infer_instance

def choose (read : List String → Option Phrase) (preceding : List String)
    (anchor clause : Phrase) : List String :=
  let shortest := withoutRepeatedTime anchor clause
  if usable read preceding clause shortest then shortest
  else if usable read preceding clause (render clause).tail then (render clause).tail
  else render clause

theorem read_choose (read : List String → Option Phrase) (preceding : List String)
    (anchor clause : Phrase) (full : read (render clause) = some clause) :
    read (choose read preceding anchor clause) = some clause := by
  dsimp only [choose]
  split
  · exact (show usable _ _ _ _ from ‹_›).1
  · split
    · exact (show usable _ _ _ _ from ‹_›).1
    · exact full

theorem choose_no_longer (read : List String → Option Phrase) (preceding : List String)
    (anchor clause : Phrase) : (choose read preceding anchor clause).length ≤ (render clause).length := by
  dsimp only [choose]
  split
  · simp only [withoutRepeatedTime, List.length_tail]
    split
    · rw [Syntax.render_length clause]
      omega
    · exact Nat.sub_le _ _
  · split
    · rw [List.length_tail]
      exact Nat.sub_le _ _
    · exact Nat.le_refl _

end Laiu.PredicateContext
