import Laiu.PredicateContext

namespace Laiu.Coordination

open Logic (Connector)
open Syntax

/-- A nonempty chain of movement clauses linked at one level by the same connector. -/
structure Chain where
  first : Phrase
  rest : List Phrase
  deriving DecidableEq, Repr

def renderFull (connector : Connector) (chain : Chain) : List String :=
  [connector.word].intercalate ((chain.first :: chain.rest).map Syntax.render)

private def parseFull (connector : Connector) (words : List String) : Option Chain := do
  let first :: rest := words.splitOn connector.word | none
  return ⟨← Syntax.parse first, ← rest.mapM Syntax.parse⟩

private def parseRest (previous : Phrase) : List (List String) → Option (List Phrase)
  | [] => some []
  | words :: rest => do
    let clause ← PredicateContext.parseBare previous words
    return clause :: (← parseRest clause rest)

private def parseShared (connector : Connector) : List String → Option Chain
  | subject :: "тэ" :: words => do
    if words.getLast? != some "эт" then none else
      let first :: next :: rest := words.dropLast.splitOn connector.word | none
      let clause ← Syntax.parse (subject :: first)
      return ⟨clause, ← parseRest clause (next :: rest)⟩
  | _ => none

def parse (connector : Connector) (words : List String) : Option Chain :=
  parseFull connector words <|> parseShared connector words

private def renderRest (connector : Connector) (previous : Phrase) : List Phrase → List (List String)
  | [] => []
  | clause :: rest =>
    PredicateContext.choose (PredicateContext.parseBare previous) [connector.word] previous clause ::
      renderRest connector clause rest

def renderShared (connector : Connector) (chain : Chain) : List String :=
  let actions := (Syntax.render chain.first).tail :: renderRest connector chain.first chain.rest
  [chain.first.person.word, "тэ"] ++ [connector.word].intercalate actions ++ ["эт"]

private theorem separator_absent (connector : Connector) (clause : Phrase) :
    connector.word ∉ Syntax.render clause := by
  have person : connector.word ≠ clause.person.word := by cases connector <;> cases clause.person <;> decide
  have travel : connector.word ≠ clause.travel.word := by cases connector <;> cases clause.travel <;> decide
  have time : connector.word ∉ clause.time.words := by cases connector <;> cases clause.time <;> decide
  have phase : connector.word ∉ clause.phase.words := by cases connector <;> cases clause.phase <;> decide
  have spatial : connector.word ∉ Syntax.spatialWords clause.spatial := by
    cases clause.spatial with
    | none => simp [Syntax.spatialWords]
    | some pair =>
      rcases pair with ⟨relation, place⟩
      cases connector <;> cases relation <;> cases place <;> decide
  have notNegative : connector.word ≠ "ли" := by cases connector <;> decide
  have notResult : connector.word ≠ "ка" := by cases connector <;> decide
  cases clause.negative <;> cases clause.result <;> simp [Syntax.render, *]

private theorem parse_full_round_trip (connector : Connector) (chain : Chain) :
    parseFull connector (renderFull connector chain) = some chain := by
  rcases chain with ⟨first, rest⟩
  have noSeparator : ∀ segment ∈ (first :: rest).map Syntax.render, connector.word ∉ segment := by
    intro segment membership
    obtain ⟨clause, _, rfl⟩ := List.mem_map.mp membership
    exact separator_absent connector clause
  have readFullRest (clauses : List Phrase) :
      (clauses.map Syntax.render).mapM Syntax.parse = some clauses := by
    induction clauses with
    | nil => rfl
    | cons clause rest ih => simp [Syntax.parse_render, ih]
  unfold parseFull renderFull
  rw [List.splitOn_intercalate connector.word noSeparator (by simp)]
  simp [Syntax.parse_render, readFullRest]

theorem parse_renderFull (connector : Connector) (chain : Chain) :
    parse connector (renderFull connector chain) = some chain := by
  simp [parse, parse_full_round_trip]

private def preferred (connector : Connector) (chain : Chain) : Prop :=
  let full := renderFull connector chain
  let short := renderShared connector chain
  let fullVowels := (Phonology.sharedVowelBoundaries full).length
  let fullConsonants := (Phonology.sharedConsonantBoundaries full).length
  let shortVowels := (Phonology.sharedVowelBoundaries short).length
  let shortConsonants := (Phonology.sharedConsonantBoundaries short).length
  parse connector short = some chain ∧ short.length ≤ full.length ∧
    shortVowels ≤ fullVowels ∧ shortConsonants ≤ fullConsonants ∧
    (short.length < full.length ∨ shortVowels < fullVowels ∨ shortConsonants < fullConsonants)

private instance (connector : Connector) (chain : Chain) : Decidable (preferred connector chain) := by
  unfold preferred
  infer_instance

def compact (connector : Connector) (chain : Chain) : List String :=
  if preferred connector chain then renderShared connector chain else renderFull connector chain

theorem parse_compact (connector : Connector) (chain : Chain) :
    parse connector (compact connector chain) = some chain := by
  unfold compact
  split
  · exact (show preferred _ _ from ‹_›).1
  · exact parse_renderFull _ _

theorem compact_no_longer (connector : Connector) (chain : Chain) :
    (compact connector chain).length ≤ (renderFull connector chain).length := by
  unfold compact
  split
  · exact (show preferred _ _ from ‹_›).2.1
  · exact Nat.le_refl _

theorem compact_preserves_truth (connector : Connector) (truth : Phrase → Bool) (chain : Chain) :
    (parse connector (compact connector chain)).map
      (fun decoded => connector.eval ((decoded.first :: decoded.rest).map truth)) =
    some (connector.eval ((chain.first :: chain.rest).map truth)) := by
  rw [parse_compact]
  rfl

example : parse .all ["а", "тэ", "ки", "лу", "на", "роки", "эт"] =
    parse .all ["а", "ки", "лу", "на", "а", "роки", "лу"] := by decide
example : parse .all ["и", "тэ", "ки", "ло", "на", "роки", "лу", "на", "ру", "эт"] =
    parse .all ["и", "ки", "ло", "на", "и", "роки", "лу", "на", "и", "ру", "лу"] := by decide
example : parse .any ["а", "тэ", "ки", "лу", "эу", "о", "роки", "эт"] = none := by decide
example : parse .one ["а", "тэ", "ки", "лу", "эла", "роки", "на", "ру", "эт"] = none := by decide
example : parse .all ["а", "тэ", "ки", "лу", "на", "роки"] = none := by decide
example : parse .all ["а", "ки", "лу", "на", "роки"] = none := by decide
example : parse .all ["а", "тэ", "ки", "лу", "эт"] = none := by decide
example : Phonology.withoutSoundLength "акилунаароки" = Phonology.withoutSoundLength "акилунароки" := by decide

end Laiu.Coordination
