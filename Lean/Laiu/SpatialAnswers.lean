import Laiu.Syntax

namespace Laiu.SpatialAnswers

open Syntax

/-- The shared part of the affirmative answer, in the respondent's perspective. -/
structure Context where
  lead : List String
  relation : Relation
  deriving DecidableEq, Repr

private def questionRelation : String → Option Relation
  | "эмбо" => some .location
  | "эмкуа" => some .direction
  | "эмэн" => some .source
  | _ => none

/-- This fragment handles ordinary questions addressed to a single listener. -/
def readQuestion : List String → Option Context
  | "эмбо" :: "а" :: "ри" :: time =>
    if time ∈ [[], ["ло"], ["лэ"], ["лу"]] then some ⟨["и", "ри"] ++ time, .location⟩ else none
  | word :: body => do
    let relation ← questionRelation word
    let clause ← Syntax.parse body
    if clause.person = .listener ∧ clause.negative = false ∧ clause.spatial = none then
      pure ⟨render { clause with person := .speaker }, relation⟩
    else none
  | [] => none

def short (context : Context) (place : Place) : List String :=
  spatialWords (some (context.relation, place))

def full (context : Context) (place : Place) : List String := context.lead ++ short context place

def recover (active : Option Context) (answer : List String) : Option (List String) := do
  let context ← active
  let some (relation, place) ← readSpatial answer | none
  if context.relation = relation then some (full context place) else none

theorem recover_short (context : Context) (place : Place) :
    recover (some context) (short context place) = some (full context place) := by
  simp [recover, short, readSpatial_render]

/-- A wrong spatial role cannot be recovered by substituting the role from the question. -/
theorem recover_wrong_role (context : Context) (relation : Relation) (place : Place)
    (wrong : context.relation ≠ relation) :
    recover (some context) (spatialWords (some (relation, place))) = none := by
  simp [recover, readSpatial_render, wrong]

theorem recover_requires_context (answer : List String) : recover none answer = none := rfl

def compact (active : Option Context) (utterance : List String) : List String :=
  match active with
  | none => utterance
  | some context =>
    let candidate := utterance.drop context.lead.length
    if recover active candidate = some utterance then candidate else utterance

/-- A shortening is performed only when the omitted words are recovered exactly. -/
theorem compact_recovers_original (active : Option Context) (utterance : List String)
    (changed : compact active utterance ≠ utterance) :
    recover active (compact active utterance) = some utterance := by
  cases active with
  | none => exact False.elim (changed rfl)
  | some context =>
    by_cases allowed : recover (some context) (utterance.drop context.lead.length) = some utterance
    · simp [compact, allowed]
    · exact False.elim (changed (by simp [compact, allowed]))

theorem compact_never_lengthens (active : Option Context) (utterance : List String) :
    (compact active utterance).length ≤ utterance.length := by
  cases active with
  | none => simp [compact]
  | some context =>
    by_cases allowed : recover (some context) (utterance.drop context.lead.length) = some utterance
    · simp [compact, allowed]
    · simp [compact, allowed]

theorem compact_full (context : Context) (place : Place) :
    compact (some context) (full context place) = short context place := by
  have dropPrefix : (full context place).drop context.lead.length = short context place := by
    simp [full]
  simp [compact, dropPrefix, recover_short]

theorem full_and_short_word_counts (context : Context) (place : Place) :
    (short context place).length = 2 ∧
      (full context place).length = context.lead.length + 2 := by
  simp [full, short, spatialWords]

theorem recover_only_accepts_two_words (context : Context) {answer reconstructed : List String}
    (accepted : recover (some context) answer = some reconstructed) : answer.length = 2 := by
  cases decoded : readSpatial answer with
  | none => simp [recover, decoded] at accepted
  | some spatial =>
    cases spatial with
    | none => simp [recover, decoded] at accepted
    | some pair =>
      obtain ⟨relation, place⟩ := pair
      rw [← readSpatial_rejoin decoded]
      rfl

example : recover (readQuestion ["эмбо", "а", "ри"]) ["ин", "тив"] =
    some ["и", "ри", "ин", "тив"] := by decide
example : recover (readQuestion ["эмкуа", "а", "ки", "лу"]) ["куа", "тив"] =
    some ["и", "ки", "лу", "куа", "тив"] := by decide
example : recover (readQuestion ["эмэн", "а", "ки"]) ["эн", "тив"] =
    some ["и", "ки", "эн", "тив"] := by decide
example : recover (readQuestion ["эмэн", "а", "ки"]) ["ин", "тив"] = none := by decide
example : recover (readQuestion ["эмэн", "а", "ки"]) ["тив"] = none := by decide
example : compact (readQuestion ["эмкуа", "а", "ки", "лу"]) ["и", "ки", "ло", "куа", "тив"] =
    ["и", "ки", "ло", "куа", "тив"] := by decide

end Laiu.SpatialAnswers
