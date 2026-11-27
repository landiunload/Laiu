import Laiu.OpenQuestions

namespace Laiu.TransferAnswers

open Syntax

inductive Role where
  | source | recipient
  deriving DecidableEq, Repr

def Role.marker : Role → String
  | .source => "эн"
  | .recipient => "куа"

private def readRole : String → Option Role
  | "эмэн" => some .source
  | "эмкуа" => some .recipient
  | _ => none

inductive Action where
  | take | give
  deriving DecidableEq, Repr

def Action.word : Action → String
  | .take => "ку"
  | .give => "му"

private def readAction : String → Option Action
  | "ку" => some .take
  | "му" => some .give
  | _ => none

inductive Item where
  | water | food
  deriving DecidableEq, Repr

def Item.word : Item → String
  | .water => "ил"
  | .food => "вус"

private def readItem : String → Option Item
  | "ил" => some .water
  | "вус" => some .food
  | _ => none

/-- An affirmative question to one addressee, asking for one participant of a transfer. -/
structure Context where
  role : Role
  action : Action
  phase : Phase
  time : Time
  result : Bool
  item : Item
  deriving DecidableEq, Repr

private def readExplicitQuestion : List String → Option Context
  | interrogative :: "а" :: rest => do
    let role ← readRole interrogative
    let (phase, rest) := takePhase rest
    let action ← rest.head?.bind readAction
    let (time, rest) := takeTime rest.tail
    let (result, rest) := takeFlag "ка" rest
    let [item] := rest | none
    let item ← readItem item
    return ⟨role, action, phase, time, result, item⟩
  | _ => none

def readQuestion (words : List String) (active : Option Directives.Addressee := none) : Option Context :=
  readExplicitQuestion (OpenQuestions.restore active words)

def compactQuestion (active : Option Directives.Addressee) (words : List String) : List String :=
  OpenQuestions.compact active (fun explicit => (readExplicitQuestion explicit).isSome) words

def full (context : Context) (person : Person) : List String :=
  (["и"] ++ context.phase.words ++ [context.action.word] ++ context.time.words ++
    (if context.result then ["ка"] else []) ++ [context.item.word, context.role.marker]) ++ [person.word]

private def readAnswer (role : Role) : List String → Option Person
  | [word] => readPerson word
  | [marker, word] => if marker = role.marker then readPerson word else none
  | _ => none

def recover (active : Option Context) (words : List String) : Option (List String) := do
  let context ← active
  let person ← readAnswer context.role words
  return full context person

theorem recover_short (context : Context) (person : Person) :
    recover (some context) [person.word] = some (full context person) := by
  simp [recover, readAnswer, readPerson_word]

theorem recover_marked (context : Context) (person : Person) :
    recover (some context) [context.role.marker, person.word] = some (full context person) := by
  simp [recover, readAnswer, readPerson_word]

theorem recover_requires_context (words : List String) : recover none words = none := rfl

theorem answer_has_at_least_one_word (context : Context) {words expanded : List String}
    (accepted : recover (some context) words = some expanded) : 1 ≤ words.length := by
  cases words with
  | nil => simp [recover, readAnswer] at accepted
  | cons _ _ => simp

theorem recover_rejects_wrong_role (context : Context) (role : Role) (word : String)
    (different : role ≠ context.role) :
    recover (some context) [role.marker, word] = none := by
  have markers : role.marker ≠ context.role.marker := by
    cases role <;> cases expected : context.role <;> simp_all [Role.marker]
  simp [recover, readAnswer, markers]

def compact (active : Option Context) (utterance : List String) : List String :=
  let candidate := utterance.getLast?.toList
  if recover active candidate = some utterance then candidate else utterance

theorem compact_recovers_original (active : Option Context) (utterance : List String)
    (changed : compact active utterance ≠ utterance) :
    recover active (compact active utterance) = some utterance := by
  by_cases allowed : recover active utterance.getLast?.toList = some utterance
  · simp [compact, allowed]
  · exact False.elim (changed (by simp [compact, allowed]))

theorem compact_full (context : Context) (person : Person) :
    compact (some context) (full context person) = [person.word] := by
  have last : (full context person).getLast? = some person.word := by
    simp only [full, List.getLast?_concat]
  simp [compact, last, recover_short]

theorem short_saves_at_least_four_words (context : Context) (person : Person) :
    (compact (some context) (full context person)).length + 4 ≤ (full context person).length := by
  rw [compact_full]
  simp only [full, List.length_append, List.length_cons, List.length_nil]
  omega

theorem short_has_no_word_junction (person : Person) :
    Phonology.sharedVowelBoundaries [person.word] = [] := rfl

example : recover (readQuestion ["эмкуа", "а", "му", "лу", "ил"]) ["а"] =
    some ["и", "му", "лу", "ил", "куа", "а"] := by decide
example : recover (readQuestion ["эмкуа", "му", "лу", "ил"] (some .one)) ["а"] =
    some ["и", "му", "лу", "ил", "куа", "а"] := by decide
example : compactQuestion (some .group) ["эмкуа", "а", "му", "лу", "ил"] =
    ["эмкуа", "а", "му", "лу", "ил"] := by decide

example : recover (readQuestion ["эмэн", "а", "ку", "ло", "ка", "вус"]) ["эн", "у"] =
    some ["и", "ку", "ло", "ка", "вус", "эн", "у"] := by decide

example : compact (readQuestion ["эмкуа", "а", "му", "лу", "ил"]) ["и", "му", "ло", "ил", "куа", "а"] =
    ["и", "му", "ло", "ил", "куа", "а"] := by decide

example : readQuestion ["эмкуа", "аа", "му", "ил"] = none := by decide
example : readQuestion ["эмкуа", "а", "му", "ил", "эн", "о"] = none := by decide

end Laiu.TransferAnswers
