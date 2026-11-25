import Laiu.Logic
import Laiu.Phonology
import Laiu.Syntax

namespace Laiu.Particles

inductive Answer where
  | confirm | deny
  deriving DecidableEq, Repr

def Answer.word : Answer → String
  | .confirm => "ла"
  | .deny => "ли"

def Answer.correct (answer : Answer) (statement : Bool) : Bool :=
  match answer with
  | .confirm => statement
  | .deny => !statement

inductive Question where
  | neutral | biased (expected : Answer)
  deriving DecidableEq, Repr

def Question.word : Question → String
  | .neutral => "эм"
  | .biased answer => answer.word ++ "м"

def readQuestion : String → Option Question
  | "эм" => some .neutral
  | "лам" => some (.biased .confirm)
  | "лим" => some (.biased .deny)
  | _ => none

theorem read_question_word (question : Question) : readQuestion question.word = some question := by
  cases question with
  | neutral => rfl
  | biased answer => cases answer <;> rfl

theorem question_word_read {word : String} {question : Question}
    (read : readQuestion word = some question) : question.word = word := by
  unfold readQuestion at read
  split at read <;> cases read <;> rfl

def Question.expected : Question → Option Answer
  | .neutral => none
  | .biased answer => some answer

/-- A correct response agrees with the proposition's truth, even when it differs from the expectation. -/
def Question.check (question : Question) (answer : Answer) (statement : Bool) : Bool × Option Bool :=
  (answer.correct statement, question.expected.map (fun expected => decide (answer = expected)))

theorem expectation_does_not_change_answer (question : Question) (answer : Answer) (statement : Bool) :
    (question.check answer statement).1 = answer.correct statement := rfl

example : (Question.biased .confirm).check .deny false = (true, some false) := by decide
example : (Question.biased .confirm).check .confirm (!false) = (true, some true) := by decide

structure Utterance where
  clause : Syntax.Phrase
  question : Option Question
  deriving DecidableEq, Repr

def renderUtterance (utterance : Utterance) : List String :=
  Syntax.render utterance.clause ++ (utterance.question.toList.map Question.word)

private def readUtterance (tokens : List String) : Option Utterance :=
  let question := tokens.getLast?.bind readQuestion
  let body := if question.isSome then tokens.dropLast else tokens
  (Syntax.parse body).map (fun clause => ⟨clause, question⟩)

private theorem question_is_not_clause_word (clause : Syntax.Phrase) (question : Question) :
    question.word ∉ Syntax.render clause := by
  have person : question.word ≠ clause.person.word := by
    cases question with
    | neutral => cases clause.person <;> decide
    | biased answer => cases answer <;> cases clause.person <;> decide
  have phase : question.word ∉ clause.phase.words := by
    cases question with
    | neutral => cases clause.phase <;> decide
    | biased answer => cases answer <;> cases clause.phase <;> decide
  have travel : question.word ≠ clause.travel.word := by
    cases question with
    | neutral => cases clause.travel <;> decide
    | biased answer => cases answer <;> cases clause.travel <;> decide
  have time : question.word ∉ clause.time.words := by
    cases question with
    | neutral => cases clause.time <;> decide
    | biased answer => cases answer <;> cases clause.time <;> decide
  have spatial : question.word ∉ Syntax.spatialWords clause.spatial := by
    cases clause.spatial with
    | none => simp [Syntax.spatialWords]
    | some pair =>
      obtain ⟨relation, place⟩ := pair
      cases question with
      | neutral => cases relation <;> cases place <;> decide
      | biased answer => cases answer <;> cases relation <;> cases place <;> decide
  have li : question.word ≠ "ли" := by
    cases question with
    | neutral => decide
    | biased answer => cases answer <;> decide
  have ka : question.word ≠ "ка" := by
    cases question with
    | neutral => decide
    | biased answer => cases answer <;> decide
  cases clause.negative <;> cases clause.result <;>
    simp [Syntax.render, *, List.mem_append]

private theorem read_utterance_render (utterance : Utterance) :
    readUtterance (renderUtterance utterance) = some utterance := by
  rcases utterance with ⟨clause, question⟩
  cases question with
  | none =>
    have notQuestion : (Syntax.render clause).getLast?.bind readQuestion = none := by
      cases h : (Syntax.render clause).getLast? with
      | none => rfl
      | some word =>
        cases read : readQuestion word with
        | none => simp [read]
        | some question =>
          have inside := List.mem_of_getLast? h
          rw [← question_word_read read] at inside
          exact False.elim (question_is_not_clause_word clause question inside)
    simp [readUtterance, renderUtterance, notQuestion, Syntax.parse_render]
  | some question =>
    change readUtterance (Syntax.render clause ++ [question.word]) = _
    simp [readUtterance, read_question_word, Syntax.parse_render]

def parseUtterance (tokens : List String) : Option Utterance := do
  let utterance ← readUtterance tokens
  if renderUtterance utterance = tokens then some utterance else none

theorem parse_utterance_render (utterance : Utterance) :
    parseUtterance (renderUtterance utterance) = some utterance := by
  simp [parseUtterance, read_utterance_render]

theorem render_utterance_parse {tokens : List String} {utterance : Utterance}
    (accepted : parseUtterance tokens = some utterance) : renderUtterance utterance = tokens := by
  obtain ⟨decoded, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted <;> simp_all

def compactUtterance (utterance : Utterance) : Utterance :=
  { utterance with clause := Syntax.compact utterance.clause }

theorem compact_utterance_minimal (utterance : Utterance) {tokens : List String} {alternative : Utterance}
    (accepted : parseUtterance tokens = some alternative)
    (sameClause : Syntax.sameMeaning utterance.clause alternative.clause)
    (sameQuestion : alternative.question = utterance.question) :
    (renderUtterance (compactUtterance utterance)).length ≤ tokens.length := by
  rw [← render_utterance_parse accepted]
  simp only [renderUtterance, compactUtterance, List.length_append, sameQuestion]
  exact Nat.add_le_add_right (Syntax.compact_minimal _ _ sameClause) _

example : parseUtterance ["а", "ки", "лим"] =
    some ⟨⟨.listener, false, .neutral, .go, .implicit, false, none⟩, some (.biased .deny)⟩ := by decide
example : parseUtterance ["а", "лим", "ки"] = none := by decide
example : parseUtterance ["а", "ки", "эм", "лам"] = none := by decide
example : renderUtterance (compactUtterance
    ⟨⟨.listener, false, .neutral, .go, .present, false, none⟩, some .neutral⟩) =
    ["а", "ки", "эм"] := rfl

inductive Participation where
  | all | each
  deriving DecidableEq, Repr

def Participation.word : Participation → String
  | .all => "ам"
  | .each => "ами"

def readParticipation : List String → Option Participation
  | ["ам"] => some .all
  | ["ами"] => some .each
  | _ => none

def Participation.holds {α : Type _} (people : Logic.Group α) (acts : Logic.Group α → Prop) :
    Participation → Prop
  | .all => Logic.allParticipate people acts
  | .each => Logic.individually people acts

theorem read_participation_word (mode : Participation) : readParticipation [mode.word] = some mode := by
  cases mode <;> rfl

theorem participation_word_read {tokens : List String} {mode : Participation}
    (read : readParticipation tokens = some mode) : tokens = [mode.word] := by
  unfold readParticipation at read
  split at read <;> cases read <;> rfl

theorem each_word_is_minimal {tokens : List String} (read : readParticipation tokens = some .each) :
    tokens.length = 1 := by
  rw [participation_word_read read]
  rfl

theorem each_entails_all {α : Type _} {people : Logic.Group α} {acts : Logic.Group α → Prop}
    (each : Participation.holds people acts .each) : Participation.holds people acts .all :=
  Logic.individually_entails_all_participate each

/-- нэлу denies any occurrence in the relevant interval. -/
def neverDuring (observations : List Bool) : Bool := Logic.noneChosen observations

theorem never_during_iff_no_occurrence (observations : List Bool) :
    neverDuring observations = true ↔ ∀ occurrence ∈ observations, occurrence = false := by
  induction observations with
  | nil => simp [neverDuring, Logic.noneChosen]
  | cons first rest ih =>
    cases first <;> simp_all [neverDuring, Logic.noneChosen]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem new_words_are_distinct_without_vowel_length :
    ["лэ", "лам", "лим", "ами", "нэлу", "тиа"].all (fun word =>
      (Morphology.reservedForms.filter (fun candidate =>
        Phonology.withoutVowelLength candidate == Phonology.withoutVowelLength word)) == [word]) = true := by
  decide

theorem start_does_not_run_into_person (person : Syntax.Person) :
    (Syntax.Phase.starts.words.head?.map (Phonology.hasSameVowelBoundary person.word)) = some false := by
  cases person <;> decide

example : Syntax.parse ["и", "тиа", "ки"] =
    some ⟨.speaker, false, .starts, .go, .implicit, false, none⟩ := by decide

example : Phonology.syllableCount "тиа" = 2 ∧ Phonology.closedSyllableCount "тиа" = 0 := by decide

end Laiu.Particles
