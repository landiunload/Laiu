import Laiu.Particles
import Laiu.PredicateContext

namespace Laiu.PolarityAnswers

open Particles Syntax

/-- Perspective changes for a reply between two speakers. A group referred to
    solely through an unspecified "we" or "you" needs more context. -/
def replyPerson : Person → Option Person
  | .speaker => some .listener
  | .listener => some .speaker
  | .we | .exclusive | .youPlural | .polite => none
  | person => some person

/-- The questioned movement, expressed from the viewpoint of the person who answers. -/
def readContext (question : List String) : Option Phrase := do
  let utterance ← parseUtterance question
  let _ ← utterance.question
  let person ← replyPerson utterance.clause.person
  return { utterance.clause with person }

theorem read_context_ignores_expectation (clause : Phrase) (question : Question) :
    readContext (renderUtterance ⟨clause, some question⟩) =
      (replyPerson clause.person).map (fun person => { clause with person }) := by
  simp [readContext, parse_utterance_render]
  cases replyPerson clause.person <;> rfl

def short (answer : Answer) : List String := [answer.word]

theorem short_answers_sound_distinct :
    Phonology.withoutVowelLength Answer.confirm.word ≠
      Phonology.withoutVowelLength Answer.deny.word := by decide

theorem short_answer_uses_one_open_syllable (answer : Answer) :
    Phonology.syllableCount answer.word = 1 ∧ Phonology.closedSyllableCount answer.word = 0 := by
  cases answer <;> decide

def readAnswer : List String → Option Answer
  | ["ла"] => some .confirm
  | ["ли"] => some .deny
  | _ => none

def expand (context : Phrase) (answer : Answer) : Phrase :=
  match answer with
  | .confirm => context
  | .deny => { context with negative := !context.negative }

theorem expand_matches_truth (context : Phrase) (answer : Answer) (affirmativeTruth : Bool) :
    (if (expand context answer).negative then !affirmativeTruth else affirmativeTruth) =
      answer.correct (if context.negative then !affirmativeTruth else affirmativeTruth) := by
  rcases context with ⟨person, negative, phase, travel, time, result, spatial⟩
  cases answer <;> cases negative <;> cases affirmativeTruth <;> rfl

def recover (context : Option Phrase) (words : List String) : Option Phrase := do
  let clause ← context
  let answer ← readAnswer words
  pure (expand clause answer)

theorem recover_short (context : Phrase) (answer : Answer) :
    recover (some context) (short answer) = some (expand context answer) := by
  cases answer <;> rfl

theorem recover_requires_context (words : List String) : recover none words = none := rfl

theorem recoverable_answer_has_one_word (context : Option Phrase) {words : List String}
    {clause : Phrase} (accepted : recover context words = some clause) : words.length = 1 := by
  cases context with
  | none => simp [recover] at accepted
  | some context =>
    cases words with
    | nil => simp [recover, readAnswer] at accepted
    | cons word rest =>
      cases rest with
      | nil => rfl
      | cons next tail => simp [recover, readAnswer] at accepted

def compact (context : Option Phrase) (clause : Phrase) : List String :=
  match context with
  | none => render clause
  | some asked =>
    let answer := if asked.negative = clause.negative then Answer.confirm else .deny
    if expand asked answer = clause then short answer else render clause

theorem compact_recovers_clause (context : Option Phrase) (clause : Phrase)
    (shortened : compact context clause ≠ render clause) :
    recover context (compact context clause) = some clause := by
  cases context with
  | none => exact False.elim (shortened rfl)
  | some asked =>
    simp only [compact] at shortened ⊢
    generalize (if asked.negative = clause.negative then Answer.confirm else .deny) = answer at shortened ⊢
    by_cases reconstructed : expand asked answer = clause
    · simp [reconstructed, recover_short]
    · exact False.elim (shortened (by simp [reconstructed]))

theorem compact_expanded (context : Phrase) (answer : Answer) :
    compact (some context) (expand context answer) = short answer := by
  cases answer <;> cases h : context.negative <;> simp [compact, expand, h]

theorem compact_saves_words (context : Option Phrase) (clause : Phrase)
    (shortened : compact context clause ≠ render clause) :
    (compact context clause).length < (render clause).length := by
  rw [recoverable_answer_has_one_word context (compact_recovers_clause context clause shortened)]
  simp only [render, List.length_append, List.length_cons, List.length_nil]
  omega

/-- An overt subject makes the reply independent. A predicate by itself gets
    its subject, and its time if unmarked, from the question. -/
def readReply (context : Option Phrase) (words : List String) : Option Phrase :=
  Syntax.parse words <|> recover context words <|>
    (context.bind (fun asked => PredicateContext.parseBare asked words))

private theorem read_reply_full (context : Option Phrase) (clause : Phrase) :
    readReply context (render clause) = some clause := by
  simp [readReply, parse_render]

def compactReply (context : Option Phrase) (clause : Phrase) : List String :=
  if compact context clause ≠ render clause then compact context clause else
    match context with
    | none => render clause
    | some asked => PredicateContext.choose (readReply context) [] asked clause

theorem read_compactReply (context : Option Phrase) (clause : Phrase) :
    readReply context (compactReply context clause) = some clause := by
  by_cases shortened : compact context clause ≠ render clause
  · rw [compactReply.eq_def, ite_eq_left shortened]
    have recovered := compact_recovers_clause context clause shortened
    have length := recoverable_answer_has_one_word context recovered
    have notFull : Syntax.parse (compact context clause) = none := by
      cases h : Syntax.parse (compact context clause) with
      | none => rfl
      | some parsed =>
        have size := congrArg List.length (Syntax.render_parse h)
        rw [length] at size
        simp only [Syntax.render, List.length_append, List.length_cons, List.length_nil] at size
        omega
    simp [readReply, notFull, recovered]
  · rw [compactReply.eq_def, ite_eq_right shortened]
    cases context with
    | none => exact read_reply_full _ _
    | some asked => exact PredicateContext.read_choose _ _ _ _ (read_reply_full _ _)

theorem compactReply_no_longer (context : Option Phrase) (clause : Phrase) :
    (compactReply context clause).length ≤ (render clause).length := by
  by_cases shortened : compact context clause ≠ render clause
  · rw [compactReply.eq_def, ite_eq_left shortened]
    exact Nat.le_of_lt (compact_saves_words _ _ shortened)
  · rw [compactReply.eq_def, ite_eq_right shortened]
    cases context with
    | none => exact Nat.le_refl _
    | some asked => exact PredicateContext.choose_no_longer _ _ _ _

example : recover (readContext ["а", "ли", "ки", "лам"]) ["ли"] =
    some ⟨.speaker, false, .neutral, .go, .implicit, false, none⟩ := by decide

example : recover (readContext ["а", "ки", "лу"]) ["ла"] = none := by decide

example : compact (readContext ["а", "ки", "лу", "эм"])
    ⟨.speaker, false, .neutral, .go, .past, false, none⟩ = ["и", "ки", "ло"] := by decide

example : readReply (readContext ["а", "ки", "лу", "эм"]) ["ки", "ло"] =
    Syntax.parse ["и", "ки", "ло"] := by decide

example : readReply (readContext ["о", "ки", "лу", "лим"]) ["роки"] =
    Syntax.parse ["о", "роки", "лу"] := by decide

example : readReply (readContext ["а", "ки", "лу", "эм"]) ["ки"] =
    Syntax.parse ["и", "ки", "лу"] := by decide

example : readReply (readContext ["а", "ки", "лу", "эм"]) ["и", "ки"] =
    Syntax.parse ["и", "ки"] := by decide

example : readReply (readContext ["аа", "ки", "лу", "эм"]) ["ки", "ло"] = none := by decide

example : compactReply (readContext ["а", "ки", "лу", "эм"])
    ⟨.woman, false, .neutral, .returnTo, .future, false, none⟩ = ["о", "роки", "лу"] := by decide

example : compactReply (readContext ["а", "ки", "лу", "куа", "тив", "эм"])
    ⟨.speaker, false, .neutral, .go, .future, false, some (.location, .garden)⟩ =
    ["ки", "лу", "ин", "тив"] := by decide

end Laiu.PolarityAnswers
