import Laiu.Syntax

namespace Laiu.Directives

open Syntax

/-- The dialogue fixes one of the three ways of addressing the listener. -/
inductive Addressee where
  | one | group | polite
  deriving DecidableEq, Repr

def Addressee.person : Addressee → Person
  | .one => .listener
  | .group => .youPlural
  | .polite => .polite

def readAddressee (word : String) : Option Addressee :=
  match readPerson word with
  | some .listener => some .one
  | some .youPlural => some .group
  | some .polite => some .polite
  | _ => none

def renderShort (clause : Phrase) : List String := "мо" :: (render clause).tail

def renderExplicit (clause : Phrase) : List String := clause.person.word :: renderShort clause

def parse (active : Option Addressee) : List String → Option Phrase
  | "мо" :: body => do
    let address ← active
    Syntax.parse (address.person.word :: body)
  | subject :: "мо" :: body => Syntax.parse (subject :: body)
  | _ => none

private theorem render_head_tail (clause : Phrase) :
    clause.person.word :: (render clause).tail = render clause := by
  cases clause
  rfl

private theorem person_is_not_marker (person : Person) : person.word ≠ "мо" := by
  cases person <;> decide

theorem parse_explicit (active : Option Addressee) (clause : Phrase) :
    parse active (renderExplicit clause) = some clause := by
  simp [renderExplicit, renderShort, parse, person_is_not_marker, render_head_tail, parse_render]

theorem parse_short (address : Addressee) (clause : Phrase) (samePerson : address.person = clause.person) :
    parse (some address) (renderShort clause) = some clause := by
  simp [renderShort, parse, samePerson, render_head_tail, parse_render]

theorem short_requires_addressee (body : List String) : parse none ("мо" :: body) = none := rfl

def compact (active : Option Addressee) (clause : Phrase) : List String :=
  match active with
  | none => renderExplicit clause
  | some address =>
    if address.person = clause.person then renderShort clause else renderExplicit clause

theorem compact_preserves_clause (active : Option Addressee) (clause : Phrase) :
    parse active (compact active clause) = some clause := by
  cases active with
  | none => simp [compact, parse_explicit]
  | some address =>
    by_cases h : address.person = clause.person
    · simp [compact, h, parse_short]
    · simp [compact, h, parse_explicit]

theorem matching_addressee_saves_one (address : Addressee) (clause : Phrase)
    (samePerson : address.person = clause.person) :
    (compact (some address) clause).length + 1 = (renderExplicit clause).length := by
  simp [compact, samePerson, renderExplicit]

theorem different_subject_stays_explicit (address : Addressee) (clause : Phrase)
    (different : address.person ≠ clause.person) :
    compact (some address) clause = renderExplicit clause := by
  simp [compact, different]

private theorem render_parts {clause : Phrase} {subject : String} {body : List String}
    (written : render clause = subject :: body) :
    clause.person.word = subject ∧ (render clause).tail = body :=
  List.cons.inj ((render_head_tail clause).trans written)

theorem parsed_surface {active : Option Addressee} {written : List String} {clause : Phrase}
    (read : parse active written = some clause) :
    written = renderExplicit clause ∨
      ∃ address, active = some address ∧ address.person = clause.person ∧ written = renderShort clause := by
  unfold parse at read
  split at read
  · rename_i body
    cases active with
    | none => contradiction
    | some address =>
      change Syntax.parse (address.person.word :: body) = some clause at read
      obtain ⟨subject, tail⟩ := render_parts (render_parse read)
      have samePerson := congrArg readPerson subject
      rw [readPerson_word, readPerson_word] at samePerson
      exact Or.inr ⟨address, rfl, (Option.some.inj samePerson).symm, by simp [renderShort, tail]⟩
  · obtain ⟨subject, tail⟩ := render_parts (render_parse read)
    exact Or.inl (by simp [renderExplicit, renderShort, subject, tail])
  · contradiction

theorem compact_minimal {active : Option Addressee} {written : List String} {clause : Phrase}
    (read : parse active written = some clause) : (compact active clause).length ≤ written.length := by
  rcases parsed_surface read with equal | ⟨address, known, samePerson, equal⟩
  · subst written
    cases active with
    | none => simp [compact]
    | some address =>
      by_cases h : address.person = clause.person <;> simp [compact, h, renderExplicit]
  · subst active written
    simp [compact, samePerson]

example : parse (some .one) ["мо", "ли", "ки"] =
    some ⟨.listener, true, .neutral, .go, .implicit, false, none⟩ := by decide
example : parse (some .one) ["ииа", "мо", "ки"] =
    some ⟨.inclusive, false, .neutral, .go, .implicit, false, none⟩ := by decide
example : parse (some .group) ["мо", "ки"] =
    some ⟨.youPlural, false, .neutral, .go, .implicit, false, none⟩ := by decide

end Laiu.Directives
