import Laiu.Particles

namespace Laiu.TemporalAdverbs

open Particles

inductive Adverb where
  | now | soon | recently | atNight | byDay | briefly
  deriving DecidableEq, Repr

def Adverb.word : Adverb → String
  | .now => "ииу"
  | .soon => "луу"
  | .recently => "лоо"
  | .atNight => "нуу"
  | .byDay => "аруу"
  | .briefly => "луви"

def Adverb.tense : Adverb → Option Logic.Tense
  | .now => some .present
  | .soon => some .future
  | .recently => some .past
  | .atNight | .byDay | .briefly => none

private def readAdverb : String → Option Adverb
  | "ииу" => some .now
  | "луу" => some .soon
  | "лоо" => some .recently
  | "нуу" => some .atNight
  | "аруу" => some .byDay
  | "луви" => some .briefly
  | _ => none

private theorem read_adverb_word (adverb : Adverb) : readAdverb adverb.word = some adverb := by
  cases adverb <;> rfl

private theorem read_adverb_on_person (person : Syntax.Person) : readAdverb person.word = none := by
  cases person <;> rfl

private theorem read_question_on_adverb (adverb : Adverb) : readQuestion adverb.word = none := by
  cases adverb <;> rfl

inductive Position where
  | initial | final
  deriving DecidableEq, Repr

structure TimedUtterance where
  body : Utterance
  adverb : Adverb
  deriving DecidableEq, Repr

def TimedUtterance.resolvedTime (utterance : TimedUtterance) (fallback : Logic.Tense) : Option Logic.Tense :=
  Logic.resolveTense fallback utterance.body.clause.time.written utterance.adverb.tense

def TimedUtterance.withoutTimeParticle (utterance : TimedUtterance) : TimedUtterance :=
  { utterance with body := { utterance.body with clause := { utterance.body.clause with time := .implicit } } }

/-- A contradictory sentence has no compact form. Preserve the particle whenever the time would change. -/
def compact (utterance : TimedUtterance) (fallback : Logic.Tense) : Option TimedUtterance := do
  let time ← utterance.resolvedTime fallback
  let unmarked := utterance.withoutTimeParticle
  if unmarked.resolvedTime fallback = some time then some unmarked else some utterance

theorem compact_preserves_contents (utterance shortened : TimedUtterance) (fallback : Logic.Tense)
    (accepted : compact utterance fallback = some shortened) :
    shortened.withoutTimeParticle = utterance.withoutTimeParticle ∧
      shortened.resolvedTime fallback = utterance.resolvedTime fallback := by
  obtain ⟨time, resolved, output⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at output
  split at output
  · rename_i unchanged
    obtain rfl := Option.some.inj output
    exact ⟨rfl, unchanged.trans resolved.symm⟩
  · obtain rfl := Option.some.inj output
    exact ⟨rfl, rfl⟩

theorem compact_drops_matching_particle (utterance : TimedUtterance) (fallback fixed : Logic.Tense)
    (written : utterance.body.clause.time.written = some fixed) (adverb : utterance.adverb.tense = some fixed) :
    compact utterance fallback = some utterance.withoutTimeParticle := by
  have full : utterance.resolvedTime fallback = some fixed := by
    simp [TimedUtterance.resolvedTime, written, adverb, Logic.resolveTense]
  have short : utterance.withoutTimeParticle.resolvedTime fallback = some fixed := by
    simp [TimedUtterance.resolvedTime, TimedUtterance.withoutTimeParticle, adverb,
      Syntax.Time.written, Logic.resolveTense]
  simp [compact, full, short]

def render (utterance : TimedUtterance) : Position → List String
  | .initial => utterance.adverb.word :: renderUtterance utterance.body
  | .final => Syntax.render utterance.body.clause ++ [utterance.adverb.word] ++
      utterance.body.question.toList.map Question.word

private def parseEnding (words : List String) : Option TimedUtterance := do
  let question := words.getLast?.bind readQuestion
  let core := if question.isSome then words.dropLast else words
  let adverb ← core.getLast?.bind readAdverb
  let clause ← Syntax.parse core.dropLast
  return ⟨⟨clause, question⟩, adverb⟩

def parse (words : List String) : Option TimedUtterance :=
  match words.head?.bind readAdverb with
  | some adverb => (parseUtterance words.tail).map (fun body => ⟨body, adverb⟩)
  | none => parseEnding words

theorem parse_render (utterance : TimedUtterance) (position : Position) :
    parse (render utterance position) = some utterance := by
  rcases utterance with ⟨⟨clause, question⟩, adverb⟩
  cases position with
  | initial => simp [render, parse, read_adverb_word, parse_utterance_render]
  | final =>
    have start : ((render ⟨⟨clause, question⟩, adverb⟩ .final).head?.bind readAdverb) = none := by
      simp [render, Syntax.render, read_adverb_on_person]
    simp only [parse, start]
    cases question with
    | none =>
      simp [render, parseEnding, read_question_on_adverb, read_adverb_word, Syntax.parse_render]
    | some question =>
      simp [render, parseEnding, List.append_assoc, read_question_word, read_adverb_word, Syntax.parse_render]

def boundaryCount (words : List String) : Nat :=
  (Phonology.sharedVowelBoundaries words).length

def Adverb.prefersFrontWhenTied : Adverb → Bool
  | .soon | .recently => true
  | _ => false

/-- Minimize vowel junctions. At equal cost, distinguish луу and лоо from the tense particles. -/
def smootherPosition (utterance : TimedUtterance) : Position :=
  let first := boundaryCount (render utterance .initial)
  let last := boundaryCount (render utterance .final)
  if first < last ∨ (first = last ∧ utterance.adverb.prefersFrontWhenTied = true) then .initial
  else .final

theorem smoother_position_is_minimal (utterance : TimedUtterance) (other : Position) :
    boundaryCount (render utterance (smootherPosition utterance)) ≤ boundaryCount (render utterance other) := by
  cases other <;> dsimp only [smootherPosition] <;> split <;> omega

theorem equal_boundaries_put_short_range_time_first (utterance : TimedUtterance)
    (shortRange : utterance.adverb.prefersFrontWhenTied = true)
    (equal : boundaryCount (render utterance .initial) = boundaryCount (render utterance .final)) :
    smootherPosition utterance = .initial := by
  simp [smootherPosition, shortRange, equal]

private theorem person_onset (person : Syntax.Person) :
    ∃ sound, person.word.toList.head? = some sound ∧ sound ≠ 'л' := by
  cases person <;> exact ⟨_, rfl, by decide⟩

theorem initial_short_range_time_survives_duration_and_boundary_loss
    (timed : TimedUtterance) (bare : Utterance) (shortRange : timed.adverb.prefersFrontWhenTied = true) :
    Phonology.withoutVowelLength (String.join (render timed .initial)) ≠
      Phonology.withoutVowelLength (String.join (renderUtterance bare)) := by
  intro same
  have front : timed.adverb.word.toList.head? = some 'л' := by
    cases adverb : timed.adverb <;> simp_all [Adverb.prefersFrontWhenTied] <;> decide
  obtain ⟨sound, personal, different⟩ := person_onset bare.clause.person
  have onset := congrArg (fun text : String => text.toList.head?) same
  simp only [Phonology.duration_loss_preserves_onset, render, renderUtterance,
    Syntax.render, List.cons_append, String.join_cons, String.toList_append, List.head?_append] at onset
  simp [front, personal] at onset
  exact different onset.symm

theorem final_short_range_time_survives_with_its_particle
    (timed : TimedUtterance) (shortRange : timed.adverb.prefersFrontWhenTied = true) :
    Phonology.withoutVowelLength (String.join (render timed .final)) ≠
      Phonology.withoutVowelLength (String.join (renderUtterance timed.body)) := by
  have different :
      (timed.adverb.word.toList.filter (!Phonology.isVowel ·)).length ≠
        (("".toList).filter (!Phonology.isVowel ·)).length := by
    cases adverb : timed.adverb <;> simp_all [Adverb.prefersFrontWhenTied] <;> decide
  simpa [render, renderUtterance, String.join_append, String.join_cons, String.append_assoc] using
    Phonology.distinct_consonant_counts_survive_in_context timed.adverb.word ""
      (String.join (Syntax.render timed.body.clause))
      (String.join (timed.body.question.toList.map Question.word)) different

theorem smoother_position_preserves_parse (utterance : TimedUtterance) :
    parse (render utterance (smootherPosition utterance)) = some utterance :=
  parse_render utterance _

theorem positions_use_same_word_count (utterance : TimedUtterance) :
    (render utterance .initial).length = (render utterance .final).length := by
  simp [render, renderUtterance] <;> omega

theorem brief_duration_preserves_tense (body : Utterance) (fallback : Logic.Tense) :
    (TimedUtterance.mk body .briefly).resolvedTime fallback =
      some (body.clause.time.written.getD fallback) := by
  exact Logic.resolved_without_fixed_adverb fallback body.clause.time.written

theorem brief_duration_costs_one_word (body : Utterance) (position : Position) :
    (render ⟨body, .briefly⟩ position).length = (renderUtterance body).length + 1 := by
  cases position <;> simp [render, renderUtterance] <;> omega

theorem brief_duration_differs_from_frequency_in_context (left right : String) :
    Phonology.withoutVowelLength (left ++ Adverb.briefly.word ++ right) ≠
      Phonology.withoutVowelLength (left ++ "вилу" ++ right) :=
  Phonology.distinct_consonants_survive_in_context _ _ _ _ (by decide)

theorem brief_duration_has_two_open_syllables :
    Phonology.syllableCount Adverb.briefly.word = 2 ∧
      Phonology.closedSyllableCount Adverb.briefly.word = 0 := by decide

theorem removing_written_particle_saves_one (utterance : TimedUtterance) (position : Position)
    (written : utterance.body.clause.time ≠ .implicit) :
    (render utterance.withoutTimeParticle position).length + 1 = (render utterance position).length := by
  have words : utterance.body.clause.time.words.length = 1 := by
    cases time : utterance.body.clause.time <;> simp_all [Syntax.Time.words]
  have length : (Syntax.render utterance.body.clause).length =
      (Syntax.render { utterance.body.clause with time := .implicit }).length + 1 := by
    rw [Syntax.render_length, words]
  cases position <;> simp [render, renderUtterance, TimedUtterance.withoutTimeParticle, length] <;> omega

example : parse ["ииу", "а", "ки", "ииу", "эм"] = none := by decide
example : parse ["а", "ки", "эм", "ииу"] = none := by decide
example : (parse ["луу", "и", "ки"]).bind (·.resolvedTime .present) = some .future := by decide
example : (parse ["и", "ки", "ло", "луу"]).bind (·.resolvedTime .present) = none := by decide
example : (parse ["и", "ки", "нуу"]).bind (·.resolvedTime .past) = some .past := by decide
example : (parse ["и", "ки", "луу"]).bind (·.resolvedTime .past) = some .future := by decide
example : parse ["а", "ки", "эм", "луви"] = none := by decide
example : parse ["луви", "а", "ки", "луви", "эм"] = none := by decide
example : (parse ["и", "ки", "ло", "ка", "луви"]).map (·.body.clause.result) = some true := by decide

example : Phonology.withoutVowelLength "акилууэм" = Phonology.withoutVowelLength "акилуэм" := by decide
example : Phonology.withoutVowelLength "акилооэм" = Phonology.withoutVowelLength "акилоэм" := by decide

end Laiu.TemporalAdverbs
