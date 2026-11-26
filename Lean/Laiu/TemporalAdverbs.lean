import Laiu.Particles

namespace Laiu.TemporalAdverbs

open Particles

inductive Adverb where
  | now | soon | recently | atNight | byDay
  deriving DecidableEq, Repr

def Adverb.word : Adverb → String
  | .now => "ииу"
  | .soon => "луу"
  | .recently => "лоо"
  | .atNight => "нуу"
  | .byDay => "аруу"

private def readAdverb : String → Option Adverb
  | "ииу" => some .now
  | "луу" => some .soon
  | "лоо" => some .recently
  | "нуу" => some .atNight
  | "аруу" => some .byDay
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

/-- Keep the ordinary final position unless moving the adverb removes a vowel junction. -/
def smootherPosition (utterance : TimedUtterance) : Position :=
  if boundaryCount (render utterance .initial) < boundaryCount (render utterance .final) then
    .initial
  else .final

theorem smoother_position_is_minimal (utterance : TimedUtterance) (other : Position) :
    boundaryCount (render utterance (smootherPosition utterance)) ≤ boundaryCount (render utterance other) := by
  cases other <;> unfold smootherPosition <;> split <;> omega

theorem smoother_position_preserves_parse (utterance : TimedUtterance) :
    parse (render utterance (smootherPosition utterance)) = some utterance :=
  parse_render utterance _

theorem positions_use_same_word_count (utterance : TimedUtterance) :
    (render utterance .initial).length = (render utterance .final).length := by
  simp [render, renderUtterance] <;> omega

example : parse ["ииу", "а", "ки", "ииу", "эм"] = none := by decide
example : parse ["а", "ки", "эм", "ииу"] = none := by decide

end Laiu.TemporalAdverbs
