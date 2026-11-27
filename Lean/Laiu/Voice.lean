import Laiu.Syntax
import Laiu.Deixis

namespace Laiu.Voice

def passiveMarker : String := "сэ"

def agentMarker : String := "рэн"

def patientMarker : String := "ас"

inductive Verb where
  | see | build | love
  deriving DecidableEq, Repr

def Verb.word : Verb → String
  | .see => "пи"
  | .build => "ко"
  | .love => "мил"

private def readVerb : String → Option Verb
  | "пи" => some .see
  | "ко" => some .build
  | "мил" => some .love
  | _ => none

structure Predicate where
  verb : Verb
  negative : Bool
  phase : Syntax.Phase
  time : Syntax.Time
  result : Bool
  spatial : Option (Syntax.Relation × Syntax.Place)
  deriving DecidableEq, Repr

structure Reading where
  agent : Option String
  patient : String
  predicate : Predicate
  deriving DecidableEq, Repr

inductive Clause where
  | active (agent patient : String) (predicate : Predicate)
  | passive (patient : String) (agent : Option String) (predicate : Predicate)
  deriving DecidableEq, Repr

def Clause.reading : Clause → Reading
  | .active agent patient predicate => ⟨some agent, patient, predicate⟩
  | .passive patient agent predicate => ⟨agent, patient, predicate⟩

def Clause.toPassive : Clause → Clause
  | .active agent patient predicate => .passive patient (some agent) predicate
  | clause => clause

theorem passivizing_preserves_roles_and_predicate (clause : Clause) :
    clause.toPassive.reading = clause.reading := by
  cases clause <;> rfl

private def isParticipant (word : String) : Bool :=
  (Syntax.readPerson word).isSome ||
    (Deixis.read word).any (fun (_, role) => role != .place) ||
    Morphology.nouns.contains word ||
    Morphology.nouns.any (fun noun => noun ++ "ам" == word)

private def predicateWords (predicate : Predicate) (passive : Bool) : List String :=
  (if predicate.negative then ["ли"] else []) ++
  (if passive then [passiveMarker] else []) ++
  predicate.phase.words ++ [predicate.verb.word] ++ predicate.time.words ++
  (if predicate.result then ["ка"] else [])

def render (clause : Clause) (markPatient : Bool := false) : List String :=
  match clause with
  | .active agent patient predicate => agent :: predicateWords predicate false ++
    (if markPatient then [patientMarker] else []) ++ [patient] ++ Syntax.spatialWords predicate.spatial
  | .passive patient agent predicate => patient :: predicateWords predicate true ++
    (agent.toList.flatMap fun word => [agentMarker, word]) ++ Syntax.spatialWords predicate.spatial

/-- An object or tense contrast covered by the audit of merged sounds. -/
def needsPatientMarker : Clause → Bool
  | .active _ patient predicate =>
    match (Phonology.withoutVowelLength patient).toList with
    | [sound] =>
      let before := (predicateWords predicate false).getLast?.bind (·.toList.getLast?)
      let after := (Syntax.spatialWords predicate.spatial).head?.bind (·.toList.head?)
      let betweenVowels := match before, after with
        | some left, some right =>
          Phonology.isVowel left && Phonology.isVowel right && left != right &&
            (sound == left || sound == right)
        | _, _ => false
      let tenseCanMerge := !predicate.result && predicate.verb == .love &&
        match predicate.time with
        | .implicit => sound == 'о' || sound == 'у' ||
            (sound == 'э' && after.any (fun right => Phonology.isVowel right && right != 'э'))
        | .past => sound == 'о' || after == some sound
        | .future => sound == 'у' || after == some sound
        | .present => false
      Phonology.isVowel sound && (betweenVowels || tenseCanMerge)
    | _ => false
  | .passive .. => false

def renderConversational (clause : Clause) : List String :=
  render clause (needsPatientMarker clause)

theorem patient_marker_adds_one_word (agent patient : String) (predicate : Predicate) :
    (render (.active agent patient predicate) true).length =
      (render (.active agent patient predicate) false).length + 1 := by
  simp [render]
  omega

private def readSecond (passive : Bool) (body : List String) : Option (Option String × List String) :=
  let (named, rest) := Syntax.takeFlag (if passive then agentMarker else patientMarker) body
  match passive, named, rest with
  | true, false, _ => some (none, rest)
  | true, true, second :: tail | false, _, second :: tail =>
    if isParticipant second then some (some second, tail) else none
  | _, _, _ => none

/-- Single-word participants with a finite set of verbs and one optional spatial phrase. -/
def parse : List String → Option Clause
  | first :: body => do
    if !isParticipant first then none else
      let (negative, body) := Syntax.takeFlag "ли" body
      let (passive, body) := Syntax.takeFlag passiveMarker body
      let (phase, body) := Syntax.takePhase body
      let verbWord :: body := body | none
      let verb ← readVerb verbWord
      let (time, body) := Syntax.takeTime body
      let (result, body) := Syntax.takeFlag "ка" body
      let (second, tail) ← readSecond passive body
      let spatial ← Syntax.readSpatial tail
      let predicate : Predicate := ⟨verb, negative, phase, time, result, spatial⟩
      if passive then some (.passive first second predicate)
      else second.map (fun patient => .active first patient predicate)
  | [] => none

theorem passive_starts_after_any_person_without_a_vowel_junction (person : Syntax.Person) :
    Phonology.hasSameVowelBoundary person.word passiveMarker = false := by
  cases person <;> decide

theorem passive_marker_is_an_open_syllable :
    Phonology.syllableCount passiveMarker = 1 ∧ Phonology.closedSyllableCount passiveMarker = 0 := by
  decide

example : (parse ["там", "ли", "сэ", "тиа", "ко", "ло"]).map Clause.reading =
    some ⟨none, "там", ⟨.build, true, .starts, .past, false, none⟩⟩ := by decide
example : (parse ["а", "сэ", "пи", "рэн", "и", "эн", "там"]).map Clause.reading =
    some ⟨some "и", "а", ⟨.see, false, .neutral, .implicit, false, some (.source, .house)⟩⟩ := by decide
example : (parse ["а", "сэ", "пи", "эн", "там"]).map Clause.reading =
    some ⟨none, "а", ⟨.see, false, .neutral, .implicit, false, some (.source, .house)⟩⟩ := by decide
example : parse ["а", "сэ", "пи", "и"] = none := by decide
example : parse ["у", "пи", "ас", "э", "эн", "там"] = parse ["у", "пи", "э", "эн", "там"] := by decide
example : (parse ["у", "пи", "лу", "у", "ин", "тив"]).map renderConversational =
    some ["у", "пи", "лу", "ас", "у", "ин", "тив"] := by decide
example : (parse ["у", "пи", "лу", "и", "ин", "тив"]).map renderConversational =
    some ["у", "пи", "лу", "ас", "и", "ин", "тив"] := by decide
example : (parse ["у", "пи", "и", "ин", "тив"]).map renderConversational =
    some ["у", "пи", "и", "ин", "тив"] := by decide
example : (parse ["а", "мил", "э", "ин", "там"]).map renderConversational =
    some ["а", "мил", "ас", "э", "ин", "там"] := by decide

end Laiu.Voice
