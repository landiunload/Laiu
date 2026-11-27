import Laiu.Logic

namespace Laiu.Syntax

inductive Person where
  | speaker | listener | man | woman | neutral | we | inclusive | exclusive |
    youPlural | polite | men | women | neutralPlural
  deriving DecidableEq, Repr

def Person.all : List Person := [.speaker, .listener, .man, .woman, .neutral,
  .we, .inclusive, .exclusive, .youPlural, .polite, .men, .women, .neutralPlural]

theorem Person.mem_all (person : Person) : person ∈ Person.all := by cases person <;> decide

def Person.word : Person → String
  | .speaker => "и"
  | .listener => "а"
  | .man => "у"
  | .woman => "о"
  | .neutral => "э"
  | .we => "ии"
  | .inclusive => "ила"
  | .exclusive => "инэ"
  | .youPlural => "аа"
  | .polite => "ааа"
  | .men => "уу"
  | .women => "оо"
  | .neutralPlural => "ээ"

def readPerson : String → Option Person
  | "и" => some .speaker
  | "а" => some .listener
  | "у" => some .man
  | "о" => some .woman
  | "э" => some .neutral
  | "ии" => some .we
  | "ила" => some .inclusive
  | "инэ" => some .exclusive
  | "аа" => some .youPlural
  | "ааа" => some .polite
  | "уу" => some .men
  | "оо" => some .women
  | "ээ" => some .neutralPlural
  | _ => none

theorem readPerson_word (person : Person) : readPerson person.word = some person := by
  cases person <;> rfl

inductive Travel where
  | go | returnTo | move
  deriving DecidableEq, Repr

def Travel.word : Travel → String
  | .go => "ки"
  | .returnTo => "роки"
  | .move => "ру"

inductive Phase where
  | neutral | starts | stops
  deriving DecidableEq, Repr

def Phase.words : Phase → List String
  | .neutral => []
  | .starts => ["тиа"]
  | .stops => ["нэо"]

inductive Time where
  | implicit | past | present | future
  deriving DecidableEq, Repr

def Time.words : Time → List String
  | .implicit => []
  | .past => ["ло"]
  | .present => ["лэ"]
  | .future => ["лу"]

theorem explicit_time_words_use_two_letters {time : Time} (explicit : time ≠ .implicit) :
    ∃ word, time.words = [word] ∧ word.length = 2 := by
  cases time <;> simp_all [Time.words] <;> decide

inductive Place where
  | garden | house | tree
  deriving DecidableEq, Repr

def Place.word : Place → String
  | .garden => "тив"
  | .house => "там"
  | .tree => "ти"

inductive Relation where
  | direction | location | source
  deriving DecidableEq, Repr

def Relation.word : Relation → String
  | .direction => "куа"
  | .location => "ин"
  | .source => "эн"

/-- One optional spatial phrase in a declarative movement clause. -/
structure Phrase where
  person : Person
  negative : Bool
  phase : Phase
  travel : Travel
  time : Time
  result : Bool
  spatial : Option (Relation × Place)
  deriving DecidableEq, Repr

def spatialWords : Option (Relation × Place) → List String
  | none => []
  | some (relation, place) => [relation.word, place.word]

def render (clause : Phrase) : List String :=
  [clause.person.word] ++ (if clause.negative then ["ли"] else []) ++
  clause.phase.words ++ [clause.travel.word] ++ clause.time.words ++
  (if clause.result then ["ка"] else []) ++ spatialWords clause.spatial

def Time.written : Time → Option Logic.Tense
  | .implicit => none
  | .past => some .past
  | .present => some .present
  | .future => some .future

/-- This fragment is a standalone clause, so its first unmarked verb defaults to present. -/
def Time.resolved (time : Time) : Logic.Tense :=
  Logic.inheritedTense .present (.independent time.written)

private def Time.compact : Time → Time
  | .present => .implicit
  | other => other

def compact (clause : Phrase) : Phrase :=
  { clause with time := clause.time.compact }

def sameMeaning (left right : Phrase) : Prop :=
  { left with time := .implicit } = { right with time := .implicit } ∧
    left.time.resolved = right.time.resolved

theorem compact_preserves_meaning (clause : Phrase) : sameMeaning (compact clause) clause := by
  refine ⟨rfl, ?_⟩
  change clause.time.compact.resolved = clause.time.resolved
  cases clause.time <;> rfl

theorem render_length (clause : Phrase) :
    (render clause).length = (render { clause with time := .implicit }).length +
      clause.time.words.length := by
  simp only [render, List.length_append, List.length_cons, List.length_nil, Time.words]
  omega

private theorem compact_time_minimal (left right : Time) (equal : left.resolved = right.resolved) :
    left.compact.words.length ≤ right.words.length := by
  cases left <;> cases right <;>
    simp [Time.resolved, Time.written, Logic.inheritedTense] at equal <;> decide

/-- Among the encodings with this meaning in the movement fragment, compact uses the fewest tokens. -/
theorem compact_minimal (clause alternative : Phrase) (equal : sameMeaning clause alternative) :
    (render (compact clause)).length ≤ (render alternative).length := by
  rw [render_length (compact clause), render_length alternative]
  change (render { clause with time := .implicit }).length + clause.time.compact.words.length ≤ _
  rw [equal.1]
  exact Nat.add_le_add_left (compact_time_minimal _ _ equal.2) _

theorem compact_present_saves_one (clause : Phrase) (present : clause.time = .present) :
    (render (compact clause)).length + 1 = (render clause).length := by
  rw [render_length (compact clause), render_length clause]
  change (render { clause with time := .implicit }).length + clause.time.compact.words.length + 1 = _
  rw [present]
  rfl

example : render (compact ⟨.speaker, false, .neutral, .go, .present, false, none⟩) =
    ["и", "ки"] := rfl

def takeFlag (marker : String) : List String → Bool × List String
  | [] => (false, [])
  | first :: rest => if first == marker then (true, rest) else (false, first :: rest)

def takePhase : List String → Phase × List String
  | "тиа" :: rest => (.starts, rest)
  | "нэо" :: rest => (.stops, rest)
  | rest => (.neutral, rest)

private def takeTravel : List String → Option (Travel × List String)
  | "ки" :: rest => some (.go, rest)
  | "роки" :: rest => some (.returnTo, rest)
  | "ру" :: rest => some (.move, rest)
  | _ => none

def takeTime : List String → Time × List String
  | "ло" :: rest => (.past, rest)
  | "лэ" :: rest => (.present, rest)
  | "лу" :: rest => (.future, rest)
  | rest => (.implicit, rest)

private def readRelation : String → Option Relation
  | "куа" => some .direction
  | "ин" => some .location
  | "эн" => some .source
  | _ => none

private def readPlace : String → Option Place
  | "тив" => some .garden
  | "там" => some .house
  | "ти" => some .tree
  | _ => none

def readSpatial : List String → Option (Option (Relation × Place))
  | [] => some none
  | [relation, place] => do
    let relation ← readRelation relation
    let place ← readPlace place
    return some (relation, place)
  | _ => none

def parse : List String → Option Phrase
  | [] => none
  | subject :: tail => do
    let person ← readPerson subject
    let (negative, tail) := takeFlag "ли" tail
    let (phase, tail) := takePhase tail
    let (travel, tail) ← takeTravel tail
    let (time, tail) := takeTime tail
    let (result, tail) := takeFlag "ка" tail
    let spatial ← readSpatial tail
    return ⟨person, negative, phase, travel, time, result, spatial⟩

private theorem bind_from_some {α β : Type} (value : α) (next : α → Option β) :
    (some value >>= next) = next value :=
  rfl

private theorem takeNegative_render (negative : Bool) (phase : Phase) (travel : Travel)
    (tail : List String) :
    takeFlag "ли" ((if negative then ["ли"] else []) ++ (phase.words ++ travel.word :: tail)) =
      (negative, phase.words ++ travel.word :: tail) := by
  cases negative with
  | true => rfl
  | false => cases phase <;> cases travel <;> rfl

private theorem takePhase_render (phase : Phase) (travel : Travel) (tail : List String) :
    takePhase (phase.words ++ travel.word :: tail) = (phase, travel.word :: tail) := by
  cases phase <;> cases travel <;> rfl

private theorem takeTravel_render (travel : Travel) (tail : List String) :
    takeTravel (travel.word :: tail) = some (travel, tail) := by
  cases travel <;> rfl

private theorem takeTime_render (time : Time) (result : Bool)
    (spatial : Option (Relation × Place)) :
    takeTime (time.words ++ ((if result then ["ка"] else []) ++ spatialWords spatial)) =
      (time, (if result then ["ка"] else []) ++ spatialWords spatial) := by
  cases time with
  | implicit =>
    cases result with
    | true => rfl
    | false =>
      cases spatial with
      | none => rfl
      | some pair =>
        rcases pair with ⟨relation, place⟩
        cases relation <;> rfl
  | past => rfl
  | present => rfl
  | future => rfl

private theorem takeResult_render (result : Bool) (spatial : Option (Relation × Place)) :
    takeFlag "ка" ((if result then ["ка"] else []) ++ spatialWords spatial) =
      (result, spatialWords spatial) := by
  cases result with
  | true => rfl
  | false =>
    cases spatial with
    | none => rfl
    | some pair =>
      rcases pair with ⟨relation, place⟩
      cases relation <;> rfl

theorem readSpatial_render (spatial : Option (Relation × Place)) :
    readSpatial (spatialWords spatial) = some spatial := by
  cases spatial with
  | none => rfl
  | some pair =>
    rcases pair with ⟨relation, place⟩
    cases relation <;> cases place <;> rfl

theorem parse_render (clause : Phrase) : parse (render clause) = some clause := by
  cases clause
  simp only [render, List.append_assoc, List.cons_append, List.nil_append, parse, readPerson_word,
    bind_from_some, takeNegative_render, takePhase_render, takeTravel_render,
    takeTime_render, takeResult_render, readSpatial_render]
  rfl

private theorem readPerson_rejoin {word : String} {person : Person}
    (read : readPerson word = some person) : person.word = word := by
  unfold readPerson at read
  split at read <;> simp at read
  all_goals
    subst person
    rfl

private theorem takeFlag_rejoin (marker : String) (words : List String) :
    (if (takeFlag marker words).1 then [marker] else []) ++ (takeFlag marker words).2 =
      words := by
  cases words with
  | nil => rfl
  | cons first tail =>
    by_cases equal : first = marker <;> simp [takeFlag, equal]

private theorem takePhase_rejoin (words : List String) :
    (takePhase words).1.words ++ (takePhase words).2 = words := by
  unfold takePhase
  split <;> rfl

private theorem takeTravel_rejoin {words tail : List String} {travel : Travel}
    (read : takeTravel words = some (travel, tail)) : travel.word :: tail = words := by
  unfold takeTravel at read
  split at read <;> simp at read
  all_goals
    obtain ⟨sameTravel, sameTail⟩ := read
    subst travel
    subst tail
    rfl

private theorem takeTime_rejoin (words : List String) :
    (takeTime words).1.words ++ (takeTime words).2 = words := by
  unfold takeTime
  split <;> rfl

private theorem readRelation_rejoin {word : String} {relation : Relation}
    (read : readRelation word = some relation) : relation.word = word := by
  unfold readRelation at read
  split at read <;> simp at read
  all_goals
    subst relation
    rfl

private theorem readPlace_rejoin {word : String} {place : Place}
    (read : readPlace word = some place) : place.word = word := by
  unfold readPlace at read
  split at read <;> simp at read
  all_goals
    subst place
    rfl

theorem readSpatial_rejoin {words : List String} {spatial : Option (Relation × Place)}
    (read : readSpatial words = some spatial) : spatialWords spatial = words := by
  unfold readSpatial at read
  split at read
  · cases read
    rfl
  · rename_i relationWord placeWord
    obtain ⟨relation, relationRead, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨place, placeRead, read⟩ := Option.bind_eq_some_iff.mp read
    change some (some (relation, place)) = some spatial at read
    cases read
    simp only [spatialWords, readRelation_rejoin relationRead, readPlace_rejoin placeRead]
  · contradiction

/-- Every accepted token sequence is the canonical rendering of its decoded clause. -/
theorem render_parse {words : List String} {clause : Phrase}
    (read : parse words = some clause) : render clause = words := by
  cases words with
  | nil => contradiction
  | cons subject tail =>
    simp only [parse] at read
    obtain ⟨person, personRead, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨travel, rest⟩, travelRead, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨spatial, spatialRead, read⟩ := Option.bind_eq_some_iff.mp read
    have equal : _ = clause := Option.some.inj read
    subst clause
    simp only [render, List.append_assoc, List.cons_append, List.nil_append]
    rw [readSpatial_rejoin spatialRead, takeFlag_rejoin, takeTime_rejoin, takeTravel_rejoin travelRead,
      takePhase_rejoin, takeFlag_rejoin, readPerson_rejoin personRead]

theorem compact_minimal_among_parsed {words : List String} {alternative : Phrase}
    (clause : Phrase) (read : parse words = some alternative) (equal : sameMeaning clause alternative) :
    (render (compact clause)).length ≤ words.length := by
  rw [← render_parse read]
  exact compact_minimal clause alternative equal

/-- No two encoded movement clauses in the fragment have the same surface form. -/
theorem render_injective {left right : Phrase} (same : render left = render right) :
    left = right := by
  have applied := congrArg parse same
  rw [parse_render, parse_render] at applied
  exact Option.some.inj applied

example : parse ["и", "ки", "ло", "ка", "куа", "тив"] =
    some ⟨.speaker, false, .neutral, .go, .past, true, some (.direction, .garden)⟩ := by decide
example : parse ["и", "ки", "ка", "тив"] = none := by decide
example : parse ["и", "ии", "ки"] = none := by decide
example : parse ["и", "ки", "тив"] = none := by decide

end Laiu.Syntax
