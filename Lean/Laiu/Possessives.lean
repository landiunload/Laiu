import Laiu.Phonology

namespace Laiu.Possessives

open Morphology Syntax

def renderFull (person : Person) : List String := ["си", person.word]

def renderShort (person : Person) : List String := [possessiveForm person]

private def readShort (word : String) : Option Person :=
  Person.all.find? fun person => possessiveForm person == word

def parse : List String → Option Person
  | ["си", person] => readPerson person
  | [word] => readShort word
  | _ => none

theorem parse_full (person : Person) : parse (renderFull person) = some person := by
  simp [parse, renderFull, readPerson_word]

theorem parse_short (person : Person) : parse (renderShort person) = some person := by
  cases person <;> decide

theorem short_saves_one_word (person : Person) :
    (renderShort person).length + 1 = (renderFull person).length := rfl

theorem short_preserves_open_syllables (person : Person) :
    Phonology.closedSyllableCount (possessiveForm person) = 0 ∧
      Phonology.syllableCount (possessiveForm person) = Phonology.syllableCount person.word + 1 := by
  cases person <;> decide

theorem possession_fits_reserved_forms (person : Person) : possessiveForm person ∈ reservedForms :=
  List.mem_append_right _ (List.mem_map.mpr ⟨person, person.mem_all, rfl⟩)

theorem short_keeps_personal_contrasts (first second : Person) :
    Phonology.withoutSoundLength (possessiveForm first) =
        Phonology.withoutSoundLength (possessiveForm second) ↔
      Phonology.withoutSoundLength first.word = Phonology.withoutSoundLength second.word := by
  cases first <;> cases second <;> decide

abbrev Noun := {word : String // word ∈ nouns}

private def readNoun (word : String) : Option Noun :=
  if known : word ∈ nouns then some ⟨word, known⟩ else none

/-- In a chain, each noun is possessed by the group to its right. -/
structure Group where
  head : Noun
  owners : List Noun
  person : Option Person
  deriving DecidableEq, Repr

private def renderOwners (owners : List Noun) : List String :=
  owners.flatMap fun noun => ["си", noun.val]

def renderGroup (short : Bool) (group : Group) : List String :=
  group.head.val :: (renderOwners group.owners ++
    group.person.toList.flatMap (if short then renderShort else renderFull))

private def parseOwners : List String → Option (List Noun × Option Person)
  | [] => some ([], none)
  | "си" :: word :: rest =>
    if let some noun := readNoun word then do
      let (owners, holder) ← parseOwners rest
      return (noun :: owners, holder)
    else if rest.isEmpty then (readPerson word).map (fun person => ([], some person)) else none
  | [word] => (readShort word).map (fun person => ([], some person))
  | _ => none

def parseGroup : List String → Option Group
  | head :: body => do
    let noun ← readNoun head
    let (owners, holder) ← parseOwners body
    return ⟨noun, owners, holder⟩
  | [] => none

private theorem read_noun (noun : Noun) : readNoun noun.val = some noun := by
  simp [readNoun, noun.property]

private theorem person_is_not_noun (person : Person) : readNoun person.word = none := by
  cases person <;> decide

private theorem parse_rendered_owners (owners : List Noun) (person : Option Person) (short : Bool) :
    parseOwners (renderOwners owners ++ person.toList.flatMap (if short then renderShort else renderFull)) =
      some (owners, person) := by
  induction owners with
  | nil =>
    cases person with
    | none => rfl
    | some person =>
      cases short with
      | false => simp [renderOwners, renderFull, parseOwners, person_is_not_noun, readPerson_word]
      | true => cases person <;> decide
  | cons noun rest ih =>
    change parseOwners ("си" :: noun.val ::
      (renderOwners rest ++ person.toList.flatMap (if short then renderShort else renderFull))) =
        some (noun :: rest, person)
    simp [parseOwners, read_noun, ih]

theorem parse_renderGroup (short : Bool) (group : Group) :
    parseGroup (renderGroup short group) = some group := by
  rcases group with ⟨noun, owners, person⟩
  simp [parseGroup, renderGroup, read_noun, parse_rendered_owners]

theorem short_group_saves_one_word (group : Group) (person : Person) (known : group.person = some person) :
    (renderGroup true group).length + 1 = (renderGroup false group).length := by
  simp [renderGroup, renderFull, renderShort, known] <;> omega

example : parseGroup ["там", "си", "ир", "сула"] = parseGroup ["там", "си", "ир", "си", "а"] := by decide
example : parseGroup ["вим", "сули"] ≠ parseGroup ["вим", "сулии"] := by decide
example : parseGroup ["там", "сула", "суло"] = none := by decide
example : parseGroup ["там", "си", "суло"] = none := by decide

end Laiu.Possessives
