import Laiu.Morphology

namespace Laiu.Phonology

def isVowel (sound : Char) : Bool := Lexicon.vowels.contains sound

def consonants : List Char := ['п', 'б', 'т', 'к', 'в', 'с', 'м', 'н', 'р', 'л']

def hasSyllableShape (word : String) : Bool :=
  let sounds := word.toList
  let consonantRuns := (sounds.splitOnP isVowel)
  sounds.all (fun c => isVowel c || consonants.contains c) &&
    match consonantRuns with
    | onset :: (next :: rest) =>
      let following := next :: rest
      onset.length ≤ 1 && ((following.getLast?).getD []).length ≤ 1 &&
        following.dropLast.all (fun run => run.length ≤ 2)
    | _ => false

private def hasFourthRepeat : List Char → Bool
  | a :: b :: c :: d :: rest =>
    (a == b && b == c && c == d) || hasFourthRepeat (b :: c :: d :: rest)
  | _ => false

def fitsRepeatMarks (word : String) : Bool := !hasFourthRepeat word.toList

private def collapseRuns (collapse : Char → Bool) (previous : Option Char) : List Char → List Char
  | [] => []
  | sound :: rest =>
    let tail := collapseRuns collapse (some sound) rest
    if collapse sound && previous == some sound then tail else sound :: tail

/-- Models a listener hearing vowel quality while losing all duration information. -/
def withoutVowelLength (word : String) : String :=
  String.ofList (collapseRuns isVowel none word.toList)

def glyphBases (word : String) : Nat := (collapseRuns (fun _ => true) none word.toList).length

def vowelBeats (word : String) : Nat := (word.toList.filter isVowel).length

def syllableCount (word : String) : Nat :=
  ((collapseRuns isVowel none word.toList).filter isVowel).length

/-- With maximal onset, a coda occurs before a two-consonant boundary or at word end. -/
def closedSyllableCount (word : String) : Nat :=
  let afterVowels := (word.toList.splitOnP isVowel).drop 1
  let internal := (afterVowels.dropLast.filter fun run => run.length == 2).length
  let final := if (afterVowels.getLast?.getD []).isEmpty then 0 else 1
  internal + final

def hasSameVowelBoundary (left right : String) : Bool :=
  match left.toList.getLast?, right.toList.head? with
  | some first, some second => isVowel first && first == second
  | _, _ => false

/-- Selected unwanted resemblances, written using the sounds of Laiu. -/
private def avoidedProfiles : List String :=
  -- Russian, Spanish/Portuguese, then English (two approximations of /æ/).
  ["каки", "кака", "сука", "пута", "путо", "паки", "пэки"]

/-- Looks for complete words or runs of up to four words within one speech group. -/
def unwantedResemblance : List String → Option (List String)
  | [] => none
  | first :: rest =>
    let lengths := List.range' 1 (min 4 (rest.length + 1))
    let windows := lengths.map ((first :: rest).take ·)
    (windows.find? fun words => avoidedProfiles.contains (withoutVowelLength (String.join words)))
      <|> unwantedResemblance rest

example : unwantedResemblance ["а", "каа", "ки", "куа"] = some ["каа", "ки"] := by decide
example : unwantedResemblance ["ла", "пуу", "та"] = some ["пуу", "та"] := by decide
example : unwantedResemblance ["ииа", "мо", "ки"] = none := by decide
example : unwantedResemblance ["мо", "ли", "ки"] = none := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem imperative_distinct_without_vowel_length :
    Morphology.reservedForms.filter (fun word => withoutVowelLength word == "мо") = ["мо"] := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem checked_forms_follow_sound_inventory_and_syllable_shape :
    Morphology.reservedForms.all hasSyllableShape = true := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem checked_forms_fit_available_repeat_marks :
    Morphology.reservedForms.all fitsRepeatMarks = true := by decide

example : withoutVowelLength "и" = withoutVowelLength "ии" := by decide
example : syllableCount "нэлу" = 2 ∧ closedSyllableCount "нэлу" = 0 := by decide
example : syllableCount "ами" = 2 ∧ closedSyllableCount "ами" = 0 := by decide
example : syllableCount "киурри" = 3 ∧ closedSyllableCount "киурри" = 1 := by decide

end Laiu.Phonology
