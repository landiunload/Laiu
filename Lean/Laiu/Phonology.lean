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

def hasSameVowelBoundary (left right : String) : Bool :=
  match left.toList.getLast?, right.toList.head? with
  | some first, some second => isVowel first && first == second
  | _, _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem checked_forms_follow_sound_inventory_and_syllable_shape :
    Morphology.reservedForms.all hasSyllableShape = true := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem checked_forms_fit_available_repeat_marks :
    Morphology.reservedForms.all fitsRepeatMarks = true := by decide

example : withoutVowelLength "ли" = withoutVowelLength "лии" ∧
    withoutVowelLength "лии" = withoutVowelLength "лиии" := by decide

end Laiu.Phonology
