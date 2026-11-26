import Laiu.Phonology

namespace Laiu.Deixis

inductive Distance where
  | near | far
  deriving DecidableEq, Repr

inductive Use where
  | one | many | place
  deriving DecidableEq, Repr

def Distance.stem : Distance → String
  | .near => "то"
  | .far => "во"

def Use.suffix : Use → String
  | .one => ""
  | .many => "м"
  | .place => "у"

def word (distance : Distance) (role : Use) : String := distance.stem ++ role.suffix

def forms : List (Distance × Use) :=
  [Distance.near, .far].flatMap fun distance => [Use.one, .many, .place].map (distance, ·)

def read (spelling : String) : Option (Distance × Use) :=
  forms.find? fun (distance, role) => word distance role == spelling

theorem read_word (distance : Distance) (role : Use) :
    read (word distance role) = some (distance, role) := by
  cases distance <;> cases role <;> decide

theorem read_word_without_duration (distance : Distance) (role : Use) :
    read (Phonology.withoutVowelLength (word distance role)) = some (distance, role) := by
  cases distance <;> cases role <;> decide

theorem distance_survives_in_context (role : Use) (left right : String) :
    Phonology.withoutVowelLength (left ++ word .near role ++ right) ≠
      Phonology.withoutVowelLength (left ++ word .far role ++ right) := by
  cases role <;> exact Phonology.distinct_consonants_survive_in_context _ _ left right (by decide)

theorem number_survives_in_context (distance : Distance) (left right : String) :
    Phonology.withoutVowelLength (left ++ word distance .one ++ right) ≠
      Phonology.withoutVowelLength (left ++ word distance .many ++ right) := by
  cases distance <;> exact Phonology.distinct_consonant_counts_survive_in_context _ _ left right (by decide)

end Laiu.Deixis
