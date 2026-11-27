import Laiu.Lexicon
import Laiu.Syntax

namespace Laiu.Morphology

def verbs : List String :=
  ["ки", "роки", "ру", "но", "нум", "ву", "сум", "ку", "му", "мут", "ко", "лиси", "пи", "рис", "мит", "та", "ра", "мил", "ми", "лип", "тал", "тил", "ри"]

def nouns : List String :=
  ["ар", "ну", "ари", "боа", "са", "со", "сок", "ти", "ил", "или", "лап", "ир", "ур", "ор", "иру", "кам", "пис", "кув", "ник", "вим", "тив", "там", "вус", "кири", "лури", "мири", "рари", "лиил"]

def adjectives : List String :=
  ["ви", "ва", "ал", "эл", "ул", "ол", "пар", "нар", "сим", "лик", "ма"]

def digits : List String :=
  ["кати", "кити", "коти", "оти", "ото", "уки", "ики", "оки", "ати"]

def rankSuffixes : List String :=
  ["", "м", "ми", "к", "ки", "л", "ли"]

private def verbNounSuffixes : List String := ["ри", "ур", "ас", "ив", "ум"]

def attach (base suffix : String) : String := base ++ suffix

private def doubleFirstVowel : List Char → List Char
  | [] => []
  | first :: rest =>
    if Lexicon.vowels.contains first then first :: first :: rest
    else first :: doubleFirstVowel rest

def superlative (adjective : String) : String :=
  String.ofList (doubleFirstVowel adjective.toList)

/-- One productive operation on each listed stem, with its appropriate category. -/
def generated : List String :=
  (verbs.flatMap fun verb => verbNounSuffixes.map (attach verb)) ++
  (nouns.map fun noun => attach noun "ам") ++
  (adjectives.flatMap fun adjective => [attach adjective "ал", attach adjective "у", superlative adjective])

/-- Plural of a derived noun and the documented agent-to-state construction. -/
def twoSuffixForms : List String :=
  (verbs.flatMap fun verb => (verbNounSuffixes.map fun suffix => attach verb (suffix ++ "ам")) ++
    [attach verb "урри"]) ++
  (adjectives.map fun adjective => attach adjective "алам")

def higherNumericForms : List String :=
  digits.flatMap fun digit => (rankSuffixes.drop 1).map (attach digit)

set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem one_step_forms_unique : generated.Nodup := by
  decide

/-- These forms have a single entry even when also reached by regular morphology. -/
theorem only_shared_dictionary_forms :
    generated.filter ((Lexicon.forms Lexicon.entries).contains ·) =
      ["кири", "рари", "мири", "виу"] := by
  decide

theorem numeric_forms_do_not_collide :
    ((Lexicon.forms Lexicon.entries) ++ higherNumericForms).Nodup ∧
      higherNumericForms.filter (generated.contains ·) = [] := by
  decide

theorem two_suffix_forms_unique : twoSuffixForms.Nodup := by decide

theorem two_suffix_forms_do_not_collide_with_roots_or_numbers :
    twoSuffixForms.filter ((Lexicon.forms Lexicon.entries ++ higherNumericForms).contains ·) = [] := by
  decide

/-- These plurals already arise from the corresponding dictionary nouns. -/
theorem only_shared_two_suffix_forms :
    twoSuffixForms.filter (generated.contains ·) = ["кириам", "рариам", "мириам"] := by
  decide

def basicReservedForms : List String :=
  Lexicon.forms Lexicon.entries ++ generated ++ higherNumericForms ++ twoSuffixForms

def possessivePrefix : String := "сул"

def possessiveForm (person : Syntax.Person) : String := possessivePrefix ++ person.word

def possessiveForms : List String := Syntax.Person.all.map possessiveForm

theorem possessive_forms_are_distinct : possessiveForms.Nodup := by decide

theorem possessive_forms_are_fresh : possessiveForms.filter (basicReservedForms.contains ·) = [] := by
  decide

def reservedForms : List String := basicReservedForms ++ possessiveForms

/-- A proposed compound must be fresh in the checked inventory. -/
def proposeCompound (left right : String) : Option String :=
  let spelling := attach left right
  if spelling ∈ reservedForms then none else some spelling

theorem proposed_compound_is_fresh {left right spelling : String}
    (accepted : proposeCompound left right = some spelling) :
    spelling ∉ reservedForms := by
  by_cases taken : attach left right ∈ reservedForms
  · simp [proposeCompound, taken] at accepted
  · have spellingEq : attach left right = spelling := by
      simpa [proposeCompound, taken] using accepted
    exact spellingEq ▸ taken

theorem approved_compound_preserves_dictionary_uniqueness {left right spelling : String}
    (accepted : proposeCompound left right = some spelling) :
    (spelling :: Lexicon.forms Lexicon.entries).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, Lexicon.entries_have_no_duplicate_forms⟩
  intro present
  apply proposed_compound_is_fresh accepted
  simp [reservedForms, basicReservedForms, present]

example : proposeCompound "ки" "ти" = none := by decide
example : proposeCompound "ко" "ти" = none := by decide
example : proposeCompound "киур" "ри" = none := by decide
example : proposeCompound "сул" "и" = none := by decide

example : generated.length = 176 := by decide
example : higherNumericForms.length = 54 := by decide
example : attach "но" "ас" = "ноас" := by rfl
example : attach "ви" "ал" = "виал" := by rfl
example : attach "ва" "ал" = "ваал" := by rfl
example : attach "ки" "ив" = "киив" := by rfl

end Laiu.Morphology
