import Laiu.Phonology

namespace Laiu.Script

inductive Repeat where
  | single | double | triple
  deriving BEq, DecidableEq, Repr

structure Glyph where
  sound : Char
  count : Repeat
  deriving BEq, DecidableEq, Repr

private def Glyph.sounds (glyph : Glyph) : List Char :=
  match glyph.count with
  | .single => [glyph.sound]
  | .double => [glyph.sound, glyph.sound]
  | .triple => [glyph.sound, glyph.sound, glyph.sound]

private def addSound (sound : Char) : List Glyph → List Glyph
  | ⟨first, .single⟩ :: rest =>
    if sound = first then ⟨first, .double⟩ :: rest else ⟨sound, .single⟩ :: ⟨first, .single⟩ :: rest
  | ⟨first, .double⟩ :: rest =>
    if sound = first then ⟨first, .triple⟩ :: rest else ⟨sound, .single⟩ :: ⟨first, .double⟩ :: rest
  | glyphs => ⟨sound, .single⟩ :: glyphs

private def pack (sounds : List Char) : List Glyph := sounds.foldr addSound []

private def unpack (glyphs : List Glyph) : List Char := glyphs.flatMap Glyph.sounds

private theorem unpack_addSound (sound : Char) (glyphs : List Glyph) :
    unpack (addSound sound glyphs) = sound :: unpack glyphs := by
  cases glyphs with
  | nil => rfl
  | cons glyph rest =>
    rcases glyph with ⟨first, count⟩
    cases count <;> by_cases same : sound = first <;> simp [same, addSound, unpack, Glyph.sounds]

private theorem unpack_pack (sounds : List Char) : unpack (pack sounds) = sounds := by
  induction sounds with
  | nil => rfl
  | cons first rest ih =>
    change unpack (addSound first (pack rest)) = first :: rest
    rw [unpack_addSound, ih]

def encode (word : String) : Option (List Glyph) :=
  if Phonology.hasSyllableShape word && Phonology.fitsRepeatMarks word then
    some (pack word.toList)
  else none

def decode (glyphs : List Glyph) : Option String :=
  let word := String.ofList (unpack glyphs)
  if encode word = some glyphs then some word else none

theorem decode_encode {word : String} {glyphs : List Glyph} (encoded : encode word = some glyphs) :
    decode glyphs = some word := by
  unfold encode at encoded
  split at encoded
  · cases encoded
    simp [decode, unpack_pack, encode, *]
  · contradiction

theorem encode_decode {word : String} {glyphs : List Glyph} (decoded : decode glyphs = some word) :
    encode word = some glyphs := by
  simp only [decode] at decoded
  split at decoded <;> simp_all

theorem legal_word_has_writing (word : String) (syllable : Phonology.hasSyllableShape word = true)
    (repeats : Phonology.fitsRepeatMarks word = true) : ∃ glyphs, encode word = some glyphs := by
  simp [encode, syllable, repeats]

theorem inventory_has_lossless_writing (word : String) (known : word ∈ Morphology.reservedForms) :
    ∃ glyphs, encode word = some glyphs ∧ decode glyphs = some word := by
  obtain ⟨glyphs, written⟩ := legal_word_has_writing word
    (List.all_eq_true.mp Phonology.checked_forms_follow_sound_inventory_and_syllable_shape word known)
    (List.all_eq_true.mp Phonology.checked_forms_fit_available_repeat_marks word known)
  exact ⟨glyphs, written, decode_encode written⟩

#guard encode "киив" == some [⟨'к', .single⟩, ⟨'и', .double⟩, ⟨'в', .single⟩]
#guard encode "киурри" == some [⟨'к', .single⟩, ⟨'и', .single⟩, ⟨'у', .single⟩, ⟨'р', .double⟩, ⟨'и', .single⟩]
#guard encode "ииии" == none
#guard decode [⟨'и', .single⟩, ⟨'и', .single⟩] == none
#guard decode [⟨'и', .triple⟩] == some "иии"

end Laiu.Script
