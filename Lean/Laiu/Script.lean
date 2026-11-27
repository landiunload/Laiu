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

inductive Ligature where
  | ki | li | em
  deriving BEq, DecidableEq, Repr

def Ligature.glyphs : Ligature → List Glyph
  | .ki => [⟨'к', .single⟩, ⟨'и', .single⟩]
  | .li => [⟨'л', .single⟩, ⟨'и', .single⟩]
  | .em => [⟨'э', .single⟩, ⟨'м', .single⟩]

inductive CompactGlyph where
  | basic (glyph : Glyph)
  | joined (pair : Ligature)
  deriving BEq, DecidableEq, Repr

private def CompactGlyph.expand : CompactGlyph → List Glyph
  | .basic glyph => [glyph]
  | .joined pair => pair.glyphs

private def joinPair : Glyph → Glyph → Option Ligature
  | ⟨'к', .single⟩, ⟨'и', .single⟩ => some .ki
  | ⟨'л', .single⟩, ⟨'и', .single⟩ => some .li
  | ⟨'э', .single⟩, ⟨'м', .single⟩ => some .em
  | _, _ => none

private theorem joined_pair_glyphs {first second : Glyph} {pair : Ligature}
    (joined : joinPair first second = some pair) : pair.glyphs = [first, second] := by
  unfold joinPair at joined
  split at joined <;> cases joined <;> rfl

private def addCompact (first : Glyph) (rest : List CompactGlyph) : List CompactGlyph :=
  match rest with
  | .basic second :: tail =>
    match joinPair first second with
    | some pair => .joined pair :: tail
    | none => .basic first :: rest
  | _ => .basic first :: rest

def compactGlyphs (glyphs : List Glyph) : List CompactGlyph := glyphs.foldr addCompact []

def expandGlyphs (glyphs : List CompactGlyph) : List Glyph := glyphs.flatMap CompactGlyph.expand

private theorem expand_addCompact (first : Glyph) (rest : List CompactGlyph) :
    expandGlyphs (addCompact first rest) = first :: expandGlyphs rest := by
  cases rest with
  | nil => rfl
  | cons head tail =>
    cases head with
    | joined => rfl
    | basic second =>
      cases joined : joinPair first second with
      | none => simp [addCompact, joined, expandGlyphs, CompactGlyph.expand]
      | some pair =>
        simp [addCompact, joined, expandGlyphs, CompactGlyph.expand, joined_pair_glyphs joined]

theorem expand_compactGlyphs (glyphs : List Glyph) : expandGlyphs (compactGlyphs glyphs) = glyphs := by
  induction glyphs with
  | nil => rfl
  | cons first rest ih =>
    change expandGlyphs (addCompact first (compactGlyphs rest)) = first :: rest
    rw [expand_addCompact, ih]

theorem compactGlyphs_never_add_signs (glyphs : List Glyph) :
    (compactGlyphs glyphs).length ≤ glyphs.length := by
  have addLength (first : Glyph) (rest : List CompactGlyph) :
      (addCompact first rest).length ≤ rest.length + 1 := by
    cases rest with
    | nil => simp [addCompact]
    | cons head tail =>
      cases head with
      | joined => simp [addCompact]
      | basic second => cases joined : joinPair first second <;> simp [addCompact, joined]
  induction glyphs with
  | nil => decide
  | cons first rest ih =>
    exact Nat.le_trans (addLength first (compactGlyphs rest)) (Nat.succ_le_succ ih)

def encodeCompact (word : String) : Option (List CompactGlyph) :=
  (encode word).map compactGlyphs

def decodeCompact (glyphs : List CompactGlyph) : Option String := decode (expandGlyphs glyphs)

theorem decode_encodeCompact {word : String} {glyphs : List CompactGlyph}
    (encoded : encodeCompact word = some glyphs) : decodeCompact glyphs = some word := by
  obtain ⟨plain, written, rfl⟩ := Option.map_eq_some_iff.mp encoded
  simp [decodeCompact, expand_compactGlyphs, decode_encode written]

theorem inventory_has_lossless_compact_writing (word : String) (known : word ∈ Morphology.reservedForms) :
    ∃ glyphs, encodeCompact word = some glyphs ∧ decodeCompact glyphs = some word := by
  obtain ⟨plain, written, _⟩ := inventory_has_lossless_writing word known
  have compact : encodeCompact word = some (compactGlyphs plain) := by
    simp [encodeCompact, written]
  exact ⟨_, compact, decode_encodeCompact compact⟩

#guard encodeCompact "эмли" == some [.joined .em, .joined .li]
#guard encodeCompact "кии" == some [.basic ⟨'к', .single⟩, .basic ⟨'и', .double⟩]
#guard encodeCompact "кки" == none
#guard decodeCompact [.joined .ki] == some "ки"

end Laiu.Script
