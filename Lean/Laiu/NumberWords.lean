import Laiu.Morphology
import Laiu.Numbers

namespace Laiu.NumberWords

/-- A decimal rank and a zero-based index into the nine nonzero digit words. -/
abbrev Field := Nat × Nat

def width : Nat := 7

private def table : List Field :=
  (List.range width).flatMap (fun rank => (List.range 9).map (fun digit => (rank, digit)))

private def word (field : Field) : String :=
  (Morphology.digits[field.2]?.getD "") ++ (Morphology.rankSuffixes[field.1]?.getD "")

private def fieldValue (field : Field) : Nat :=
  (field.2 + 1) * 10 ^ field.1

private def value (fields : List Field) : Nat :=
  (fields.map fieldValue).sum

private def liftRank (field : Field) : Field :=
  (field.1 + 1, field.2)

private def fields (places : Nat) (n : Nat) : List Field :=
  match places with
  | 0 => []
  | places + 1 =>
    let higher := (fields places (n / 10)).map liftRank
    let remainder := n % 10
    if remainder = 0 then higher else (0, remainder - 1) :: higher

private theorem value_lift (ds : List Field) :
    value (ds.map liftRank) = value ds * 10 := by
  induction ds with
  | nil => rfl
  | cons field rest ih =>
    simp only [value, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.add_mul]
    simp [fieldValue, liftRank, Nat.pow_succ, Nat.mul_assoc]

private theorem value_fields (places n : Nat) (bounded : n < 10 ^ places) :
    value (fields places n) = n := by
  induction places generalizing n with
  | zero =>
    have : n = 0 := by simpa using bounded
    subst n
    rfl
  | succ places ih =>
    have quotientBound : n / 10 < 10 ^ places :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [Nat.pow_succ] using bounded)
    have decomposition := Nat.mod_add_div n 10
    rw [fields]
    split
    · rename_i h
      rw [value_lift, ih _ quotientBound]
      omega
    · rename_i h
      change fieldValue (0, n % 10 - 1) + value ((fields places (n / 10)).map liftRank) = n
      rw [value_lift, ih _ quotientBound]
      simp [fieldValue]
      omega

private theorem fields_bounded (places n : Nat) (d : Field) (h : d ∈ fields places n) :
    d.1 < places ∧ d.2 < 9 := by
  induction places generalizing n d with
  | zero => simp [fields] at h
  | succ places ih =>
    simp only [fields] at h
    have higher (hh : d ∈ (fields places (n / 10)).map liftRank) :
        d.1 < places + 1 ∧ d.2 < 9 := by
      obtain ⟨item, mem, eq⟩ := List.mem_map.mp hh
      subst d
      simpa [liftRank] using ih (n / 10) item mem
    split at h
    · exact higher h
    · rcases List.mem_cons.mp h with eq | mem
      · subst d
        constructor
        · simp
        · change n % 10 - 1 < 9
          have := Nat.mod_lt n (by decide : 0 < 10)
          omega
      · exact higher mem

private theorem mem_table {field : Field} (rank : field.1 < width) (digit : field.2 < 9) :
    field ∈ table := by
  apply List.mem_flatMap.mpr
  exact ⟨field.1, List.mem_range.mpr rank,
    List.mem_map.mpr ⟨field.2, List.mem_range.mpr digit, by cases field <;> rfl⟩⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem table_unique : (table.map word).Nodup := by decide

private theorem find_word_of_mem (items : List Field) (distinct : (items.map word).Nodup)
    (target : Field) (mem : target ∈ items) :
    items.find? (fun candidate => word candidate == word target) = some target := by
  induction items with
  | nil => simp at mem
  | cons head rest ih =>
    rcases List.mem_cons.mp mem with eq | inRest
    · subst target
      simp
    · have nodup := List.nodup_cons.mp (by simpa only [List.map_cons] using distinct)
      have unequal : word head ≠ word target := by
        intro same
        apply nodup.1
        rw [same]
        exact List.mem_map.mpr ⟨target, inRest, rfl⟩
      simp [beq_eq_false_iff_ne.mpr unequal, ih nodup.2 inRest]

private def readField (token : String) : Option Field :=
  table.find? (fun candidate => word candidate == token)

private theorem read_fields (ds : List Field) (admitted : ∀ d ∈ ds, d ∈ table) :
    (ds.map word).mapM readField = some ds := by
  induction ds with
  | nil => rfl
  | cons first rest ih =>
    have head : readField (word first) = some first :=
      find_word_of_mem table table_unique first (admitted first (by simp))
    have tail := ih (fun d mem => admitted d (by simp [mem]))
    simp [head, tail]

private def spellBlock (n : Nat) : List String :=
  if n = 0 then ["нэ"] else ((fields width n).reverse.map word)

private def readBlock (tokens : List String) : Option Nat :=
  if tokens = ["нэ"] then some 0
  else (tokens.mapM readField).map (fun digits => value digits.reverse)

private theorem reserved_tokens_not_fields :
    ["па", "нэ", "ит", "тэл"].all (fun t => !(table.map word).contains t) = true := by
  decide

private theorem reserved_not_field {d : Field} (h : d ∈ table) {token : String}
    (reserved : token ∈ ["па", "нэ", "ит", "тэл"]) : word d ≠ token := by
  intro eq
  have mem : token ∈ table.map word := by
    rw [← eq]
    exact List.mem_map.mpr ⟨d, h, rfl⟩
  have forbidden := List.all_eq_true.mp reserved_tokens_not_fields token reserved
  simp [mem] at forbidden

private theorem encoded_fields_admitted (n : Nat) :
    ∀ d ∈ (fields width n).reverse, d ∈ table := by
  intro d mem
  have limits := fields_bounded width n d (by simpa using mem)
  exact mem_table limits.1 limits.2

private theorem marker_not_in_block (n : Nat) {token : String} (notZero : token ≠ "нэ")
    (reserved : token ∈ ["па", "нэ", "ит", "тэл"]) : token ∉ spellBlock n := by
  unfold spellBlock
  split
  · simpa using notZero
  · intro h
    obtain ⟨field, mem, eq⟩ := List.mem_map.mp h
    exact reserved_not_field (encoded_fields_admitted n field mem) reserved eq

private theorem read_spell_block (n : Nat) (bounded : n < Numbers.radix) :
    readBlock (spellBlock n) = some n := by
  by_cases zero : n = 0
  · subst n
    rfl
  · have parsed := read_fields (fields width n).reverse (encoded_fields_admitted n)
    have nonzero : ((fields width n).reverse.map word) ≠ ["нэ"] := by
      intro eq
      have absent : readField "нэ" = none := by decide
      rw [eq] at parsed
      simp [absent] at parsed
    have bound : n < 10 ^ width := bounded
    unfold spellBlock readBlock
    rw [ite_eq_right zero, ite_eq_right nonzero, parsed]
    simp only [Option.map_some, List.reverse_reverse, value_fields width n bound]

def spell (n : Nat) : List String :=
  ["па"].intercalate ((Numbers.encode n).map spellBlock)

private def readRaw (tokens : List String) : Option Nat :=
  ((tokens.splitOn "па").mapM readBlock).map Numbers.decode

/-- Re-encoding validates rank order, omission of zero ranks, and block boundaries together. -/
def parse (tokens : List String) : Option Nat := do
  let n ← readRaw tokens
  if spell n = tokens then some n else none

private theorem spelled_blocks_map (n : Nat) :
    ((Numbers.encode n).map spellBlock).mapM readBlock = some (Numbers.encode n) := by
  have forBounded (blocks : List Nat) (bounded : ∀ d ∈ blocks, d < Numbers.radix) :
      (blocks.map spellBlock).mapM readBlock = some blocks := by
    induction blocks with
    | nil => rfl
    | cons d tail ih =>
      have head := read_spell_block d (bounded d (by simp))
      have rest := ih (fun e mem => bounded e (by simp [mem]))
      simp [head, rest]
  exact forBounded _ (fun d mem => Numbers.encode_blocks_bounded n d mem)

private theorem read_raw_spell (n : Nat) : readRaw (spell n) = some n := by
  have notEmpty : (Numbers.encode n).map spellBlock ≠ [] := by
    intro empty
    have h : Numbers.encode n = [] := List.map_eq_nil_iff.mp empty
    have canonical := Numbers.encode_is_canonical n
    rw [h] at canonical
    cases canonical
  have noSeparator : ∀ block ∈ (Numbers.encode n).map spellBlock, "па" ∉ block := by
    intro block mem
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp mem
    exact marker_not_in_block d (by decide) (by decide)
  simp only [spell, readRaw, List.splitOn_intercalate "па" noSeparator notEmpty,
    spelled_blocks_map, Option.map_some, Numbers.decode_encode]

theorem parse_spell (n : Nat) : parse (spell n) = some n := by
  simp [parse, read_raw_spell]

theorem spell_parse {tokens : List String} {n : Nat} (accepted : parse tokens = some n) :
    spell n = tokens := by
  cases h : readRaw tokens with
  | none => simp [parse, h] at accepted
  | some decoded =>
    by_cases same : spell decoded = tokens
    · simp [parse, h, same] at accepted
      simpa [accepted] using same
    · simp [parse, h, same] at accepted

theorem spell_injective : Function.Injective spell := by
  intro left right equal
  have parsed := congrArg parse equal
  simpa only [parse_spell, Option.some.injEq] using parsed

theorem spell_nonempty (n : Nat) : spell n ≠ [] := by
  intro empty
  have read := parse_spell n
  rw [empty] at read
  have zero : spell 0 = ["нэ"] := by
    unfold spell Numbers.encode
    rw [Numbers.encodeLowFirst]
    rfl
  change (if spell 0 = [] then some 0 else none) = some n at read
  simp [zero] at read

private theorem reserved_not_in_number (n : Nat) {token : String} (notZero : token ≠ "нэ")
    (notSeparator : token ≠ "па") (reserved : token ∈ ["па", "нэ", "ит", "тэл"]) :
    token ∉ spell n := by
  suffices ∀ blocks : List Nat, token ∉ ["па"].intercalate (blocks.map spellBlock) by
    exact this (Numbers.encode n)
  intro blocks
  induction blocks with
  | nil => simp
  | cons d rest ih =>
    have head := marker_not_in_block d notZero reserved
    cases rest with
    | nil => simpa using head
    | cons next tail =>
      simpa [List.intercalate_cons_cons, head, notSeparator] using ih

inductive Quantity where
  | cardinal (value : Nat)
  | ordinal (indexMinusOne : Nat)
  | fraction (numerator denominatorMinusOne : Nat)
  deriving BEq, DecidableEq, Repr

def spellQuantity : Quantity → List String
  | .cardinal n => spell n
  | .ordinal index => "ит" :: spell index.succ
  | .fraction numerator denominator => spell numerator ++ "тэл" :: spell denominator.succ

private def readQuantity (tokens : List String) : Option Quantity :=
  if tokens.head? == some "ит" then do
    match ← readRaw tokens.tail with
    | 0 => none
    | index + 1 => some (.ordinal index)
  else
    match tokens.splitOn "тэл" with
    | [whole] => (readRaw whole).map Quantity.cardinal
    | [numerator, denominator] => do
      let numerator ← readRaw numerator
      match ← readRaw denominator with
      | 0 => none
      | denominator + 1 => some (.fraction numerator denominator)
    | _ => none

private theorem head_not_reserved {tokens : List String} {token : String} (absent : token ∉ tokens) :
    (tokens.head? == some token) = false := by
  cases tokens with
  | nil => rfl
  | cons head tail =>
    have ne : head ≠ token := fun eq => absent (by simp [eq])
    simp [ne]

private theorem read_spell_quantity (quantity : Quantity) :
    readQuantity (spellQuantity quantity) = some quantity := by
  have noIt (n : Nat) : "ит" ∉ spell n := reserved_not_in_number n (by decide) (by decide) (by decide)
  have noTel (n : Nat) : "тэл" ∉ spell n := reserved_not_in_number n (by decide) (by decide) (by decide)
  cases quantity with
  | cardinal n =>
    simp [spellQuantity, readQuantity, head_not_reserved (noIt n),
      List.splitOn_eq_singleton (noTel n), read_raw_spell]
  | ordinal index =>
    simp [spellQuantity, readQuantity, read_raw_spell]
  | fraction numerator denominator =>
    have absent : "ит" ∉ spell numerator ++ "тэл" :: spell denominator.succ := by
      simp [noIt]
    unfold spellQuantity readQuantity
    rw [head_not_reserved absent]
    simp [List.splitOn_append_cons_self_of_not_mem (noTel numerator),
      List.splitOn_eq_singleton (noTel denominator.succ), read_raw_spell]

def parseQuantity (tokens : List String) : Option Quantity := do
  let quantity ← readQuantity tokens
  if spellQuantity quantity = tokens then some quantity else none

theorem parse_spell_quantity (quantity : Quantity) :
    parseQuantity (spellQuantity quantity) = some quantity := by
  simp [parseQuantity, read_spell_quantity]

theorem spell_parse_quantity {tokens : List String} {quantity : Quantity}
    (accepted : parseQuantity tokens = some quantity) : spellQuantity quantity = tokens := by
  obtain ⟨decoded, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted <;> simp_all

theorem spell_quantity_injective : Function.Injective spellQuantity := by
  intro left right equal
  have parsed := congrArg parseQuantity equal
  simpa only [parse_spell_quantity, Option.some.injEq] using parsed

#guard spell 24005 == ["китики", "отик", "ото"]
#guard parse ["кати", "па", "нэ", "па", "кити"] == some 100000000000002
#guard parse ["кати", "катим"] == none
#guard parse ["катим", "катим"] == none
#guard parse ["нэ", "па", "кати"] == none
#guard parse ["кати", "па", "па", "кити"] == none
#guard parseQuantity ["ит", "кати", "па", "кити"] == some (.ordinal 10000001)
#guard parseQuantity ["кати", "тэл", "кити"] == some (.fraction 1 1)
#guard parseQuantity ["ит", "нэ"] == none
#guard parseQuantity ["кати", "тэл", "нэ"] == none
#guard parseQuantity ["кати", "тэл", "кити", "тэл", "коти"] == none
#guard parseQuantity ["ит", "кати", "катим"] == none
#guard parseQuantity ["тэл", "кити"] == none

end Laiu.NumberWords
