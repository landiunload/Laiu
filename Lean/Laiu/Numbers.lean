import Std

namespace Laiu.Numbers

/- This module treats a numerical block as its value. Spelling each block
   using Laiu's digit words and rank suffixes is a separate lexical layer.
   Adjacent surface blocks have the reserved separator па. -/

def radix : Nat := 10000000

theorem radix_positive : 0 < radix := by decide

theorem quotient_lt (n : Nat) (large : ¬ n < radix) : n / radix < n := by
  have radixPos : 0 < radix := radix_positive
  have pos : 0 < n := by omega
  exact Nat.div_lt_self pos (by decide)

def encodeLowFirst (n : Nat) : List Nat :=
  if _large : ¬ n < radix then
    (n % radix) :: encodeLowFirst (n / radix)
  else
    [n]
termination_by n
decreasing_by exact quotient_lt n _large

def decodeLowFirst : List Nat → Nat
  | [] => 0
  | digit :: higher => digit + radix * decodeLowFirst higher

theorem decode_encode_low_first (n : Nat) :
    decodeLowFirst (encodeLowFirst n) = n := by
  refine Nat.strongRecOn n ?_
  intro value ih
  rw [encodeLowFirst]
  split
  · rename_i large
    rw [decodeLowFirst, ih (value / radix) (quotient_lt value large)]
    exact Nat.mod_add_div value radix
  · simp [decodeLowFirst]

inductive CanonicalLowFirst : List Nat → Prop
  | single {digit} : digit < radix → CanonicalLowFirst [digit]
  | more {digit higher} :
      digit < radix →
      0 < decodeLowFirst higher →
      CanonicalLowFirst higher →
      CanonicalLowFirst (digit :: higher)

theorem quotient_positive (n : Nat) (large : ¬ n < radix) : 0 < n / radix := by
  apply Nat.pos_of_ne_zero
  intro zero
  have decomposition := Nat.mod_add_div n radix
  rw [zero, Nat.mul_zero, Nat.add_zero] at decomposition
  have bounded := Nat.mod_lt n radix_positive
  omega

theorem encode_low_first_is_canonical (n : Nat) : CanonicalLowFirst (encodeLowFirst n) := by
  refine Nat.strongRecOn n ?_
  intro value ih
  rw [encodeLowFirst]
  split
  · rename_i large
    apply CanonicalLowFirst.more (Nat.mod_lt value radix_positive)
    · rw [decode_encode_low_first]
      exact quotient_positive value large
    · exact ih (value / radix) (quotient_lt value large)
  · rename_i small
    exact CanonicalLowFirst.single (by omega)

theorem canonical_blocks_bounded (blocks : List Nat)
    (canonical : CanonicalLowFirst blocks) :
    ∀ digit ∈ blocks, digit < radix := by
  induction canonical with
  | single bound =>
    intro digit mem
    simpa [List.eq_of_mem_singleton mem] using bound
  | more bound _ _ ih =>
    intro digit mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact bound
    · exact ih digit mem

theorem encode_decode_low_first (blocks : List Nat)
    (canonical : CanonicalLowFirst blocks) : encodeLowFirst (decodeLowFirst blocks) = blocks := by
  induction canonical with
  | @single digit bound =>
    rw [decodeLowFirst, decodeLowFirst, Nat.mul_zero, Nat.add_zero, encodeLowFirst]
    simp [bound]
  | @more digit higher bound positive _ ih =>
    rw [decodeLowFirst, encodeLowFirst]
    have radixLeProduct : radix ≤ radix * decodeLowFirst higher := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left radix positive
    have large : ¬ digit + radix * decodeLowFirst higher < radix := by
      omega
    have remainder : (digit + radix * decodeLowFirst higher) % radix = digit := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]
    have quotient : (digit + radix * decodeLowFirst higher) / radix = decodeLowFirst higher := by
      rw [Nat.add_mul_div_left _ _ radix_positive, Nat.div_eq_of_lt bound, Nat.zero_add]
    rw [dite_eq_left large, remainder, quotient, ih]

/- On the page, the leftmost block is the most significant. -/

def encode (n : Nat) : List Nat := (encodeLowFirst n).reverse

def decode (blocks : List Nat) : Nat := decodeLowFirst blocks.reverse

def Canonical (blocks : List Nat) : Prop := CanonicalLowFirst blocks.reverse

theorem decode_encode (n : Nat) : decode (encode n) = n := by
  simp [decode, encode, decode_encode_low_first]

theorem encode_is_canonical (n : Nat) : Canonical (encode n) := by
  simpa [Canonical, encode] using encode_low_first_is_canonical n

theorem encode_decode (blocks : List Nat) (canonical : Canonical blocks) :
    encode (decode blocks) = blocks := by
  unfold Canonical at canonical
  simp [encode, decode, encode_decode_low_first blocks.reverse canonical]

theorem encode_injective : Function.Injective encode := by
  intro a b same
  simpa only [decode_encode] using congrArg decode same

theorem encode_blocks_bounded (n digit : Nat) (mem : digit ∈ encode n) : digit < radix := by
  exact canonical_blocks_bounded _ (encode_low_first_is_canonical n) _ (by simpa [encode] using mem)

example : decode [0] = 0 := by decide
example : decode [1, 0, 2] = 100000000000002 := by decide
example : ¬ Canonical [0, 2] := by
  intro canonical
  change CanonicalLowFirst [2, 0] at canonical
  cases canonical with
  | more _ positive _ => simp [decodeLowFirst] at positive

end Laiu.Numbers
