import Laiu.Logic
import Laiu.Phonology

namespace Laiu.Shortening

def negateTimes : Nat → Bool → Bool
  | 0, truth => truth
  | n + 1, truth => !(negateTimes n truth)

private theorem negate_two_more (n : Nat) (truth : Bool) :
    negateTimes (n + 2) truth = negateTimes n truth := by
  simp only [negateTimes, Bool.not_not]

theorem keep_only_negation_parity (n : Nat) (truth : Bool) :
    negateTimes (n % 2) truth = negateTimes n truth := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        change negateTimes ((n + 2) % 2) truth = negateTimes (n + 2) truth
        rw [show (n + 2) % 2 = n % 2 by omega, negate_two_more]
        exact ih n (by omega)

def renderNegation (n : Nat) (body : List String) : List String :=
  List.replicate n "ли" ++ body

theorem shorten_negation (n : Nat) (truth : Bool) (body : List String) :
    negateTimes (n % 2) truth = negateTimes n truth ∧
      (renderNegation (n % 2) body).length + 2 * (n / 2) = (renderNegation n body).length := by
  refine ⟨keep_only_negation_parity n truth, ?_⟩
  simp only [renderNegation, List.length_append, List.length_replicate]
  omega

theorem shortest_negation_stack (n m : Nat) (body : List String)
    (same : ∀ truth, negateTimes n truth = negateTimes m truth) :
    (renderNegation (n % 2) body).length ≤ (renderNegation m body).length := by
  have sameParity : n % 2 = m % 2 := by
    have h := same true
    rw [← keep_only_negation_parity n true, ← keep_only_negation_parity m true] at h
    have left : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have right : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases left with left | left <;> rcases right with right | right <;>
      simp [left, right, negateTimes] at h ⊢
  simpa [renderNegation, sameParity] using Nat.add_le_add_right (Nat.mod_le m 2) body.length

inductive Join where
  | all | any

def Join.connector : Join → Logic.Connector
  | .all => .all
  | .any => .any

def Join.word (join : Join) : String := join.connector.word

def Join.eval (join : Join) : List Bool → Bool := join.connector.eval

/-- In a homogeneous chain, evaluation is independent of nested grouping. -/
theorem flatten_truth (join : Join) (before inner after : List Bool) :
    join.eval (before ++ [join.eval inner] ++ after) = join.eval (before ++ inner ++ after) := by
  cases join <;> simp [Join.eval, Join.connector, Logic.Connector.eval]

def renderChain (join : Join) (operands : List (List String)) : List String :=
  [join.word].intercalate operands

private theorem chain_length (join : Join) (operands : List (List String)) :
    (renderChain join operands).length = (operands.map List.length).sum + (operands.length - 1) := by
  induction operands with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => simp [renderChain]
    | cons next tail =>
      unfold renderChain at ih ⊢
      rw [List.intercalate_cons_cons]
      simp only [List.length_append, List.length_cons, List.length_nil, List.map_cons, List.sum_cons] at ih ⊢
      omega

private def framed (words : List String) : List String := ["тэ"] ++ words ++ ["эт"]

/-- Dropping one redundant group removes exactly the two frame markers. -/
theorem flatten_length (join : Join) (before inner after : List (List String)) (nonempty : inner ≠ []) :
    (renderChain join (before ++ inner ++ after)).length + 2 =
      (renderChain join (before ++ [framed (renderChain join inner)] ++ after)).length := by
  have positive : 0 < inner.length := List.length_pos_iff.mpr nonempty
  rw [chain_length, chain_length]
  simp only [List.map_append, List.sum_append, List.length_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, framed]
  rw [chain_length]
  omega

/-- Each ordinary operand carries its own spelling and truth value. -/
theorem shorten_homogeneous_chain (join : Join) (before inner after : List (List String × Bool))
    (nonempty : inner ≠ []) :
    join.eval (before.map Prod.snd ++ [join.eval (inner.map Prod.snd)] ++ after.map Prod.snd) =
      join.eval ((before ++ inner ++ after).map Prod.snd) ∧
    (renderChain join ((before ++ inner ++ after).map Prod.fst)).length + 2 =
      (renderChain join (before.map Prod.fst ++
        [framed (renderChain join (inner.map Prod.fst))] ++ after.map Prod.fst)).length := by
  simp only [List.map_append]
  exact ⟨flatten_truth join _ _ _, flatten_length join _ _ _ (by simpa using nonempty)⟩

theorem exclusive_frame_can_change_result :
    Logic.Connector.one.eval [true, Logic.Connector.one.eval [true, true]] ≠
      Logic.Connector.one.eval [true, true, true] := by
  decide

theorem choice_connectors_have_two_open_syllables :
    [Logic.Connector.any, Logic.Connector.one].all (fun connector =>
      Phonology.syllableCount connector.word == 2 && Phonology.closedSyllableCount connector.word == 0) = true := by
  decide

theorem choice_connectors_differ_in_context (left right : String) :
    Phonology.withoutVowelLength (left ++ Logic.Connector.any.word ++ right) ≠
      Phonology.withoutVowelLength (left ++ Logic.Connector.one.word ++ right) := by
  intro same
  have count := congrArg (fun text : String => (text.toList.filter (!Phonology.isVowel ·)).length) same
  rw [Phonology.duration_loss_preserves_consonants, Phonology.duration_loss_preserves_consonants] at count
  simp [Logic.Connector.word, String.toList_append, Phonology.isVowel, Lexicon.vowels] at count

example : renderNegation (2 % 2) ["ки"] = ["ки"] := rfl
example : renderChain .all [["а", "ки"], ["у", "но"], ["о", "мит"]] =
    ["а", "ки", "на", "у", "но", "на", "о", "мит"] := rfl
example : renderChain .all [["а", "ки"], framed (renderChain .all [["у", "но"], ["о", "мит"]])] =
    ["а", "ки", "на", "тэ", "у", "но", "на", "о", "мит", "эт"] := rfl

end Laiu.Shortening
