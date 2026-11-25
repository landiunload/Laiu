import Laiu.Logic
import Laiu.NumberWords

namespace Laiu.References

/-- Depth zero in the model is the nearest frame, written as depth one in Laiu. -/
def spell (depth : Nat) : List String :=
  "тэр" :: (if depth = 0 then [] else NumberWords.spell depth.succ)

def parse : List String → Option Nat
  | ["тэр"] => some 0
  | "тэр" :: number => do
    match ← NumberWords.parse number with
    | 0 => none
    | depth + 1 => some depth
  | _ => none

private theorem parse_number {head : String} {tail : List String} {depth : Nat}
    (read : NumberWords.parse (head :: tail) = some depth.succ) :
    parse ("тэр" :: head :: tail) = some depth := by
  simp [parse, read]

theorem parse_spell (depth : Nat) : parse (spell depth) = some depth := by
  by_cases nearest : depth = 0
  · subst depth
    rfl
  · simp only [spell, ite_eq_right nearest]
    cases written : NumberWords.spell depth.succ with
    | nil => exact False.elim (NumberWords.spell_nonempty _ written)
    | cons head tail =>
      apply parse_number
      rw [← written, NumberWords.parse_spell]

theorem normalize_parsed {tokens : List String} {depth : Nat} (accepted : parse tokens = some depth) :
    tokens = spell depth ∨ (depth = 0 ∧ tokens = "тэр" :: NumberWords.spell 1) := by
  unfold parse at accepted
  split at accepted
  · cases accepted
    exact Or.inl rfl
  · rename_i number _
    obtain ⟨n, read, tail⟩ := Option.bind_eq_some_iff.mp accepted
    cases n with
    | zero => contradiction
    | succ n =>
      have same : n = depth := Option.some.inj tail
      subst depth
      have form := NumberWords.spell_parse read
      by_cases nearest : n = 0
      · subst n
        exact Or.inr ⟨rfl, congrArg ("тэр" :: ·) form.symm⟩
      · exact Or.inl (by simp [spell, nearest, form])
  · contradiction

theorem spell_minimal {tokens : List String} {depth : Nat} (accepted : parse tokens = some depth) :
    (spell depth).length ≤ tokens.length := by
  rcases normalize_parsed accepted with same | ⟨rfl, rfl⟩
  · simp [same]
  · simp [spell]

inductive Frame (α : Type _) where
  | relative (referent : α)
  | content

def relativeScopes {α : Type _} (frames : List (Frame α)) : List α :=
  frames.filterMap fun frame => match frame with
    | .relative referent => some referent
    | .content => none

def resolve {α : Type _} (frames : List (Frame α)) (tokens : List String) : Option α :=
  (parse tokens).bind fun depth => Logic.resolveRelative (relativeScopes frames) depth.succ

theorem content_preserves_referent {α : Type _} (before after : List (Frame α)) (tokens : List String) :
    resolve (before ++ .content :: after) tokens = resolve (before ++ after) tokens := by
  simp [resolve, relativeScopes, List.filterMap_append]

theorem resolvable_at_available_depth {α : Type _} (frames : List (Frame α)) (depth : Nat) :
    (resolve frames (spell depth)).isSome = true ↔ depth < (relativeScopes frames).length := by
  unfold resolve
  rw [parse_spell]
  change (Logic.resolveRelative (relativeScopes frames) (depth + 1)).isSome = true ↔ _
  rw [Logic.relative_is_available_iff]
  omega

#guard parse ["тэр", "кати"] == some 0
#guard parse ["тэр", "нэ"] == none
#guard parse ["тэр", "кати", "катим"] == none
#guard resolve [.relative "ребёнок", .content, .relative "взрослый"] ["тэр", "кити"] == some "взрослый"
#guard resolve [.relative "ребёнок", .content] ["тэр", "кити"] == none

end Laiu.References
