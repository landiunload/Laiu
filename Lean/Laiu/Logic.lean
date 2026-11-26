import Std

namespace Laiu.Logic

/- Exclusive choice counts selections in the entire list. A grouped operand may itself
   be the result of an independent exclusive choice. -/

def countTrue : List Bool → Nat
  | [] => 0
  | false :: rest => countTrue rest
  | true :: rest => (countTrue rest).succ

def noneChosen : List Bool → Bool
  | [] => true
  | false :: rest => noneChosen rest
  | true :: _ => false

def exactlyOne : List Bool → Bool
  | [] => false
  | false :: rest => exactlyOne rest
  | true :: rest => noneChosen rest

theorem noneChosen_iff_count (choices : List Bool) :
    noneChosen choices = true ↔ countTrue choices = 0 := by
  induction choices with
  | nil => simp [noneChosen, countTrue]
  | cons choice rest ih =>
    cases choice with
    | false => simpa only [noneChosen, countTrue] using ih
    | true => simp [noneChosen, countTrue]

theorem exactlyOne_iff_count (choices : List Bool) :
    exactlyOne choices = true ↔ countTrue choices = 1 := by
  induction choices with
  | nil => simp [exactlyOne, countTrue]
  | cons choice rest ih =>
    cases choice with
    | false => simpa only [exactlyOne, countTrue] using ih
    | true => simp [exactlyOne, countTrue, noneChosen_iff_count]

theorem countTrue_append (left right : List Bool) :
    countTrue (left ++ right) = countTrue left + countTrue right := by
  induction left with
  | nil => simp [countTrue]
  | cons choice rest ih =>
    cases choice <;> simp [countTrue, ih, Nat.succ_add]

theorem exactlyOne_append_iff (left right : List Bool) :
    exactlyOne (left ++ right) = true ↔
      (exactlyOne left = true ∧ noneChosen right = true) ∨
      (noneChosen left = true ∧ exactlyOne right = true) := by
  simp only [exactlyOne_iff_count, countTrue_append, noneChosen_iff_count]
  omega

def binaryXor (left right : Bool) : Bool :=
  if left then !right else right

theorem flat_choice_differs_from_repeated_binary_xor :
    exactlyOne [true, true, true] ≠ binaryXor (binaryXor true true) true := by
  decide

/- Only relative frames are numbered. The caller supplies the stack
   with the innermost relative frame first. Depth zero never denotes a frame. -/

def resolveRelative {α : Type _} : List α → Nat → Option α
  | _, 0 => none
  | [], _ => none
  | referent :: _, 1 => some referent
  | _ :: outer, depth + 2 => resolveRelative outer (depth + 1)

theorem relative_is_available_iff {α : Type _} (scopes : List α) (depth : Nat) :
    (resolveRelative scopes depth).isSome = true ↔ 0 < depth ∧ depth ≤ scopes.length := by
  induction scopes generalizing depth with
  | nil =>
    cases depth <;> simp [resolveRelative]
  | cons referent outer ih =>
    cases depth with
    | zero => simp [resolveRelative]
    | succ depth =>
      cases depth with
      | zero => simp [resolveRelative]
      | succ depth =>
        change (resolveRelative outer (depth + 1)).isSome = true ↔
          0 < depth + 2 ∧ depth + 2 ≤ (referent :: outer).length
        rw [ih]
        simp only [List.length_cons]
        omega

theorem adding_inner_frames_preserves_outer_referent
    {α : Type _} (inner outer : List α) (depth : Nat) (positive : 0 < depth) :
    resolveRelative (inner ++ outer) (depth + inner.length) = resolveRelative outer depth := by
  induction inner with
  | nil => simp
  | cons head rest ih =>
    have indexPositive : 0 < depth + rest.length := by omega
    have skip (index : Nat) (nonzero : 0 < index) :
        resolveRelative (head :: (rest ++ outer)) index.succ =
          resolveRelative (rest ++ outer) index := by
      cases index with
      | zero => omega
      | succ index => rfl
    simpa only [List.cons_append, List.length_cons, Nat.add_succ] using
      (skip (depth + rest.length) indexPositive).trans ih

def resolveWrittenRelative {α : Type _} (scopes : List α) (depth : Option Nat) : Option α :=
  resolveRelative scopes (depth.getD 1)

theorem omitted_and_explicit_nearest_select_same_frame {α : Type _}
    (scopes : List α) :
    resolveWrittenRelative scopes none = resolveWrittenRelative scopes (some 1) := rfl

/- Tense rules distinguish an independently anchored clause from a subjectless
   dependent action list. Explicit action times are local to that action. -/

inductive Tense where
  | past
  | present
  | future
  deriving DecidableEq, Repr

inductive FrameAnchor where
  | dependent
  | independent (firstVerbTime : Option Tense)
  deriving DecidableEq, Repr

def inheritedTense (parent : Tense) : FrameAnchor → Tense
  | .dependent => parent
  | .independent first => first.getD .present

/-- The particle and adverb constrain the same event time. Use the context only when neither specifies it. -/
def resolveTense (fallback : Tense) (particle adverb : Option Tense) : Option Tense :=
  match particle, adverb with
  | some written, some fixed => if written = fixed then some fixed else none
  | some written, none => some written
  | none, fixed => some (fixed.getD fallback)

theorem resolved_without_fixed_adverb (fallback : Tense) (particle : Option Tense) :
    resolveTense fallback particle none = some (particle.getD fallback) := by
  cases particle <;> rfl

theorem matching_particle_is_redundant (fallback fixed : Tense) :
    resolveTense fallback (some fixed) (some fixed) = resolveTense fallback none (some fixed) := by
  simp [resolveTense]

theorem conflicting_time_fails (fallback particle adverb : Tense) (different : particle ≠ adverb) :
    resolveTense fallback (some particle) (some adverb) = none := by
  simp [resolveTense, different]

def actionTenses (parent : Tense) (anchor : FrameAnchor) :
    List (Option Tense) → List Tense :=
  List.map (fun written => written.getD (inheritedTense parent anchor))

def actionTensesWithAdverbs (parent : Tense) (anchor : FrameAnchor)
    (actions : List (Option Tense × Option Tense)) : Option (List Tense) :=
  actions.mapM fun (particle, adverb) => resolveTense (inheritedTense parent anchor) particle adverb

theorem fixed_adverb_acts_like_local_particle (parent fixed : Tense) (anchor : FrameAnchor)
    (before after : List (Option Tense × Option Tense)) :
    actionTensesWithAdverbs parent anchor (before ++ (none, some fixed) :: after) =
      actionTensesWithAdverbs parent anchor (before ++ (some fixed, none) :: after) := by
  simp [actionTensesWithAdverbs, List.mapM_append, resolveTense]

theorem override_stays_local (parent explicit : Tense) (anchor : FrameAnchor)
    (before after : List (Option Tense)) :
    actionTenses parent anchor (before ++ (some explicit :: after)) =
      actionTenses parent anchor before ++ (explicit :: actionTenses parent anchor after) := by
  simp [actionTenses, List.map_append]

theorem every_unmarked_dependent_action_inherits (parent : Tense) (count : Nat) :
    actionTenses parent .dependent (List.replicate count none) =
      List.replicate count parent := by
  simp [actionTenses, inheritedTense]

theorem independent_clause_ignores_each_parent (left right : Tense) (first : Option Tense)
    (actions : List (Option Tense)) :
    actionTenses left (.independent first) actions =
      actionTenses right (.independent first) actions := by
  simp [actionTenses, inheritedTense]

theorem omitting_matching_particle_preserves_dependent_times (fallback fixed : Tense)
    (actions : List (Option Tense)) :
    (resolveTense fallback (some fixed) (some fixed)).map (fun time => actionTenses time .dependent actions) =
      (resolveTense fallback none (some fixed)).map (fun time => actionTenses time .dependent actions) := by
  rw [matching_particle_is_redundant]

example :
    actionTenses .past .dependent [none, some .present, none] =
      [.past, .present, .past] := by
  decide

example : actionTensesWithAdverbs .past .dependent [(none, none), (none, some .present)] =
    some [.past, .present] := by decide

example :
    actionTenses .past (.independent none) [none] = [.present] := by
  decide

/- The rules distinguish denial of a quantifier from denying the predicate of
   each entity. These laws use classical interpretation and the given domain. -/

theorem all_not_iff_not_some {α : Type _} (predicate : α → Prop) :
    (∀ entity, ¬ predicate entity) ↔ ¬ ∃ entity, predicate entity := by
  constructor
  · intro allNot existsSome
    obtain ⟨entity, holds⟩ := existsSome
    exact allNot entity holds
  · intro notSome entity holds
    exact notSome ⟨entity, holds⟩

theorem not_all_iff_some_not {α : Type _} (predicate : α → Prop) :
    (¬ ∀ entity, predicate entity) ↔ ∃ entity, ¬ predicate entity := by
  constructor
  · intro notAll
    apply Classical.byContradiction
    intro noCounterexample
    apply notAll
    intro entity
    exact Classical.byContradiction (fun fails => noCounterexample ⟨entity, fails⟩)
  · intro counterexample all
    obtain ⟨entity, fails⟩ := counterexample
    exact fails (all entity)

theorem not_all_does_not_entail_all_not :
    (¬ ∀ entity : Bool, entity = true) ∧ ¬ (∀ entity : Bool, ¬ entity = true) := by
  constructor
  · intro all
    have impossible := all false
    cases impossible
  · intro allNot
    exact allNot true rfl

/-- An action may apply to a single participant or to a group of participants. -/
abbrev Group (α : Type _) := α → Prop

def individually {α : Type _} (people : Group α) (acts : Group α → Prop) : Prop :=
  ∀ person, people person → acts (fun other => other = person)

def together {α : Type _} (people : Group α) (acts : Group α → Prop) : Prop :=
  acts people

/-- Bare ам requires coverage of the domain. The witnessing group may vary by participant. -/
def allParticipate {α : Type _} (people : Group α) (acts : Group α → Prop) : Prop :=
  ∀ person, people person → ∃ group, (∀ other, group other → people other) ∧ group person ∧ acts group

theorem individually_entails_all_participate {α : Type _} {people : Group α} {acts : Group α → Prop}
    (separate : individually people acts) : allParticipate people acts := by
  intro person included
  exact ⟨(· = person), fun _ eq => eq ▸ included, rfl, separate person included⟩

theorem together_entails_all_participate {α : Type _} {people : Group α} {acts : Group α → Prop}
    (joint : together people acts) : allParticipate people acts := by
  intro person included
  exact ⟨people, fun _ member => member, included, joint⟩

private def mixedAction (group : Group (Fin 3)) : Prop :=
  (group 0 ∧ ¬ group 1 ∧ ¬ group 2) ∨ (¬ group 0 ∧ group 1 ∧ group 2)

/-- One person acts alone and the other two act together. Bare ам covers this case. -/
theorem mixed_participation_is_covered :
    allParticipate (fun _ => True) mixedAction ∧
    ¬ individually (fun _ => True) mixedAction ∧ ¬ together (fun _ => True) mixedAction := by
  refine ⟨?_, ?_, ?_⟩
  · intro person _
    by_cases zero : person = 0
    · exact ⟨(· = 0), fun _ _ => trivial, zero, Or.inl (by decide)⟩
    · exact ⟨(· ≠ 0), fun _ _ => trivial, zero, Or.inr (by decide)⟩
  · intro separate
    have action := separate 1 trivial
    simp [mixedAction] at action
  · simp [together, mixedAction]

theorem quantifier_swap_changes_meaning :
    (∀ person : Bool, ∃ other : Bool, person = other) ∧
    ¬ (∃ other : Bool, ∀ person : Bool, person = other) := by
  constructor
  · exact fun person => ⟨person, rfl⟩
  · intro shared
    obtain ⟨other, equal⟩ := shared
    have impossible := (equal false).trans (equal true).symm
    cases impossible

end Laiu.Logic
