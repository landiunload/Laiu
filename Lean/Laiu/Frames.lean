import Std

namespace Laiu.Frames

structure Word where
  token : String
  ordinary : token ≠ "тэ" ∧ token ≠ "эт"

/-- A sequence of tokens or nested frames. This records boundaries, independent of grammatical roles. -/
inductive Segment where
  | empty
  | word (value : Word) (rest : Segment)
  | frame (inside rest : Segment)

def render : Segment → List String
  | .empty => []
  | .word word rest => word.token :: render rest
  | .frame inside rest => "тэ" :: (render inside ++ "эт" :: render rest)

private def append (right : Segment) : Segment → Segment
  | .empty => right
  | .word word rest => .word word (append right rest)
  | .frame inside rest => .frame inside (append right rest)

private theorem append_empty (segment : Segment) : append .empty segment = segment := by
  induction segment with
  | empty => rfl
  | word _ _ ih => simp [append, ih]
  | frame _ _ _ ih => simp [append, ih]

private abbrev State := Segment × List Segment

private def step (token : String) : Option State → Option State
  | none => none
  | some (current, outer) =>
    if close : token = "эт" then some (.empty, current :: outer)
    else if openFrame : token = "тэ" then
      match outer with
      | [] => none
      | resumed :: tail => some (.frame current resumed, tail)
    else some (.word ⟨token, openFrame, close⟩ current, outer)

private def scan (tokens : List String) (state : Option State) : Option State :=
  tokens.foldr step state

def parse (tokens : List String) : Option Segment :=
  match scan tokens (some (.empty, [])) with
  | some (segment, []) => some segment
  | _ => none

private theorem scan_append (left right : List String) (state : Option State) :
    scan (left ++ right) state = scan left (scan right state) := by
  simp [scan, List.foldr_append]

private theorem scan_render (segment endOfSequence : Segment) (outer : List Segment) :
    scan (render segment) (some (endOfSequence, outer)) = some (append endOfSequence segment, outer) := by
  induction segment generalizing endOfSequence outer with
  | empty => rfl
  | word word rest ih =>
    change step word.token (scan (render rest) _) = _
    rw [ih]
    simp [step, word.ordinary.1, word.ordinary.2, append]
  | frame inside rest innerIH restIH =>
    change step "тэ" (scan (render inside ++ "эт" :: render rest) _) = _
    rw [scan_append]
    change step "тэ" (scan (render inside) (step "эт" (scan (render rest) _))) = _
    rw [restIH]
    change step "тэ" (scan (render inside) (some (.empty, append endOfSequence rest :: outer))) = _
    rw [innerIH, append_empty]
    rfl

theorem parse_render (segment : Segment) : parse (render segment) = some segment := by
  simp [parse, scan_render, append_empty]

private def join (current : Segment) : List Segment → List String
  | [] => render current
  | next :: tail => render current ++ "эт" :: join next tail

private theorem step_rejoins {token : String} {state next : State} (read : step token (some state) = some next) :
    join next.1 next.2 = token :: join state.1 state.2 := by
  obtain ⟨current, outer⟩ := state
  by_cases closing : token = "эт"
  · subst token
    cases read
    rfl
  · by_cases opening : token = "тэ"
    · subst token
      cases outer with
      | nil => contradiction
      | cons resumed tail =>
        cases read
        cases tail <;> simp [join, render, List.append_assoc]
    · simp [step, closing, opening] at read
      subst next
      cases outer <;> rfl

private theorem scan_rejoins (tokens : List String) (start finish : State)
    (read : scan tokens (some start) = some finish) : join finish.1 finish.2 = tokens ++ join start.1 start.2 := by
  induction tokens generalizing finish with
  | nil =>
    change some start = some finish at read
    cases read
    rfl
  | cons first rest ih =>
    change step first (scan rest (some start)) = some finish at read
    cases suffix : scan rest (some start) with
    | none => rw [suffix] at read; contradiction
    | some state =>
      rw [suffix] at read
      rw [step_rejoins read, ih state suffix]
      rfl

theorem render_parse {tokens : List String} {segment : Segment} (read : parse tokens = some segment) :
    render segment = tokens := by
  unfold parse at read
  split at read
  · rename_i found scanned
    cases read
    simpa [join, render] using scan_rejoins tokens (.empty, []) (segment, []) scanned
  · contradiction

def balances (tokens : List String) : Bool := (parse tokens).isSome

#guard balances ["ир", "тэ", "тэр", "пи", "иру", "тэ", "тэр", "мил", "тэр", "кити", "эт", "эт"]
#guard !balances ["и", "та", "тэ", "а", "ки"]
#guard !balances ["и", "та", "эт", "а", "ки", "тэ"]

end Laiu.Frames
