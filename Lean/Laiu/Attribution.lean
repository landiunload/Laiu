import Laiu.Syntax

namespace Laiu.Attribution

inductive Stance where
  | plain | possible | impossible
  deriving BEq, DecidableEq, Repr

def Stance.words : Stance → List String
  | .plain => []
  | .possible => ["эли"]
  | .impossible => ["ли", "эли"]

/-- The source supplies the claim, including any uncertainty expressed in it. -/
structure Claim where
  source : Option Syntax.Person
  stance : Stance
  content : Syntax.Phrase
  deriving DecidableEq, Repr

def sourceWords : Option Syntax.Person → List String
  | none => []
  | some person => ["мэн", person.word, ","]

def render (claim : Claim) : List String :=
  sourceWords claim.source ++ claim.stance.words ++ Syntax.render claim.content

private def readContent (source : Option Syntax.Person) (words : List String) : Option Claim :=
  let (stance, content) :=
    if words.head? = some "эли" then (.possible, words.tail)
    else if words.head? = some "ли" ∧ words.tail.head? = some "эли" then (.impossible, words.drop 2)
    else (Stance.plain, words)
  (Syntax.parse content).map (fun clause => ⟨source, stance, clause⟩)

private def readClaim : List String → Option Claim
  | "мэн" :: person :: "," :: rest => do
    readContent (some (← Syntax.readPerson person)) rest
  | rest => readContent none rest

def parse (written : List String) : Option Claim := do
  let claim ← readClaim written
  if render claim = written then some claim else none

private theorem render_cons (content : Syntax.Phrase) :
    Syntax.render content = content.person.word :: (Syntax.render content).tail := by
  cases content
  rfl

private theorem read_rendered_content (source : Option Syntax.Person) (stance : Stance)
    (content : Syntax.Phrase) :
    readContent source (stance.words ++ Syntax.render content) = some ⟨source, stance, content⟩ := by
  cases stance with
  | plain =>
    simp only [Stance.words, List.nil_append]
    have parsed := Syntax.parse_render content
    rw [render_cons content] at parsed ⊢
    cases person : content.person <;>
      simp only [person, Syntax.Person.word] at parsed ⊢ <;>
      simp [readContent, parsed]
  | possible => simp [Stance.words, readContent, Syntax.parse_render]
  | impossible => simp [Stance.words, readContent, Syntax.parse_render]

theorem parse_render (claim : Claim) : parse (render claim) = some claim := by
  rcases claim with ⟨source, stance, content⟩
  have decoded : readClaim (render ⟨source, stance, content⟩) = some ⟨source, stance, content⟩ := by
    cases source with
    | none =>
      cases stance with
      | plain =>
        simp only [render, sourceWords, Stance.words, List.nil_append]
        have parsed := read_rendered_content none .plain content
        simp only [Stance.words, List.nil_append] at parsed
        rw [render_cons content] at parsed ⊢
        cases person : content.person <;>
          simp only [person, Syntax.Person.word] at parsed ⊢ <;>
          exact parsed
      | possible => simpa [render, sourceWords, Stance.words, readClaim] using
          read_rendered_content none .possible content
      | impossible => simpa [render, sourceWords, Stance.words, readClaim] using
          read_rendered_content none .impossible content
    | some person => simpa [render, sourceWords, readClaim, Syntax.readPerson_word, List.append_assoc] using
        read_rendered_content (some person) stance content
  simp [parse, decoded]

theorem render_parse {written : List String} {claim : Claim} (accepted : parse written = some claim) :
    render claim = written := by
  obtain ⟨decoded, _, result⟩ := Option.bind_eq_some_iff.mp accepted
  split at result <;> simp_all

theorem same_writing_same_claim {first second : Claim} (written : render first = render second) :
    first = second := by
  have parsed := congrArg parse written
  simpa [parse_render] using parsed

def wordCount (written : List String) : Nat := (written.filter (· != ",")).length

theorem naming_source_adds_two_words (source : Syntax.Person) (stance : Stance) (content : Syntax.Phrase) :
    wordCount (render ⟨some source, stance, content⟩) = wordCount (render ⟨none, stance, content⟩) + 2 := by
  cases source <;> simp [wordCount, render, sourceWords, Syntax.Person.word] <;> omega

example : (parse ["мэн", "о", ",", "эли", "у", "ки", "лу"]).map (·.stance) = some .possible := by decide
example : (parse ["мэн", "о", ",", "у", "ли", "ки", "лу"]).map (·.content.negative) = some true := by decide
example : (parse ["мэн", "о", ",", "у", "ки", "лу", "эн", "тив"]).map (·.content.spatial) =
    some (some (.source, .garden)) := by decide
example : parse ["мэн", "о", "у", "ки", "лу"] = none := by decide
example : parse ["эли", "мэн", "о", ",", "у", "ки", "лу"] = none := by decide
example : parse ["мэн", "о", ",", "а", "ки", "лу", "эм"] = none := by decide
example : parse ["эн", "о", ",", "у", "ки", "лу"] = none := by decide

end Laiu.Attribution
