import «Misc».Logic.Bool.Utils

/-- A symbol of arity `n`. -/
structure Symbol (n : ℕ) where
  repr : String
  fn : Vec n Bool → Bool

/--
  The signature (symbols) of a propositional language.

  This is modeled as a family of sets of functions with different arities.
  Constants are `Signature.symbols 0`.

  Notice that signatures need not be finite.
-/
structure Signature where
  /-- Symbols with arity `n`. -/
  symbols : (n : ℕ) → Set (Symbol n)

/-- Constructs signatures with symbols of arity `1` and `2`. -/
def Signature.mk₁₂ (u : Set (Symbol 1)) (b : Set (Symbol 2)) :=
  Signature.mk (fun
    | 1 => u
    | 2 => b
    | _ => ∅
  )

/--
  Formulas for a given signature with at most `n` unbound variables.
-/
inductive Signature.Formula {S : Signature} (n : ℕ) where
  /-- Unbound variables. -/
  | var : (Fin n) → S.Formula n
  /-- Application. Constants are applications of arity `0`. -/
  | apply : (f : _) → (f ∈ S.symbols a) → Vec a (S.Formula n) → S.Formula n

/--
  Sentences for a given signature are formulas with no unbound variables.
-/
def Signature.Sentence {S : Signature} := S.Formula 0

/--
  The _valuation_ of a formula is the boolean function it represents.
-/
def Signature.Formula.value {S : Signature} {φ : S.Formula n} (vars : Vec n Bool) : Bool :=
  match φ with
  | var i => vars i
  | apply f _ ψs => f.2 (fun i => (ψs i).value vars)

/-- Renders a formula to a string. -/
instance {S : Signature} : ToString (S.Formula n) :=
  let rec toString (φ : S.Formula n) : String :=
    match φ with
    | Signature.Formula.var i => s!"x_{i}"
    | @Signature.Formula.apply _ _ a f _ ψs =>
      match a with
      -- constants are just the symbols
      | 0 => s!"{f.1}"
      -- unary operators do not surround their arguments
      | 1 => s!"{f.1}{toString (ψs 0)}"
      -- operators of arity `n > 1` surround their arguments in brackets (`[]`)
      | k+2 =>
        have a_pos : k+2 > 0 := by simp only [gt_iff_lt, add_pos_iff, or_true]
        let params := (List.range (k+2)).map (fun i => toString (ψs (@Fin.ofNat' (k+2) i a_pos)))
        s!"{f.1}{params}"
  
  ⟨toString⟩
