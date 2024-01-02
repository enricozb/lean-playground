import «Misc».Logic.Bool.Utils

namespace Logic

/-- A symbol of arity `n`. -/
structure Symbol (n : ℕ) where
  repr : String
  fn : [Bool; n] → Bool

/--
  The signature (symbols) of a propositional language.

  This is modeled as a family of sets of functions with different arities.
  Constants are `Signature.symbols 0`.

  Notice that signatures need not be finite.
-/
structure Signature where
  /-- Symbols with arity `n`. -/
  symbols : (n : ℕ) → Set (Symbol n)

/-- A signature of a single symbol. -/
@[simp]
def Signature.singleton (s : Symbol n) : Signature := ⟨
  fun a => 
    if h : a = n then
      by rw [h]; exact Set.singleton s
    else
      ∅
⟩

/-- A signature of a single symbol for every arity. -/
@[simp]
def Signature.singleton' (f : (n : ℕ) → Symbol n) : Signature := ⟨fun a => {f a}⟩

/-- Creates a new signature by inserting a symbol. -/
@[simp]
def Signature.insert (s : Symbol n) (S : Signature) : Signature := ⟨
  fun a =>
    if h : a = n then
      by rw [h]; exact (S.symbols n).insert s
    else
      S.symbols a
⟩

/-- Creates a new signature by inserting a symbol for every arity. -/
@[simp]
def Signature.insert' (f : (n : ℕ) → Symbol n) (S : Signature) : Signature := ⟨
  fun a => (S.symbols a).insert (f a)
⟩

@[simp]
def Signature.union (S₁ S₂ : Signature) : Signature := ⟨
  fun a => S₁.symbols a ∪ S₂.symbols a
⟩

instance : Union Signature := ⟨Signature.union⟩

/-- Parser for constructing a signature of symbols of a single arity. -/
syntax (priority := high) "⟪" term,+ "⟫" : term
/-- Parser for constructing a signature of symbols of any arity. -/
syntax (priority := high) "⟪" term,+ "⟫ₙ" : term

/- Declares two expansions/syntax transformers -/
macro_rules
  | `(⟪$x⟫) => `(Signature.singleton $x)
  | `(⟪$x, $xs:term,*⟫) => `(Signature.insert $x ⟪$xs,*⟫)
  | `(⟪$x⟫ₙ) => `(Signature.singleton' $x)
  | `(⟪$x, $xs:term,*⟫ₙ) => `(Signature.insert' $x ⟪$xs,*⟫ₙ)

-- def sig_noa : Signature := ⟪(¬)⟫ ∪ ⟪(∧), (∨)⟫ ∪ ⟪(⋁), (⋀)⟫ₙ

/--
  Formulas for a given signature with at most `n` unbound variables.
-/
inductive Signature.Formula {S : Signature} (n : ℕ) where
  /-- Unbound variables. -/
  | var : (Fin n) → S.Formula n
  /-- Application. Constants are applications of arity `0`. -/
  | apply : (f : _) → (f ∈ S.symbols a) → [S.Formula n; a] → S.Formula n

/--
  Sentences for a given signature are formulas with no unbound variables.
-/
def Signature.Sentence {S : Signature} := S.Formula 0

/--
  The _valuation_ of a formula is the boolean function it represents.
-/
def Signature.Formula.value {S : Signature} {φ : S.Formula n} (vars : [Bool; n]) : Bool :=
  match φ with
  | var i => vars i
  | apply f _ ψs => f.2 (fun i => (ψs i).value vars)

/--
  Composes a formula of `n` variables and a vector of `n` formulas.

  Specifically, if `φ(b 1, .., b n)` and `ψs : Vec n (Formula m)`, `compose`
  replaces every occurence of `b i` with `ψs i`.
-/
def Signature.Formula.compose {S : Signature} (φ : S.Formula n) (ψs : [S.Formula m; n]) : S.Formula m :=
  match φ with
  | var i => ψs i
  | apply f hf ψs' => apply f hf (fun i => (ψs' i).compose ψs)

/-- Renders a formula to a strin g. -/
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

end Logic
