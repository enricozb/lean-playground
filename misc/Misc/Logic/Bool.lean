import Mathlib.Init.Set
import Mathlib.Data.Nat.Basic

/--
  A macro definition of a vector, modeled as a `(Fin n → α)`.
  For some reason this doesn't work:
  ```
  def Vec (n : ℕ) (α : Type v) := Fin n → α
  ```
-/
macro_rules
| `( Vec $n $α ) => `( Fin $n → $α )

/--
  The signature of a propositional language. Specifically, the symbols
  (constants & functions) that generate a language.
  
  This modelling of a signature only accounts for functions of arity
  up to 3. This is because manipulating functions of variable arity
  requires a model of lists of fixed but arbitrary length. Fixing
  the function signatures in this way will hopefully simplify pattern
  matching and other tactics during proofs.
-/
structure Signature where
  constants : Set Prop
  unary : Set (Prop → Prop)
  binary : Set (Prop → Prop → Prop)
  ternary : Set (Prop → Prop → Prop → Prop)

/--
  Formulas for a given signature with at most `n` unbound variables.
-/
inductive Signature.Formula {S : Signature} (n : ℕ) where
  /-- Unbound variables. -/
  | var : (Fin n) → S.Formula n
  /-- Constant (prime) formulas. -/
  | const : (c : _) → (c ∈ S.constants) → S.Formula n
  | unary : (f : _) → (f ∈ S.unary) → S.Formula n → S.Formula n
  | binary : (f : _) → (f ∈ S.binary) → S.Formula n → S.Formula n → S.Formula n
  | ternary : (f : _) → (f ∈ S.ternary) → S.Formula n → S.Formula n → S.Formula n → S.Formula n

/--
  The _valuation_ of a formula, given the values of the variables.
-/
def Signature.Formula.value {S : Signature} {φ : S.Formula n} (vars : Vec n Prop) : Prop :=
  match φ with
  | var i => vars i
  | const c _ => c
  | unary f _ ψ₁ => f (ψ₁.value vars)
  | binary f _ ψ₁ ψ₂ => f (ψ₁.value vars) (ψ₂.value vars)
  | ternary f _ ψ₁ ψ₂ ψ₃ => f (ψ₁.value vars) (ψ₂.value vars) (ψ₃.value vars)

/--
  Sentences for a given signature are formulas with no unbound variables.
-/
def Signature.Sentence {S : Signature} := S.Formula 0

/--
  A signature is _functional complete_ if any function of any arity is representable by some formula.
-/
def Signature.functional_complete {S : Signature} : Prop :=
  ∀ {n} (f : Vec n Prop → Prop), ∃ (φ : S.Formula n), φ.value = f

def Signature.subset (S₁ S₂ : Signature) : Prop :=
  S₁.constants ⊆ S₂.constants ∧
  S₁.unary ⊆ S₂.unary ∧
  S₁.binary ⊆ S₂.binary ∧
  S₁.ternary ⊆ S₂.ternary  

theorem Signature.subset_functional_complete {S₁ S₂ : Signature} (hfc : S₁.functional_complete) (hs : S₁.subset S₂) :
  S₂.functional_complete := sorry

def sig_noa : Signature := ⟨∅, {(¬·)}, {(·∨·), (·∧·)}, ∅⟩
def sig_no : Signature := ⟨∅, {(¬·)}, {(·∨·)}, ∅⟩
def sig_na : Signature := ⟨∅, {(¬·)}, {(·∧·)}, ∅⟩

theorem sig_noa_functional_complete : sig_noa.functional_complete := sorry