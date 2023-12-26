/-
  An initial attempt at some exercises from
    A Concise Introduction to Mathematical Logic
    Springer; 3rd ed. 2010 edition (December 17, 2009)
    ISBN-10 : 1441912207

  I think the way I designed these structures isn't great, especially `Interpretation`.
  This makes it difficult to prove things about specific interpretations, so I'll just
  leave the file here as a learning.

  Resources:
    - https://github.com/leanprover-community/mathlib4/blob/de998ec5efecfd02da10d832018622a6488a6565//Mathlib/ModelTheory/Basic.lean#L60-L64
    - https://github.com/iehality/lean4-logic/
    - 

  Authors: Enrico Z. Borba
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import «Misc».Utils

section Utilities

/-- Converts a set to a type. -/
@[simp]
def asType {α : Type v} (s : Set α) : Type v := {a : α // a ∈ s}

/-- Syntax for sets as types. -/
syntax (priority := high) "⟦" term,* "⟧" : term

/-- Macro for sets as types. -/
macro_rules
| `( ⟦ ⟧ ) => `(PEmpty)
| `( ⟦ $xs:term,* ⟧ ) => `( asType { $xs:term,*} )

/--
  A macro definition of a vector, modeled as a `(Fin n → α)`.
  For some reason this doesn't work:
  ```
  def Vec (n : ℕ) (α : Type v) := Fin n → α
  ```
-/
macro_rules
| `( Vec $n $α ) => `( Fin $n → $α )

end Utilities

/--
  The signature of a propositional language. Specifically,
  the symbols (constants & functions) that generate a language.
-/
structure Signature where
  /-- Functions of any arity. Constants are `Signature.F 0`. -/
  Functions : (n : ℕ) → Type u

/-- The 0-arity symbols in a signature. -/
def Signature.Constants {S : Signature} := S.Functions 0

/-- A Signature of unary and binary functions. -/
@[simp]
def Signature.mk₁₂ (f₁ f₂ : Type u) : Signature := Signature.mk
  fun n => match n with
  | 1 => f₁
  | 2 => f₂
  | _ => PEmpty

/--
  Formulas for a given signature with at most `n` unbound variables.
-/
inductive Signature.Formula {S : Signature.{u}} (n : ℕ) : Type u where
  /-- Unbound variables. -/
  | var : (Fin n) → S.Formula n
  /-- Prime (constant) formulas. -/
  | const : S.Constants → S.Formula n
  /-- Composite formulas. -/
  | apply : (m : ℕ) → S.Functions m → Vec m (S.Formula n) → S.Formula n

/--
  Sentences for a given signature are formulas with no unbound variables.
-/
def Signature.Sentence {S : Signature.{u}} : Type u := S.Formula 0

/--
  An interpretation of a signature using a backing type `M`.
  For example, for propositional (boolean) formulas, `M = Prop`,
  and the interpretation would map each symbol to a function of
  the specified arity.

  Functions of arity `n` have type `(Fin n → M) → M`, where `(Fin n → M)`
  represents an `n`-tuple.

  This is called a _structure_ or a _valuation_, depending on
  the literature.
-/
structure Signature.Interpretation {S : Signature} (M : Type v) where
  /--
    For all arities `n`, each symbol of arity `n` is mapped to a
    function 
  -/
  funcs : ∀ (n : ℕ), S.Functions n → Vec n M → M

/- An interpretation of a formula. -/
def Signature.Interpretation.formula {S : Signature} {I : S.Interpretation M} (φ : S.Formula n) : Vec n M → M :=
  fun vals => match φ with
  | Signature.Formula.var v => vals v
  | Signature.Formula.const c => I.funcs 0 c Fin.elim0
  | Signature.Formula.apply arity func ψs =>
    let func_interpreted : Vec arity M → M := I.funcs arity func
    let ψs_interpreted : Vec arity M := (fun i => I.formula (ψs i) vals)
    func_interpreted ψs_interpreted

/--
  An interpretation with type `M` is _functional complete_ if all
  functions `f : Vec n M → M` can be represented by a formula `φ`
  with `n` unbound variables.
-/
def Signature.Interpretation.FunctionalComplete {S : Signature} {I : S.Interpretation M} :=
  ∀ {n} (f : Vec n M → M),    -- for all functions `f : Vec n M → M`
  ∃ (φ : S.Formula n),        -- there exists a formula `φ`
    I.formula φ = f           -- that, when interpreted, equals `f`

/-- The set of boolean functions of arity `n`. -/
def B (n : ℕ) := Vec n Bool → Bool

/-- The set of boolean formulas of arity `n`. -/
def ℱₙ (n : ℕ) := (Signature.mk₁₂ ⟦'¬'⟧ ⟦'∨', '∧'⟧).Formula n

/--
  The set of all boolean formulas.
  This "double counts" formulas, as `¬ p` is in `ℱₙ n` for all `n > 0`.
-/
def ℱ := Σ n, ℱₙ n

/- Boolean Functions and Formulas -/
namespace Chapter1_1

/-- Signature of unary not (`¬`), and binary or/and (`∨`, `∧`). -/
@[simp]
def S_noa := (Signature.mk₁₂ ⟦'¬'⟧ ⟦'∨', '∧'⟧)

def S_noa_I : S_noa.Interpretation Bool := ⟨fun
  -- no constants in this signature
  | 0 => fun c => by contradiction 
  | 1 => fun _ value => Bool.not (value 0)
  | 2 => fun ⟨op, h_op⟩ values =>
    have h_op : op = '∨' ∨ op = '∧' := h_op
    if h_op_or : op = '∨' then Bool.or (values 0) (values 1) else
    if h_op_and : op = '∧' then Bool.and (values 0) (values 1) else by
    have : ¬(op = '∨' ∨ op = '∧') := not_or.mpr ⟨h_op_or, h_op_and⟩
    contradiction

  -- no functions of arity `n ≥ 3` 
  | n+3 => fun c => by contradiction 
⟩

-- theorem S_noa_functional_complete : S_noa_I.FunctionalComplete := sorry

end Chapter1_1