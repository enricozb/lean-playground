import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Set
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.FinEnum

/--
  A macro definition of a vector, modeled as a `(Fin n → α)`.
  For some reason this doesn't work:
  ```
  def Vec (n : ℕ) (α : Type v) := Fin n → α
  ```
-/
macro_rules
| `( Vec $n $α ) => `( Fin $n → $α )

macro_rules
| `( Fn $n ) => `( String × (Vec $n Bool → Bool) )

instance : FinEnum Bool := ⟨
  2, -- card
  (fun b => if b then 1 else 0),
  (fun i => if i = 0 then false else true),
  (by simp only),
  (by simp only)
⟩


/--
  The signature (symbols) of a propositional language.

  This is modeled as a family of sets of functions with different arities.
  Constants are `Signature.symbols 0`.
-/
structure Signature where
  /-- Symbols with arity `n`. -/
  symbols : (n : ℕ) → Set (Fn n)

/-- Constructs signatures with symbols of arity `1` and `2`. -/
def Signature.mk₁₂ (u : Set (Fn 1)) (b : Set (Fn 2)) :=
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

instance {S : Signature} : ToString (S.Formula n) :=
  let rec toString (φ : S.Formula n) : String :=
    match φ with
    | Signature.Formula.var i => s!"x_{i}"
    | @Signature.Formula.apply _ _ a f hf ψs =>
      match a with
      | 0 => s!"{f.1}()"
      | 1 => s!"{f.1}{toString (ψs 0)}"
      | k+2 =>
        have a_pos : k+2 > 0 := by simp only [gt_iff_lt, add_pos_iff, or_true]
        let params := (List.range (k+2)).map (fun i => toString (ψs (@Fin.ofNat' (k+2) i a_pos)))
        s!"{f.1}{params}"
  
  ⟨toString⟩

/--
  The _valuation_ of a formula, given the values of the variables.
-/
@[reducible]
def Signature.Formula.value {S : Signature} {φ : S.Formula n} (vars : Vec n Bool) : Bool :=
  match φ with
  | var i => vars i
  | apply f _ ψs => f.2 (fun i => (ψs i).value vars)

/--
  Sentences for a given signature are formulas with no unbound variables.
-/
def Signature.Sentence {S : Signature} := S.Formula 0

/--
  A signature is _functional complete_ if any function of any arity is
  representable by some formula.
-/
def Signature.functional_complete {S : Signature} : Prop :=
  ∀ {n} (f : Fn n), ∃ (φ : S.Formula n), φ.value = f.2

/--
  A signature `S₁` is a subset of a signature `S₂` if the symbols
  in `S₁` are also in `S₂`.
-/
def Signature.subset (S₁ S₂ : Signature) : Prop :=
  ∀ (n : ℕ), S₁.symbols n ⊆ S₂.symbols n

/--
  A signature `S₁` is _subsumes_ a signature `S₂` if every formula
  `φ` of signature `S₂` can be represented by a formula `ψ` of signature `S₁`.
-/
@[simp]
def Signature.subsumes (S₁ S₂ : Signature) : Prop :=
  ∀ {n} (φ : S₂.Formula n), ∃ ψ : S₁.Formula n, φ.value = ψ.value

/--
  Embeds a formula `φ` of a signature `S₁` into a signature `S₂` assuming `S₁ ⊆ S₂`. 
-/
@[simp, reducible]
def Signature.embed {S₁ S₂ : Signature} (hs : S₁.subset S₂) (φ : S₁.Formula n) : S₂.Formula n :=
  match φ with
  | Formula.var i => Formula.var i
  | Formula.apply f hf ψs =>
    Formula.apply f
      (Set.mem_of_subset_of_mem (hs _) hf)
      (fun i => embed hs (ψs i))

/--
  If signature `S₁` is a subset of signature `S₂`, then `S₂` subsumes `S₁`.
-/
def Signature.subset_subsumes {S₁ S₂ : Signature} (hs : S₁.subset S₂) :
  S₂.subsumes S₁ := by
    intro n φ
    let ψ := embed hs φ
    have h : φ.value = (embed hs φ).value := by
      funext vars
      induction φ
      · rfl
      · rename_i a f hf φs hφs
        have hφ : (Formula.apply f hf φs).value vars = f.2 (fun i => (φs i).value vars) := rfl
        have hψ : ψ.value vars = f.2 (fun i => (embed hs (φs i)).value vars) := rfl
        rw [hφ, hψ, funext hφs]
    
    exact ⟨ψ, h⟩


/--
  If a signature `S₁` can subsume a functional complete signature `S₂`, then
  `S₁` is also functional complete.
-/
theorem Signature.subsumes_functional_complete {S₁ S₂ : Signature} (hfc : S₁.functional_complete) (hs : S₂.subsumes S₁) :
  S₂.functional_complete := by
  intro n f
  have ⟨φ, hφ⟩ := hfc f
  have ⟨ψ, hψ⟩ := hs φ
  rw [hφ] at hψ
  exact ⟨ψ, hψ.symm⟩

/--
  If a signature `S₁` is the subset of a functional complete signature `S₂`, then
  `S₁` is also functional complete.
-/
theorem Signature.subset_functional_complete {S₁ S₂ : Signature} (hfc : S₁.functional_complete) (hs : S₁.subset S₂) :
  S₂.functional_complete := by
  have hr : S₂.subsumes S₁ := S₁.subset_subsumes hs
  exact @subsumes_functional_complete S₁ S₂ hfc hr

def not' : Vec 1 Bool → Bool := (fun p => ¬ (p 0))
def or' : Vec 2 Bool → Bool := (fun p => (p 0) ∨ (p 1))
def and' : Vec 2 Bool → Bool := (fun p => (p 0) ∧ (p 1))
def bigor' (n : ℕ) : Vec n Bool → Bool := (fun p => ∃ i, p i)
def bigand' (n : ℕ) : Vec n Bool → Bool := (fun p => ∀ i, p i)

notation "(¬)" => ("¬", not')
notation "(∨)" => ("∨", or')
notation "(∧)" => ("∧", and')
notation "⋁" => ("⋁", bigor' ·)
notation "⋀" => ("⋀", bigand' ·)

/--
  The signature `{¬} ∪ {⋁ n : n ∈ ℕ} ∪ {⋀ n : n ∈ ℕ} `.
  
  This includes the big-or and big-and operators for every arity `n`, as they
  are used for constructing DNFs and CNFs of boolean functions.
-/
@[simp]
def sig_nOA := Signature.mk (fun
  | 1 => {⋁ 1, ⋀ 1, (¬)}
  | n => {⋁ n, ⋀ n}
)

lemma sig_nOA_not : (¬) ∈ sig_nOA.symbols 1 := by
  simp only [sig_nOA, Set.mem_singleton_iff, Set.mem_insert_iff, true_or]

lemma sig_nOA_Or {n : ℕ} : (⋁ n) ∈ sig_nOA.symbols n := by
  match n with
  | 0 => simp only [sig_nOA, Set.mem_singleton_iff, Set.mem_insert_iff, true_or]
  | 1 => simp only [sig_nOA, Set.mem_singleton_iff, Set.mem_insert_iff, true_or, or_true]
  | n+2 => simp only [sig_nOA, Set.mem_singleton_iff, Set.mem_insert_iff, Nat.add_eq, Nat.add_zero, true_or]

lemma sig_nOA_And {n : ℕ} : (⋀ n) ∈ sig_nOA.symbols n := by
  match n with
  | 0 => simp only [sig_nOA, Set.mem_singleton_iff, Set.mem_insert_iff, or_true]
  | 1 => simp only [sig_nOA, Set.mem_singleton_iff, Set.mem_insert_iff, true_or, or_true]
  | n+2 => simp only [sig_nOA, Set.mem_singleton_iff, Set.mem_insert_iff, Nat.add_eq, Nat.add_zero, or_true]

/--
  The conjunctive gadget used to construct a DNF for a boolean function.

  If `b` is an `n`-tuple, then `dnf_entry` produces a formula of arity `n`,
  `φ(x₁, .., xₙ) = ⋀ᵢ₌₁..ₙ (if bᵢ then xᵢ else ¬xᵢ)`. Each of these conjunctions
  are then disjuncted to produce a DNF.

  Technically this conjunction can live in a signature `{¬, ⋀}`, but it is in
  the signature `{¬, ∧, ∨, ⋀, ⋁}` to simplify the construction of the DNF.
-/
def dnf_entry (b : Vec n Bool) : sig_nOA.Formula n :=
  Signature.Formula.apply (⋀ n) sig_nOA_And (fun i =>
    if b i then
      (Signature.Formula.var i)
    else
      (Signature.Formula.apply (¬) sig_nOA_not (fun _ => Signature.Formula.var i))
  )

/--
  The disjunctive normal form (DNF) of a boolean function `f` of arity `n`.

  This requires `∀ (b : Vec n Prop), Decidable (f b)` in order to
  constructively produce a formula `φ` that represents `f`.
-/
def dnf (f : Vec n Bool → Bool) : sig_nOA.Formula n :=
  have all : List (Vec n Bool) := @FinEnum.pi.enum (Fin n) (fun _ => Bool) _ _
  have trues := all.filter f

  Signature.Formula.apply (⋁ trues.length) sig_nOA_Or (dnf_entry ∘ trues.get)

#eval (dnf (fun b : Vec 2 Bool => b 0 ∨ b 1))

theorem sig_nOA_functional_complete : sig_nOA.functional_complete := by
  intro n f
  let f_preim := {b : Vec n Prop | f b}
  have card : ℕ := sorry
  have surj : Fin card → ↑f_preim := sorry

  -- have f_preim_fin : Finite f_preim := Subtype.finite
  -- have f_preim_finty := (Fintype.ofFinite f_preim)
  -- have f_preim_card := Fintype.card f_preim

  have conj (b : Vec n Prop) : sig_nOA.Formula n := by
    exact Signature.Formula.apply (⋀ n) sig_nOA_And (
      fun i =>
        -- if (b i) then (var i) else ¬(var i)
        @ite (Signature.Formula n) (b i) (Classical.propDecidable _)
          (Signature.Formula.var i)
          (Signature.Formula.apply (¬) sig_nOA_not (fun _ => Signature.Formula.var i))
    )
  
  -- construct `φ` by applying `⋁` to `conj` to each element of `f_preim`
  have φ : sig_nOA.Formula n := Signature.Formula.apply (⋁ card) sig_nOA_Or (fun i => conj (surj i))

  -- need to use finiteness of `f_preim` to show there exists some `n` for
  -- which we can apply `⋁ n` to everything.
  -- have φ := Signature.Formula.apply

  apply Exists.intro φ
  funext b
  simp

def sig_noa := Signature.mk₁₂ {(¬)} {(∨), (∧)}
def sig_no := Signature.mk₁₂ {(¬)} {(∨)}
def sig_na := Signature.mk₁₂ {(¬)} {(∧)}

theorem sig_noa_subsumes_nOA : sig_noa.subsumes sig_nOA := by
  intro n φ

  let rec embed (φ : sig_nOA.Formula n) : sig_noa.Formula n :=
    match φ with
    | Signature.Formula.var i => Signature.Formula.var i
    | Signature.Formula.apply a f hf φs => match a with
      | 0 => by
        have : f = (⋁ 0) := hf
        exact 
      | 1 => by
        have : f = (¬) ∨ f = (⋁ 1) := hf
      | 2 => sorry
      | n => sorry

  let ψ := embed φ
  have hψ : φ.value = ψ.value := sorry
  
  exact ⟨ψ, hψ⟩ 

/--
  Theorem 2.1 from Chapter 1.

  The signature `{¬, ∧, ∨}` is functional complete.
-/
theorem sig_noa_functional_complete : sig_noa.functional_complete :=
  Signature.subsumes_functional_complete sig_nOA_functional_complete sig_noa_subsumes_nOA