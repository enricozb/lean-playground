import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Set
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.FinEnum

/- Some utilities to clarify & simplify definitions. -/
section Utils

/--
  A notation for vectors.

  A definition cannot be used as inductive constructors can't contain `def`s.
-/
notation "Vec" => (fun (n : ℕ) (α : Type) => Fin n → α)

instance : FinEnum Bool := ⟨
  -- card
  2,
  -- mappings between Bool and Fin 2
  (fun b => if b then 1 else 0),
  (fun i => if i = 0 then false else true),
  -- proofs that above maps are inverses of each other
  (by simp only),
  (by simp only)
⟩

end Utils

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

/--
  The _valuation_ of a formula is the boolean function it represents.
-/
def Signature.Formula.value {S : Signature} {φ : S.Formula n} (vars : Vec n Bool) : Bool :=
  match φ with
  | var i => vars i
  | apply f _ ψs => f.2 (fun i => (ψs i).value vars)

/--
  Applies a formula to a vector of formulas.
-/
def Signature.Formula.fmap {S : Signature} {φ : S.Formula n} (ψs : Vec n (S.Formula m)) : S.Formula m :=
  match φ with
  | var i => ψs i
  | apply f hf ψs' => apply f hf (fun i => (ψs' i).fmap ψs)

/--
  Sentences for a given signature are formulas with no unbound variables.
-/
def Signature.Sentence {S : Signature} := S.Formula 0

/--
  A signature is _functional complete_ if any function of any arity is
  representable by some formula.
-/
def Signature.functional_complete {S : Signature} : Prop :=
  ∀ {n} (f : Vec n Bool → Bool), ∃ (φ : S.Formula n), f = φ.value

/--
  A signature `S₁` is a subset of a signature `S₂` if the symbols
  in `S₁` are also in `S₂`.
-/
def Signature.subset (S₁ S₂ : Signature) : Prop :=
  ∀ (n : ℕ), S₁.symbols n ⊆ S₂.symbols n

/--
  A signature `S₁` is _subsumes_ a signature `S₂` if every _formula_
  `φ` of signature `S₂` can be represented by a formula `ψ` of signature `S₁`.
-/
def Signature.subsumes (S₁ S₂ : Signature) :=
  ∀ {n} (φ : S₂.Formula n), (ψ : S₁.Formula n) ×' (φ.value = ψ.value)

/--
  A signature `S₁` is _narrows_ a signature `S₂` if every _symbol_
  `s` of signature `S₂` can be represented by a formula `ψ` of signature `S₁`.
-/
def Signature.narrows (S₁ S₂ : Signature) :=
  ∀ {n} {s : _}, (s ∈ S₂.symbols n) → (ψ : S₁.Formula n) ×' (s.fn = ψ.value)

/--
  Maps a formula `φ` of a signature `S₂` into a signature `S₁` assuming `S₁.narrows S₂`. 
-/
def Signature.narrow {S₁ S₂ : Signature} (hn : S₁.narrows S₂) (φ : S₂.Formula n) : S₁.Formula n :=
  match φ with
  | Formula.var i => Formula.var i
  | Formula.apply _ hf ψs => (hn hf).1.fmap (fun i => (S₁.narrow hn (ψs i)))

/--
  A narrowed formula `φ₂ := S₁.narrow φ₁` represesents `φ₁`.
-/
theorem Signature.narrow_represents {S₁ S₂ : Signature} {hn : S₁.narrows S₂} (φ : S₂.Formula n) :
  φ.value = (S₁.narrow hn φ).value := by
  funext b
  induction φ
  · rfl
  · rename_i a f hf φs hφs
    simp [Signature.Formula.value, narrow, *]
    sorry

/-- If a signature `S₁` narrows a signature `S₂` then it subsumes it. -/
theorem Signature.narrows_subsumes {S₁ S₂ : Signature} (hn : S₁.narrows S₂) : S₁.subsumes S₂ := by
  intro n φ
  exact ⟨S₁.narrow hn φ, S₁.narrow_represents φ⟩

/--
  Embeds a formula `φ` of a signature `S₁` into a signature `S₂` assuming `S₁ ⊆ S₂`. 
-/
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
  rw [hφ.symm] at hψ
  exact ⟨ψ, hψ⟩

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

notation "(¬)" => Symbol.mk "¬" not'
notation "(∨)" => Symbol.mk "∨" or'
notation "(∧)" => Symbol.mk "∧" and'
notation "⋁" => (fun n => Symbol.mk "⋁" (bigor' n))
notation "⋀" => (fun n => Symbol.mk "⋀" (bigand' n))

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
  simp only [sig_nOA, Set.mem_singleton_iff, Symbol.mk.injEq, Set.mem_insert_iff, or_self, false_and, or_true]

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
  A list of inputs satisfying `f`.
  
  That is, a list of `b : Vec n Bool` such that `f b = true`. This list is
  ordered by the ordering imposed by `FinEnum Bool`.
-/
def satisfying_inputs (f : Vec n Bool → Bool) : List (Vec n Bool) :=
  (FinEnum.pi.enum (fun _ => Bool)).filter f

/-- If `f b = true` then `b` is in the list of satisfying inputs. -/
def satisfying_inputs_contains (f : Vec n Bool → Bool) (b : Vec n Bool) (hb : f b = true) :
  ∃ i, (satisfying_inputs f).get i = b := 
  List.mem_iff_get.mp (List.mem_filter.mpr ⟨FinEnum.pi.mem_enum _, hb⟩)

/--
  The conjunctive gadget (a DNF entry) used to construct a DNF for a boolean
  function.

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
  If a conjunctive gadget (a DNF entry) constructed from a boolean vector `b₁`
  evaluates to true for some boolean vector `b₂` if and only if `b₁ = b₂`.
-/
lemma dnf_entry_true_iff (b₁ b₂ : Vec n Bool) : (dnf_entry b₁).value b₂ = true ↔ b₁ = b₂ := by
  apply Iff.intro
  · intro hφb₂
    funext i
    simp [Signature.Formula.value, dnf_entry, bigand', *] at hφb₂
    have hφb₂ᵢ := hφb₂ i
    by_cases b₁ i = true
    all_goals simp [Signature.Formula.value, dnf_entry, bigand', not', *] at hφb₂ᵢ
    · simp only [Bool.not_eq_true, h, hφb₂ᵢ]
    · rw [Bool.not_eq_true] at h
      rw [of_decide_eq_true hφb₂ᵢ]
      exact h

  · intro hb₁_eq_b₂
    simp only [Signature.Formula.value, bigand', decide_eq_true_eq]
    intro i
    by_cases b₂ i = true
    all_goals { simp only [Signature.Formula.value, *] }

/--
  The conjunctive gadget (a DNF entry) evaluates to true for the boolean vector
  `b` that was used to build it.
-/
lemma dnf_entry_self (b : Vec n Bool) : (dnf_entry b).value b = true := 
(dnf_entry_true_iff b b).mpr rfl


/--
  The disjunctive normal form (DNF) of a boolean function `f` of arity `n`.

  This requires `∀ (b : Vec n Prop), Decidable (f b)` in order to
  constructively produce a formula `φ` that represents `f`.
-/
def dnf (f : Vec n Bool → Bool) : sig_nOA.Formula n :=
  have trues := satisfying_inputs f

  Signature.Formula.apply (⋁ trues.length) sig_nOA_Or (dnf_entry ∘ trues.get)

/--
  For any function `f: 𝔹ⁿ → 𝔹`, the DNF of `f` represents `f`.
-/
theorem dnf_represents (f : Vec n Bool → Bool) : (dnf f).value = f := by
  funext b
  rw [Signature.Formula.value]
  simp only [bigor']
  by_cases (f b)

  -- f b = true
  · rw [h]
    simp only [Bool.true_eq_decide_iff, bigand', decide_eq_true_eq]
    have ⟨i, hi⟩ := satisfying_inputs_contains f b h
    apply Exists.intro i
    rw [Function.comp_apply, hi]
    exact dnf_entry_self b

  -- f b = false
  · rw [Bool.not_eq_true] at h
    rw [h]
    simp only [
      Bool.false_eq_decide_iff, bigand', decide_eq_false_iff_not,
      not_exists, not_forall, Bool.not_eq_true, Function.comp_apply
    ]
    intro i
    apply by_contradiction
    intro hφb_true
    let bᵢ := (satisfying_inputs f).get i
    have hfbᵢ : f bᵢ = true := (List.mem_filter.mp (List.get_mem _ i _)).2
    rw [Bool.not_eq_false] at hφb_true
    rw [(dnf_entry_true_iff bᵢ b).mp hφb_true, h] at hfbᵢ
    contradiction

/--
  The signature `{¬, ∨, ∧, ⋁, ⋀}` is functional complete.
-/
theorem sig_nOA_functional_complete : sig_nOA.functional_complete := by
  intro n f
  exact ⟨dnf f, (dnf_represents f).symm⟩

def sig_noa := Signature.mk₁₂ {(¬)} {(∨), (∧)}
def sig_no := Signature.mk₁₂ {(¬)} {(∨)}
def sig_na := Signature.mk₁₂ {(¬)} {(∧)}

def sig_noa_narrows_nOA : sig_noa.narrows sig_nOA := by
  intro a f hf
  match a with
  | 0 =>
    simp [bigand', bigor', *] at hf
    if h_or : f = (⋁ 0) then
      sorry
    else if h_and : f = (⋀ 0) then
      sorry
    else
      have := not_or.mpr ⟨h_or, h_and⟩ hf
      contradiction

  | 1 => sorry
  | 2 => sorry
  | n => sorry


-- theorem sig_noa_subsumes_nOA : sig_noa.subsumes sig_nOA := by
--   intro n φ

--   let rec embed (φ : sig_nOA.Formula n) : sig_noa.Formula n :=
--     match φ with
--     | Signature.Formula.var i => Signature.Formula.var i
--     | Signature.Formula.apply a f hf φs => match a with
--       | 0 => by
--         have : f = (⋁ 0) := hf
--         exact 
--       | 1 => by
--         have : f = (¬) ∨ f = (⋁ 1) := hf
--       | 2 => sorry
--       | n => sorry

--   let ψ := embed φ
--   have hψ : φ.value = ψ.value := sorry
  
--   exact ⟨ψ, hψ⟩ 

/--
  Theorem 2.1 from Chapter 1.

  The signature `{¬, ∧, ∨}` is functional complete.
-/
theorem sig_noa_functional_complete : sig_noa.functional_complete :=
  Signature.subsumes_functional_complete
    sig_nOA_functional_complete
    (sig_noa.narrows_subsumes sig_noa_narrows_nOA)