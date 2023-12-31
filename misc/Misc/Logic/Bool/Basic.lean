import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Set
import Mathlib.Tactic.LibrarySearch
import «Misc».Logic.Bool.FunctionalComplete


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
  The signature `{¬, ⋁, ⋀}` is functional complete.
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