import «Misc».Logic.Bool.FunctionalComplete

namespace DNF

def not' := @Symbol.mk 1 "¬" (fun b => ¬ (b 0))
def and' (n : ℕ) := @Symbol.mk n "⋀" (fun b => ∀ i, b i)
def or' (n : ℕ) := @Symbol.mk n "⋁" (fun b => ∃ i, b i)

scoped [DNF] notation "~" => not'
scoped [DNF] notation "⋀" => and'
scoped [DNF] notation "⋁" => or'

/--
  The signature `{T, ~} ∪ {⋁ n : n ∈ ℕ} ∪ {⋀ n : n ∈ ℕ}`.
  
  This includes the big-or and big-and operators for every arity `n`, as they
  are used for constructing DNFs and CNFs of boolean functions.
-/
def 𝓢 := ⟪~⟫ ∪ ⟪⋀, ⋁⟫ₙ

theorem 𝓢_not : (~) ∈ 𝓢.symbols 1 := by
  simp [𝓢, Union.union, Set.union, Set.insert, Set.singleton]

theorem 𝓢_and {n : ℕ} : (⋀ n) ∈ 𝓢.symbols n := by
  simp [𝓢, Union.union, Set.union, Set.insert]

theorem 𝓢_or {n : ℕ} : (⋁ n) ∈ 𝓢.symbols n := by
  simp [𝓢, Union.union, Set.union, Set.insert]

theorem 𝓢_symbols_1 (hs : s ∈ 𝓢.symbols 1) : s = (~) ∨ s = (⋀ 1) ∨ s = (⋁ 1) := by
  simp [𝓢, Union.union, Set.union, Set.insert, Set.singleton] at hs
  exact hs

theorem 𝓢_symbols_n {n : ℕ} {s : Symbol n} (hn : n ≠ 1) (hs : s ∈ 𝓢.symbols n) : s = (⋀ n) ∨ s = (⋁ n) := by
  simp [𝓢, Union.union, Set.union, Set.insert, Set.singleton, hn] at hs
  exact hs
  
theorem 𝓢_symbols_0 (hs : s ∈ 𝓢.symbols 0) : s = (⋀ 0) ∨ s = (⋁ 0) := 𝓢_symbols_n Nat.zero_ne_one hs

/--
  A list of inputs satisfying `f`.
  
  That is, a list of `b : [Bool; n]` such that `f b = true`. This list is
  ordered by the ordering imposed by `FinEnum Bool`.
-/
def satisfying_inputs (f : [Bool; n] → Bool) : List [Bool; n] :=
  (FinEnum.pi.enum (fun _ => Bool)).filter f

/-- If `f b = true` then `b` is in the list of satisfying inputs. -/
def satisfying_inputs_contains (f : [Bool; n] → Bool) (b : [Bool; n]) (hb : f b = true) :
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
def dnf_entry (b : [Bool; n]) : 𝓢.Formula n :=
  Signature.Formula.apply (⋀ n) 𝓢_and (fun i =>
    if b i then
      (Signature.Formula.var i)
    else
      (Signature.Formula.apply (~) 𝓢_not (fun _ => Signature.Formula.var i))
  )

/--
  If a conjunctive gadget (a DNF entry) constructed from a boolean vector `b₁`
  evaluates to true for some boolean vector `b₂` if and only if `b₁ = b₂`.
-/
lemma dnf_entry_true_iff (b₁ b₂ : [Bool; n]) : (dnf_entry b₁).value b₂ = true ↔ b₁ = b₂ := by
  apply Iff.intro
  · intro hφb₂
    funext i
    simp [Signature.Formula.value, dnf_entry, and'] at hφb₂
    have hφb₂ᵢ := hφb₂ i
    by_cases b₁ i = true
    all_goals simp [Signature.Formula.value, dnf_entry, and', *] at hφb₂ᵢ
    · simp only [Bool.not_eq_true, h, hφb₂ᵢ]
    · rw [Bool.not_eq_true] at h
      simp [not'] at hφb₂ᵢ
      rw [h, hφb₂ᵢ]

  · intro hb₁_eq_b₂
    simp only [Signature.Formula.value, and', decide_eq_true_eq]
    intro i
    by_cases b₂ i = true
    all_goals { simp only [Signature.Formula.value, *] }

/--
  The conjunctive gadget (a DNF entry) evaluates to true for the boolean vector
  `b` that was used to build it.
-/
lemma dnf_entry_self (b : [Bool; n]) : (dnf_entry b).value b = true := 
  (dnf_entry_true_iff b b).mpr rfl

/--
  The disjunctive normal form (DNF) of a boolean function `f` of arity `n`.
-/
def dnf (f : [Bool; n] → Bool) : 𝓢.Formula n :=
  Signature.Formula.apply 
    (⋁ (satisfying_inputs f).length)
    𝓢_or
    (dnf_entry ∘ (satisfying_inputs f).get)

/--
  For any function `f: 𝔹ⁿ → 𝔹`, the DNF of `f` represents `f`.
-/
theorem dnf_represents (f : [Bool; n] → Bool) : (dnf f).value = f := by
  funext b
  rw [Signature.Formula.value]
  simp only [or']
  by_cases (f b)

  -- f b = true
  · rw [h]
    simp only [Bool.true_eq_decide_iff, and', decide_eq_true_eq]
    have ⟨i, hi⟩ := satisfying_inputs_contains f b h
    apply Exists.intro i
    rw [Function.comp_apply, hi]
    exact dnf_entry_self b

  -- f b = false
  · rw [Bool.not_eq_true] at h
    rw [h]
    simp only [
      Bool.false_eq_decide_iff, and', decide_eq_false_iff_not,
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
theorem 𝓢_functional_complete : 𝓢.functional_complete := by
  intro n f
  exact ⟨dnf f, (dnf_represents f).symm⟩

end DNF
