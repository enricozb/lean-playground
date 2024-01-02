import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Set
import Mathlib.Tactic.LibrarySearch
import «Misc».Logic.Bool.DNF

open Logic

def top' := @Symbol.mk 0 "⊤" (fun _ => true)
def not' := @Symbol.mk 1 "¬" (fun b => ¬ (b 0))
def and' := @Symbol.mk 2 "∧" (fun b => (b 0) ∧ (b 1))
def or' := @Symbol.mk 2 "∨" (fun b => (b 0) ∨ (b 1))

notation "T" => top'
notation "~" => not'
notation "⋏" => and'
notation "⋎" => or'

/--
  The signature `{T, ~, ∧, ∨}`, where `∧` and `∨` operators are fixed-arity
  binary operators.
-/
def 𝓢₁ := ⟪T⟫ ∪ ⟪~⟫ ∪ ⟪⋏, ⋎⟫

theorem 𝓢₁_mem_top : (T) ∈ 𝓢₁.symbols 0 := by simp [𝓢₁, Union.union, Set.union, Set.singleton]
theorem 𝓢₁_mem_not : (~) ∈ 𝓢₁.symbols 1 := by simp [𝓢₁, Union.union, Set.union, Set.singleton]
theorem 𝓢₁_mem_and : (⋏) ∈ 𝓢₁.symbols 2 := by simp [𝓢₁, Union.union, Set.union, Set.insert]
theorem 𝓢₁_mem_or : (⋎) ∈ 𝓢₁.symbols 2 := by simp [𝓢₁, Union.union, Set.union, Set.insert, Set.singleton]

def 𝓢₁.top : 𝓢₁.Formula n := Signature.Formula.apply T 𝓢₁_mem_top default
def 𝓢₁.bot : 𝓢₁.Formula n := Signature.Formula.apply ~ 𝓢₁_mem_not (fun _ => 𝓢₁.top)
def 𝓢₁.not (φ : 𝓢₁.Formula n) : 𝓢₁.Formula n := Signature.Formula.apply ~ 𝓢₁_mem_not (fun _ => φ)

def 𝓢₁.and (φs : [𝓢₁.Formula n; m]) : 𝓢₁.Formula n :=
  match m with
  | 0 => 𝓢₁.top
  | _+1 => Signature.Formula.apply (⋏) 𝓢₁_mem_and
      (fun arg => if arg = 0 then (φs 0) else (𝓢₁.and (Fin.tail φs)))

theorem 𝓢₁.and_value_succ (b: [Bool; n]) (φs : [𝓢₁.Formula n; m + 1]) :
  ((𝓢₁.and φs).value b) = ((φs 0).value b && (𝓢₁.and (Fin.tail φs)).value b) := by
  simp [Signature.Formula.value, 𝓢₁.and, and', top']

def 𝓢₁.or {n m : ℕ} (φs : [𝓢₁.Formula n; m]) : 𝓢₁.Formula n :=
  match m with
  | 0 => 𝓢₁.bot
  | _+1 => Signature.Formula.apply (⋎) 𝓢₁_mem_or
      (fun arg => if arg = 0 then (φs 0) else (𝓢₁.or (Fin.tail φs)))

theorem 𝓢₁.or_value_succ (b: [Bool; n]) (φs : [𝓢₁.Formula n; m + 1]) :
  ((𝓢₁.or φs).value b) = ((φs 0).value b || (𝓢₁.or (Fin.tail φs)).value b) := by
  simp [Signature.Formula.value, 𝓢₁.or, or', top']

theorem 𝓢₁.and_value (φs : [𝓢₁.Formula n; m]) :
  (𝓢₁.and φs).value = (fun b => ∀ i, (φs i).value b) := by
  induction' m with m hmi
  · rfl
  · funext b
    rw [𝓢₁.and_value_succ b φs, hmi (Fin.tail φs)]
    simp [Signature.Formula.value, Fin.tail_def, *]
    by_cases (φs 0).value b = true
    · simp only [h, Bool.true_and, Fin.forall_fin_succ, true_and]
    · rw [Bool.not_eq_true] at h
      simp only [h, Bool.false_and, Bool.false_eq_decide_iff, not_forall, Bool.not_eq_true]
      exact ⟨0, h⟩

theorem 𝓢₁.or_value (φs : [𝓢₁.Formula n; m]) :
  (𝓢₁.or φs).value = (fun b => ∃ i, (φs i).value b) := by
  induction' m with m hmi
  · rfl
  · funext b
    rw [𝓢₁.or_value_succ b φs, hmi (Fin.tail φs)]
    simp [Signature.Formula.value, Fin.tail_def, *]
    by_cases (φs 0).value b = true
    · simp only [h, Bool.true_or, Bool.true_eq_decide_iff]; exact ⟨0, h⟩
    · rw [Bool.not_eq_true] at h
      simp only [Bool.false_or, Fin.exists_fin_succ, false_or, h]

theorem 𝓢₁_subsumes_DNF_𝓢 : 𝓢₁.subsumes DNF.𝓢 := by
  intro n φ
  suffices hψ : ∃ ψ : 𝓢₁.Formula n, φ.value = ψ.value
  exact ⟨hψ.choose, hψ.choose_spec⟩

  -- TODO hf_and and hf_or here can be handled in the same way in all arities
  match φ with
  | Signature.Formula.var i => exact ⟨Signature.Formula.var i, rfl⟩
  | @Signature.Formula.apply DNF.𝓢 n a f hf φs =>
    match a with
    | 0 =>
      have hf := DNF.𝓢_symbols_0 hf
      apply Or.elim hf
      · intro hf_and
        apply Exists.intro 𝓢₁.top
        simp [Signature.Formula.value, DNF.and', top', *]
      · intro hf_or
        apply Exists.intro 𝓢₁.bot
        simp [Signature.Formula.value, DNF.or', top', not', *]

    | 1 =>
      have hf := DNF.𝓢_symbols_1 hf
      have φs₁ := (fun i => 𝓢₁_subsumes_DNF_𝓢 (φs i)) 1
      apply Or.elim hf; swap; intro hf; apply Or.elim hf

      · intro hf_and
        apply Exists.intro φs₁.1
        simp [Signature.Formula.value, DNF.and', ←φs₁.2, *]
        funext b
        by_cases (φs 1).value b = true
        · rw [h, decide_eq_true_eq]
          intro i
          rw [Subsingleton.eq_one i, h]
        · rw [Bool.not_eq_true] at h
          rw [h, decide_eq_false_iff_not, not_forall]
          let i : Fin 1 := 0
          apply Exists.intro i
          rw [Bool.not_eq_true, Subsingleton.eq_one i, h]

      · intro hf_or
        apply Exists.intro φs₁.1
        simp [Signature.Formula.value, DNF.or', ←φs₁.2, *]
        funext b
        by_cases (φs 1).value b = true
        · rw [h, decide_eq_true_eq]
          let i : Fin 1 := 0
          apply Exists.intro i
          rw [Subsingleton.eq_one i, h]
        · rw [Bool.not_eq_true] at h
          rw [h, decide_eq_false_iff_not, not_exists]
          intro i
          rw [Subsingleton.eq_one i, h, Bool.not_eq_true]

      · intro hf_not
        apply Exists.intro (𝓢₁.not φs₁.1)
        simp [Signature.Formula.value, DNF.not', not', ←φs₁.2, *]

    | k + 2 =>
      let a := k + 2
      have ha_neq_one : a ≠ 1 := Nat.succ_succ_ne_one k
      have hf := DNF.𝓢_symbols_n ha_neq_one hf
      let φ's := (fun i => (𝓢₁_subsumes_DNF_𝓢 (φs i)).1)
      have hφ's := (fun i => (𝓢₁_subsumes_DNF_𝓢 (φs i)).2)
      apply Or.elim hf
      · intro hf_and
        apply Exists.intro (𝓢₁.and φ's)
        rw [𝓢₁.and_value]
        simp [Signature.Formula.value, DNF.and', *]
      · intro hf_or 
        apply Exists.intro (𝓢₁.or φ's)
        rw [𝓢₁.or_value]
        simp [Signature.Formula.value, DNF.or', *]

/--
  Theorem 2.1 from Chapter 1.

  The signature `{T, ~, ∧, ∨}` is functional complete.
-/
theorem 𝓢₁_functional_complete : 𝓢₁.functional_complete :=
  Signature.subsumes_functional_complete
    DNF.𝓢_functional_complete
    𝓢₁_subsumes_DNF_𝓢
