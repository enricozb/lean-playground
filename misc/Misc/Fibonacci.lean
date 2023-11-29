import Mathlib.Algebra.Periodic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Init.Function
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


/-!
# Fibonacci Sequence and Pisano Periods

This file has two namespaces: `Fib` and `FibMod`. These are pretty similar to
each other and can probably be combined by setting the modulus to zero for the
standard Fibonacci sequence and to greater than one for the modular sequence.
Having the modulus equal to one causes the matrix `Q` to not be invertible,
since its determinant is zero.

The `FibMod`  has some additional theorems about the modularity of the
Fibonacci sequence modulo `m`. This periodicity is established by equating the
Fibonacci sequence modulo `m` to powers of the matrix `Q`, which has an order
since `Matrix (Fin 2) (Fin 2) (ZMod m)` is a `Fintype`.
-/

namespace Fib

-- matrix used in the fibonacci sequence
def Q : Matrix (Fin 2) (Fin 2) ℕ := ![
  ![1, 1],
  ![1, 0]
]

-- a _familiar_ recurrence relation
lemma Q_pow_succ (n : ℕ) : Q^(n + 2) = Q^(n + 1) + Q^n := by
  have h1 : Q^(n + 2) = Q^n * Q^2 := by simp [pow_add]
  have h2 : Q^2 = Q + 1 := by simp only
  rw [h1, h2, mul_add, mul_one]
  conv in Q^n * Q => { congr; rfl; rw [←pow_one Q] }
  rw [←pow_add]

-- efficient definition from mathlib
def fib_fast (n : ℕ) : ℕ :=
  ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

-- recursive definition
def fib_rec : ℕ → ℕ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => fib_rec (n + 1) + fib_rec (n)

-- recursive matrix definition
def fib_rec_mat : ℕ → ℕ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => (Q.mulVec ![fib_rec_mat (n+1), fib_rec_mat n]) 0

-- power matrix definition
def fib_pow_mat (n : ℕ) : ℕ := (Q^(n + 1)) 1 1

-- whether a function is the fibonacci sequence
def is_fib (f : ℕ → ℕ) : Prop := f 0 = 0 ∧ f 1 = 1 ∧ ∀ n, f (n + 2) = f (n + 1) + f n

-- any two functions f₁ and f₂ that are fib are equal
theorem is_fib_eq (f₁ : ℕ → ℕ) (f₂ : ℕ → ℕ) {hf₁ : is_fib f₁} {hf₂ : is_fib f₂} : f₁ = f₂ := by
  apply funext; intro n
  have ⟨h0f₁, h1f₁, hnf₁⟩ := hf₁
  have ⟨h0f₂, h1f₂, hnf₂⟩ := hf₂
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  -- 0
  | zero => rw [h0f₁, h0f₂]
  | succ n => cases n with
  -- 1
  | zero => rw [h1f₁, h1f₂]
  -- n+2
  | succ n =>
    rw [hnf₁ n, hnf₂ n, nih n _, nih (n+1) _]
    · exact Nat.lt.base (n + 1)
    · apply Nat.lt.step; exact Nat.lt.base n

-- efficient definition satisfies recurrece relation
theorem fib_fast_is_fib : is_fib fib_fast := by
  simp [is_fib]
  intro n
  simp only [fib_fast, Function.iterate_succ_apply' _, Nat.add_comm]

-- recursive definition satisfies recurrece relation
theorem fib_rec_is_fib : is_fib fib_rec := by
  simp [is_fib]
  intro n
  rfl

-- recursive matrix definition satisfies recurrece relation
theorem fib_rec_mat_is_fib : is_fib fib_rec_mat := by
  simp only [is_fib, true_and]
  intro n
  simp only [
    fib_rec_mat, Q,
    Matrix.mulVec, Matrix.dotProduct, Matrix.vecCons,
    Fin.cons_zero, Fin.sum_univ_two, Fin.cons_one,
    Nat.add_eq,
    add_zero, one_mul
  ]

-- power matrix definition satisfies recurrence relation
theorem fib_pow_mat_is_fib : is_fib fib_pow_mat := by
  simp [is_fib]
  intro n
  simp [fib_pow_mat, Q_pow_succ, Matrix.add_apply]

lemma Q_11_is_fib : is_fib (fun n => (Q ^ (n + 1)) 1 1) := by
  simp only [false_and, and_self, is_fib, true_and]
  intro n
  simp only [Q_pow_succ, Matrix.add_apply]

lemma Q_10_is_fib : is_fib (fun n => (Q ^ n) 1 0) := by
  simp only [false_and, and_self, is_fib, true_and]
  intro n
  simp only [Q_pow_succ, Matrix.add_apply]

lemma Q_01_is_fib : is_fib (fun n => (Q ^ n) 0 1) := by
  simp only [false_and, and_self, is_fib, true_and]
  intro n
  simp only [Q_pow_succ, Matrix.add_apply]

lemma Q_00_is_fib : is_fib (
  fun n => match n with
    | 0 => 0
    | n+1 => (Q ^ n) 0 0
) := by
  simp only [false_and, and_self, is_fib, true_and]
  intro n
  simp only [Nat.add_eq, Nat.add_zero]
  cases n with
  | zero => simp only
  | succ n => simp only [Q_pow_succ, Matrix.add_apply]

end Fib

namespace FibMod

-- matrix used in the fibonacci sequence
def Q (m : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod m) := ![
  ![1, 1],
  ![1, 0]
]

lemma Q_pow_two {m : ℕ} : Q m ^ 2 = Q m + 1 := by
  apply funext; intro i; apply funext; intro j
  have h00 : Q m 0 0 = 1 := rfl
  have h01 : Q m 0 1 = 1 := rfl
  have h10 : Q m 1 0 = 1 := rfl
  have h11 : Q m 1 1 = 0 := rfl
  fin_cases i
  all_goals fin_cases j
  all_goals simp [pow_two, Matrix.mul_apply, h00, h01, h10, h11]

-- a _familiar_ recurrence relation
lemma Q_pow_succ {m : ℕ} (n : ℕ) : Q m ^ (n + 2) = Q m ^ (n + 1) + Q m ^ n := by
  have h1 : Q m ^ (n + 2) = Q m ^ n * Q m ^ 2 := by simp [pow_add]
  simp only [h1, Q_pow_two, mul_add, mul_one, add_left_inj]
  rw [pow_add, pow_one]

lemma Q_det (m : ℕ) : (Q m).det = -1 := by
  rw [Matrix.det_fin_two]
  have h00 : Q m 0 0 = 1 := rfl
  have h01 : Q m 0 1 = 1 := rfl
  have h10 : Q m 1 0 = 1 := rfl
  have h11 : Q m 1 1 = 0 := rfl
  simp only [h00, h01, h10, h11]
  ring_nf

lemma Q_unit_det {m : ℕ} : IsUnit (Q m).det := by
  simp only [Q_det m, IsUnit.neg_iff, isUnit_one]

-- powers of `Q` eventually repeat
lemma Q_exists_pow_eq {m : ℕ} [Fact (m > 1)] : ∃ a b, a > b ∧ Q m ^ a = Q m ^ b := by
  have h_not_injective : ¬Function.Injective (fun n => Q m ^ n) :=
    not_injective_infinite_finite _
  simp [Function.Injective] at h_not_injective
  have ⟨a, b, hQ_pow_a_eq_Q_pow_b, ha_neq_b⟩ := h_not_injective
  have ha_b_order : b > a ∨ a > b := Nat.lt_or_gt_of_ne ha_neq_b    
  cases ha_b_order with
  | inl hb_gt_a => exact ⟨b, a, hb_gt_a, hQ_pow_a_eq_Q_pow_b.symm⟩
  | inr ha_gt_b => exact ⟨a, b, ha_gt_b, hQ_pow_a_eq_Q_pow_b⟩

-- `Q` has finite order
theorem Q_order_finite {m : ℕ} [hm : Fact (m > 1)] : ∃ c > 0, Q m ^ c = 1 := by
  have ⟨a, b, ha_gt_b, hQ_pow_a_eq_Q_pow_b⟩ := @Q_exists_pow_eq m hm
  have a_ge_b : a ≥ b := Nat.le_of_lt ha_gt_b 
  have ha_sub_b_gt_zero : a - b > 0 := by simp only [ge_iff_le, gt_iff_lt, tsub_pos_iff_lt, ha_gt_b]
  have hQ_pow_c_eq_one : Q m ^ (a - b) = 1 := by
    simp only [
      ge_iff_le, ne_eq, le_refl, tsub_eq_zero_of_le, pow_zero,
      Matrix.pow_sub' (Q m) (@Q_unit_det m) (a_ge_b), ←hQ_pow_a_eq_Q_pow_b,
      Matrix.det_pow, ←Matrix.pow_sub' (Q m) (@Q_unit_det m) (by rfl)
    ]
    
  exact ⟨a - b, ha_sub_b_gt_zero, hQ_pow_c_eq_one⟩

-- fibonacci sequence modulo m > 1
def fib {m : ℕ} (n : ℕ) : (ZMod m) := Fib.fib_fast n

-- power matrix definition
def fib_pow_mat {m : ℕ} [Fact (m > 1)] (n : ℕ) : (ZMod m) := (Q m ^ (n + 1)) 1 1

-- whether a function is the fibonacci sequence
def is_fib {m : ℕ} (f : ℕ → (ZMod m)) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧ ∀ n, f (n + 2) = f (n + 1) + f n

-- any two functions f₁ and f₂ that are fib are equal
theorem is_fib_eq {m : ℕ} [Fact (m > 1)] (f₁ : ℕ → (ZMod m)) (f₂ : ℕ → (ZMod m)) {hf₁ : is_fib f₁} {hf₂ : is_fib f₂} : f₁ = f₂ := by
  apply funext; intro n
  have ⟨h0f₁, h1f₁, hnf₁⟩ := hf₁
  have ⟨h0f₂, h1f₂, hnf₂⟩ := hf₂
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  -- 0
  | zero => rw [h0f₁, h0f₂]
  | succ n => cases n with
  -- 1
  | zero => rw [h1f₁, h1f₂]
  -- n+2
  | succ n =>
    rw [hnf₁ n, hnf₂ n, nih n _, nih (n+1) _]
    · exact Nat.lt.base (n + 1)
    · apply Nat.lt.step; exact Nat.lt.base n

-- `FibMod.fib` definition satisfies recurrece relation
theorem fib_is_fib {m : ℕ} : is_fib (@fib m) := by
  rw [is_fib, fib, Fib.fib_fast]
  apply And.intro; simp
  rw [fib, Fib.fib_fast]
  apply And.intro; simp
  simp [fib, Fib.fib_fast_is_fib.right.right]

-- `FibMod.fib_pow_mat` definition satisfies recurrece relation
theorem fib_pow_mat_is_fib {m : ℕ} [hm : Fact (m > 1)] :
  is_fib (@fib_pow_mat m hm) := by
  simp [is_fib, fib_pow_mat]
  -- Q m ^ 1 1 1 = 0
  apply And.intro; rfl
  -- Q m ^ 2 1 1 = 1
  apply And.intro; rw [Q_pow_two]; simp; rfl
  -- Q m ^ (n + 3) = Q m ^ (n + 2) + Q m ^ (n + 1)
  intro n
  simp only [Q_pow_succ, Matrix.add_apply]

lemma Q_11_is_fib (m : ℕ) : is_fib (fun n => (Q m ^ (n + 1)) 1 1) := by
  simp only [
    Q_pow_succ, is_fib,
    add_left_eq_self, and_self, and_true, false_and, forall_const,
    Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, pow_one, pow_zero, true_and, zero_add
  ]
  rfl

lemma Q_10_is_fib (m : ℕ) : is_fib (fun n => (Q m ^ n) 1 0) := by
  simp only [
    Q_pow_succ, is_fib,
    add_left_eq_self, and_self, and_true, false_and, forall_const,
    Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, pow_one, pow_zero, true_and, zero_add
  ]
  rfl

lemma Q_01_is_fib (m : ℕ) : is_fib (fun n => (Q m ^ n) 0 1) := by
  simp only [
    Q_pow_succ, is_fib,
    add_left_eq_self, and_self, and_true, false_and, forall_const,
    Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, pow_one, pow_zero, true_and, zero_add
  ]
  rfl

lemma Q_00_is_fib (m : ℕ) : is_fib (
  fun n => match n with
    | 0 => 0
    | n+1 => (Q m ^ n) 0 0
) := by
  simp only [
    Q_pow_succ, is_fib,
    add_left_eq_self, and_self, and_true, false_and, forall_const,
    Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, pow_one, pow_zero, true_and, zero_add
  ]
  intro n
  cases n with
  | zero => 
    simp only [Nat.zero_eq, Nat.add_eq, zero_add, pow_one, add_zero, pow_zero, Matrix.one_apply_eq]
    rfl
  | succ n => simp only [Q_pow_succ, Matrix.add_apply]

lemma Q_entries (m : ℕ) [hm : Fact (m > 1)] (n : ℕ) :
  (Q m ^ (n + 2)) 1 1 = (Q m ^ (n + 1)) 1 0 ∧
  (Q m ^ (n + 1)) 1 0 = (Q m ^ (n + 1)) 0 1 ∧
  (Q m ^ (n + 1)) 0 1 = (Q m ^ n) 0 0  
  := by
  apply And.intro; swap; apply And.intro
  · let f₁ : ℕ → ZMod m := (fun n => (Q m ^ n) 1 0)
    let f₂ : ℕ → ZMod m := (fun n => (Q m ^ n) 0 1)
    have h := @is_fib_eq m hm f₁ f₂ (Q_10_is_fib m) (Q_01_is_fib m)
    have h₁ : f₁ (n + 1) = (Q m ^ (n + 1)) 1 0 := rfl
    have h₂ : f₂ (n + 1) = (Q m ^ (n + 1)) 0 1 := rfl
    rw [←h₁, ←h₂, h]
  · let f₁ : ℕ → ZMod m := (fun n => (Q m ^ (n + 1)) 0 1) 
    -- let f₂ : ℕ → ZMod m := (fun n => (Q m ^ n) 0)
    sorry
  sorry

-- if `f(n) := (Q m ^ n)` 1 1 has period `p`, then `Q` has order `p`
lemma Q_entry_period_is_order (m : ℕ)
  (h_period : ∀ (x : ℕ), (Q m ^ (x + p + 1)) 1 1 = (Q m ^ (x + 1)) 1 1):
  Q m ^ p = 1 := by

  have hQ_pow_eq : ∀ x, Q m ^ (x + p + 1) = Q m ^ (x + 1) := by
    intro x
    have ⟨h11_eq_10, h10_eq_01, h01_eq_00⟩ := Q_entries m (x + p + 1)
    have ⟨h11_eq_10', h10_eq_01', h01_eq_00'⟩ := Q_entries m (x + 1)
    apply funext; intro i; apply funext; intro j
    fin_cases i
    all_goals fin_cases j
    all_goals simp only [Fin.mk_one, Fin.zero_eta]
    · have hx2 := h_period (x + 2)
      rw [(by ring : x + 2 + p + 1 = x + p + 3)] at hx2
      rw [←h01_eq_00, ←h10_eq_01, ←h11_eq_10, hx2, (by ring : x + 2 + 1 = x + 3),
          h11_eq_10', h10_eq_01', h01_eq_00']
    · have ⟨h11_eq_10, h10_eq_01, _⟩ := Q_entries m (x + p)
      have ⟨h11_eq_10', h10_eq_01', _⟩ := Q_entries m x
      rw [←h10_eq_01, ←h10_eq_01', ←h11_eq_10, ←h11_eq_10', ←h_period (x + 1)]
      ring_nf
    · have ⟨h11_eq_10, _, _⟩ := Q_entries m (x + p)
      have ⟨h11_eq_10', _, _⟩ := Q_entries m x
      rw [←h11_eq_10, ←h11_eq_10', ←h_period (x + 1)]
      ring_nf
    · exact h_period x

  have hQ_pow_p : Q m ^ (p + 1) = Q m := by
    have h := hQ_pow_eq 0
    simp only [zero_add, pow_one] at h
    exact h
  have hp : p = p + 1 - 1 := by simp
  rw [
    hp, Matrix.pow_sub' (Q m) (@Q_unit_det m) (by simp only [le_add_iff_nonneg_left, zero_le]),
    hQ_pow_p, pow_one, Matrix.mul_nonsing_inv _ (@Q_unit_det m)
  ]

-- `FibMod.fib` equals `FibMod.fib_pow_mat`
theorem fib_eq_fib_pow_mat {m : ℕ} [hm : Fact (m > 1)] : @fib m = @fib_pow_mat m hm :=
  @is_fib_eq m hm (@fib m) (@fib_pow_mat m hm) (@fib_is_fib m) (@fib_pow_mat_is_fib m hm)

-- `FibMod.fib m` has period `p`
def fib_period (m : ℕ) [Fact (m > 1)] (p : ℕ) := Function.Periodic (@fib m) p

-- The pisano period, or the minimum period `p` for `FibMod.fib m` 
def pisano_period (m : ℕ) (p : ℕ) [hm : Fact (m > 1)] := @fib_period m hm p ∧ ∀ p' < p, ¬@fib_period m hm p'

-- `FibMod.fib` has period `p` iff `Q m ^ p = 1`
lemma fib_period_iff_Q_order (m : ℕ) [Fact (m > 1)] (p : ℕ): fib_period m p ↔ Q m ^ p = 1 := by
  have mp : fib_period m p → Q m ^ p = 1 := by
    intro h_period
    rw [fib_period] at h_period
    simp only [Function.Periodic, fib_eq_fib_pow_mat, fib_pow_mat] at h_period
    exact Q_entry_period_is_order m h_period

  have mpr : Q m ^ p = 1 → fib_period m p := by
    intro h_order
    rw [fib_period]
    simp only [Function.Periodic, fib_eq_fib_pow_mat, fib_pow_mat, pow_add, h_order]
    intro x
    ring_nf

  exact ⟨mp, mpr⟩

-- `FibMod.fib` is periodic for some period `p > 0`, but with no bounds on the period
theorem fib_periodic (m : ℕ) [hm : Fact (m > 1)] : ∃ p > 0, fib_period m p := by
  simp [fib_period, fib_eq_fib_pow_mat, fib_pow_mat]
  have ⟨c, hc_gt_zero, hQ_pow_c_eq_one⟩ := @Q_order_finite m hm
  apply Exists.intro
  swap; exact c
  apply And.intro; exact hc_gt_zero
  simp [pow_add, hQ_pow_c_eq_one]

-- `FibMod.fib` having period `p` implies `p` is even
theorem fib_period_even (m : ℕ) [hm : Fact (m > 1)] (p : ℕ) (hp : fib_period m p) : m > 2 → Even p := by
  intro hm'
  have h_order : Q m ^ p = 1 := (fib_period_iff_Q_order m p).mp hp
  have h_det_pow : (Q m).det ^ p = 1 := by rw [←Matrix.det_pow (Q m) p, h_order, Matrix.det_one]
  rw [Q_det] at h_det_pow
  rw [neg_one_pow_eq_one_iff_even] at h_det_pow
  exact h_det_pow
  exact @ZMod.neg_one_ne_one m (Fact.mk hm')

end FibMod
