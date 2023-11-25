import Mathlib.Algebra.Periodic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Init.Function
import Mathlib.LinearAlgebra.Matrix.ZPow

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

lemma Q_unit_det {m : ℕ} : IsUnit (Q m).det := by
  have Q_det_eq_neg_one : (Q m).det = -1 := by
    rw [Matrix.det_fin_two]
    have h00 : Q m 0 0 = 1 := rfl
    have h01 : Q m 0 1 = 1 := rfl
    have h10 : Q m 1 0 = 1 := rfl
    have h11 : Q m 1 1 = 0 := rfl
    simp only [h00, h01, h10, h11]
    ring
  simp only [Q_det_eq_neg_one, IsUnit.neg_iff, isUnit_one]

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
      Matrix.det_pow,  ← Matrix.pow_sub' (Q m) (@Q_unit_det m) (by rfl)
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

-- `FibMod.fib` equals `FibMod.fib_pow_mat`
theorem fib_eq_fib_pow_mat {m : ℕ} [hm : Fact (m > 1)] : @fib m = @fib_pow_mat m hm :=
  @is_fib_eq m hm (@fib m) (@fib_pow_mat m hm) (@fib_is_fib m) (@fib_pow_mat_is_fib m hm)

-- `FibMod.fib` is periodic, but with no bounds on the period
theorem fib_periodic {m : ℕ} [hm : Fact (m > 1)] : ∃ c > 0, Function.Periodic (@fib m) c := by
  simp [fib_eq_fib_pow_mat, fib_pow_mat]
  have ⟨c, hc_gt_zero, hQ_pow_c_eq_one⟩ := @Q_order_finite m hm
  apply Exists.intro
  swap; exact c
  apply And.intro; exact hc_gt_zero
  simp [pow_add, hQ_pow_c_eq_one]

end FibMod