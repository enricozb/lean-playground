import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Data.Fintype.Card

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

-- fibonacci sequence modulo m > 1
def fib_mod {m : ℕ} [Fact (m > 1)] (n : ℕ) : (ZMod m) := Fib.fib_fast n

def is_fib {m : ℕ} (f : ℕ → (ZMod m)) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧ ∀ n, f (n + 2) = f (n + 1) + f n

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

lemma Q_pow_succ {m : ℕ} (n : ℕ) : Q m ^ (n + 2) = Q m ^ (n + 1) + Q m ^ n := by
  have h1 : Q m ^ (n + 2) = Q m ^ n * Q m ^ 2 := by simp [pow_add]
  simp only [h1, Q_pow_two, mul_add, mul_one, add_left_inj]
  rw [pow_add, pow_one]

theorem fib_mod_eq_Q_mod_pow {m : ℕ} [Fact (m > 1)] :
  is_fib (fun n => (Q m ^ (n + 1)) 1 1) := by
  simp [is_fib]
  -- Q m 1 1 = 0
  apply And.intro; rfl
  -- Q m ^ 2 1 1 = 1
  apply And.intro; rw [Q_pow_two]; simp; rfl
  intro n
  simp only [Q_pow_succ, Matrix.add_apply]
  
theorem Q_order_finite {m : ℕ} [Fact (m > 1)] : ∃ c > 0, Q ^ c = 1 := sorry


-- theorem Q_det_ne_zero (m : ℕ) [Fact (m > 1)] : (Q m).det ≠ 0 := by
--   simp [Q, Matrix.det_fin_two]

-- def Q_GL (m : ℕ) [Fact (m > 1)] : GL (Fin 2) (ZMod m) :=
--   Matrix.GeneralLinearGroup.mkOfDetNeZero (Q m) (Q_det_ne_zero m)

end FibMod