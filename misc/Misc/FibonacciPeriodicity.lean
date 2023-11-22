import Mathlib.Algebra.Periodic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.LinearAlgebra.Matrix.Determinant

-- TODO:
-- [x] prove Fib is equivalent to the matrix version
-- [ ] prove periodicity of Fib i mod n

namespace Fib

-- definition from mathlib
def fib (n : ℕ) : ℕ :=
  ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

-- standard recursive definition of the fibonacci sequence
def seq_rec : ℕ → ℕ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => seq_rec (n + 1) + seq_rec (n)

-- matrix definition of the fibonacci sequence
def Q : Matrix (Fin 2) (Fin 2) ℕ := ![
  ![1, 1],
  ![1, 0]
]

def Q_mod (n : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod n) := ![
  ![1, 1],
  ![1, 0]
]

theorem Q_mod_det : ∀ n, (Q_mod n).det = -1 := by
  intro n
  simp [Matrix.det_fin_two]
  have h00 : Q_mod n 0 0 = 1 := rfl
  have h01 : Q_mod n 0 1 = 1 := rfl
  have h10 : Q_mod n 1 0 = 1 := rfl
  have h11 : Q_mod n 1 1 = 0 := rfl
  rw [h00, h01, h10, h11]
  simp only [mul_zero, mul_one, zero_sub]

def seq_mat : ℕ → ℕ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => (Q.mulVec ![seq_mat (n+1), seq_mat n]) 0

theorem seq_rec_eq_seq_mat : seq_rec = seq_mat := by
  apply funext; intro n
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => 
      simp [seq_rec, seq_mat, Fib.Q,
            Matrix.mulVec, Matrix.vecCons, Matrix.dotProduct,
            Matrix.vecHead, Matrix.vecTail]
      rw [nih (n+1) _, nih n _]
      · apply Nat.lt.step; exact Nat.lt.base n
      · exact Nat.lt.base (n + 1)

theorem fib_eq_rec_def : ∀ n, fib (n + 2) = fib (n + 1) + fib n := by
  -- not sure i could have come up with this, from mathlib
  intro n; simp [fib, Function.iterate_succ_apply' _, Nat.add_comm]

theorem fib_eq_seq_rec : fib = seq_rec := by
  apply funext; intro n
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n =>
      rw [fib_eq_rec_def n, seq_rec, nih (n + 1) _, nih n _]
      · apply Nat.lt.step; exact Nat.lt.base n
      · exact Nat.lt.base (n + 1)

def seq_pow_mat (n : ℕ) : ℕ := (Q^(n + 1)) 1 1

theorem q_pow_succ : ∀ n, Q^(n + 2) = Q^(n + 1) + Q^n := by
  intro n
  have h1 : Q^(n+2) = Q^n * Q^2 := by simp [pow_add]
  have h2 : Q^2 = Q + 1 := by simp only
  rw [h1, h2, mul_add, mul_one]
  conv in Q^n * Q => { congr; rfl; rw [←pow_one Q] }
  rw [←pow_add]

theorem fib_eq_seq_pow_mat : fib = seq_pow_mat := by
  apply funext; intro n
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n =>
      rw [seq_pow_mat, q_pow_succ, Matrix.add_apply]
      rw [←seq_pow_mat, ←seq_pow_mat, ←nih n, ←nih (n+1), fib_eq_rec_def]
      · exact Nat.lt.base (n + 1)
      · apply Nat.lt.step; exact Nat.lt.base n

theorem pisano_period : ∀ m > 1, ∃ c, Function.Periodic (fun n => (fib n) % m) c := by
  intros m hm
  sorry

theorem pisano_period_bound : ∀ m > 1, ∃ c ≤ 6 * m, Function.Periodic (fun n => (fib n) % m) c := sorry

end Fib

def Q_mod (n : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod n) := ![
  ![1, 1],
  ![1, 0]
]

#check (Q_mod 5).orderOf