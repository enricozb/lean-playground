import Mathlib.Algebra.Periodic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.GroupTheory.OrderOfElement

-- TODO:
-- [x] prove Fib is equivalent to the matrix version
-- [ ] prove periodicity of Fib i mod n

namespace Fib

-- matrix used in the fibonacci sequence
def Q : Matrix (Fin 2) (Fin 2) ℤ := ![
  ![1, 1],
  ![1, 0]
]

lemma one_ne_zero {m : ℕ} [Fact (1 < m)] : (1 : ZMod m) ≠ 0 := by simp

-- matrix used in the fibonacci sequence but with entries in ZMod m
def Q_mod (m : ℕ) [Fact (1 < m)] : GL (Fin 2) (ZMod m) :=
  let Q_mod m : (Matrix (Fin 2) (Fin 2) (ZMod m)) := (Q.map (↑·) : Matrix (Fin 2) (Fin 2) (ZMod m))

  let i : (Matrix.det (Q_mod m)) ≠ 0 := by
    simp [Matrix.det_fin_two]
    have Q_00 : Q 0 0 = 1 := by simp only
    have Q_01 : Q 0 1 = 1 := by simp only
    have Q_10 : Q 1 0 = 1 := by simp only
    have Q_11 : Q 1 1 = 0 := by simp only
    simp [Q_00, Q_01, Q_10, Q_11]

  Matrix.GeneralLinearGroup.mkOfDetNeZero (Q_mod m) i

theorem Q_mod_fin_order {m : ℕ} [Fact (1 < m)] (n : ℕ) : IsOfFinOrder (Q_mod m) := by
  rw [IsOfFinOrder]

lemma Q_mod_00 : Q_mod n 0 0 = 1 := by simp [Q_mod, Matrix.map_apply, Q]
lemma Q_mod_01 : Q_mod n 0 1 = 1 := by simp [Q_mod, Matrix.map_apply, Q]
lemma Q_mod_10 : Q_mod n 1 0 = 1 := by simp [Q_mod, Matrix.map_apply, Q]
lemma Q_mod_11 : Q_mod n 1 1 = 0 := by simp [Q_mod, Matrix.map_apply, Q]

-- definition from mathlib
def fib (n : ℕ) : ℤ :=
  ((fun p : ℤ × ℤ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

-- standard recursive definition of the fibonacci sequence
def fib_rec : ℕ → ℤ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => fib_rec (n + 1) + fib_rec (n)

-- standard matrix definition of the fibonacci sequence
def fib_mat : ℕ → ℤ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => (Q.mulVec ![fib_mat (n+1), fib_mat n]) 0

-- matrix definition using powers of Q
def fib_pow_mat (n : ℕ) : ℕ := (Q^(n + 1)) 1 1

def fib_mod (m : ℕ) (n : ℕ) : ℕ := (fib n) % m 

theorem fib_add_two : ∀ n, fib (n + 2) = fib (n + 1) + fib n := by
  intro n
  simp only [fib, Function.iterate_succ_apply' _, Nat.add_comm]

theorem fib_rec_eq_fib_mat : fib_rec = fib_mat := by
  apply funext; intro n
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => 
      simp [fib_rec, fib_mat, Fib.Q,
            Matrix.mulVec, Matrix.vecCons, Matrix.dotProduct,
            Matrix.vecHead, Matrix.vecTail]
      rw [nih (n+1) _, nih n _]
      · apply Nat.lt.step; exact Nat.lt.base n
      · exact Nat.lt.base (n + 1)

theorem fib_eq_fib_rec : fib = fib_rec := by
  apply funext; intro n
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n =>
      rw [fib_add_two n, fib_rec, nih (n + 1) _, nih n _]
      · apply Nat.lt.step; exact Nat.lt.base n
      · exact Nat.lt.base (n + 1)

theorem q_pow_succ : ∀ n, Q^(n + 2) = Q^(n + 1) + Q^n := by
  intro n
  have h1 : Q^(n+2) = Q^n * Q^2 := by simp [pow_add]
  have h2 : Q^2 = Q + 1 := by simp only
  rw [h1, h2, mul_add, mul_one]
  conv in Q^n * Q => { congr; rfl; rw [←pow_one Q] }
  rw [←pow_add]

theorem q_mod_pow_succ : ∀ n m, (Q_mod m)^(n + 2) = (Q_mod m)^(n + 1) + (Q_mod m)^n := by
  intro n m
  have h1 : (Q_mod m)^(n+2) = (Q_mod m)^n * (Q_mod m)^2 := by simp [pow_add]
  have h2 : (Q_mod m)^2 = (Q_mod m) + 1 := sorry
  rw [h1, h2, mul_add, mul_one]
  conv in (Q_mod m)^n * (Q_mod m) => { congr; rfl; rw [←pow_one (Q_mod m)] }
  rw [←pow_add]

theorem fib_eq_fib_pow_mat : fib = fib_pow_mat := by
  apply funext; intro n
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n =>
      rw [fib_pow_mat, q_pow_succ, Matrix.add_apply]
      rw [←fib_pow_mat, ←fib_pow_mat, ←nih n, ←nih (n+1), fib_add_two]
      · exact Nat.lt.base (n + 1)
      · apply Nat.lt.step; exact Nat.lt.base n

theorem Q_mod_det : ∀ n, (Q_mod n).det = -1 := by
  intro n
  simp [Matrix.det_fin_two]
  rw [Q_mod_00, Q_mod_01, Q_mod_10, Q_mod_11]
  simp only [mul_zero, mul_one, zero_sub]

theorem fib_mod_eq_Q_mod_pow : ∀ m > 1, ∀ n, fib_mod m n = (((Q_mod m)^(n+1)) 1 1) := by
  intro m mh n
  simp only [ZMod.nat_cast_mod, fib_mod, fib_eq_fib_pow_mat, fib_pow_mat]
  have h11 : Q 1 1 = 0 := rfl
  have h11' : Q_mod m 1 1 = 0 := by simp [Q_mod, Matrix.map_apply, Q]
  have h11_2 : ((Q ^ 2) : Matrix _ _ _) 1 1 = 1 := by simp
  have h11'_2 : (((Q_mod m) ^ 2) : Matrix _ _ _) 1 1 = 1 := sorry
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => simp [h11, h11']
  | succ n => cases n with
    | zero =>
      simp only [Nat.zero_eq, ←Nat.one_eq_succ_zero]
      ring_nf
      simp only [Nat.cast_one, h11_2, h11'_2]
    | succ n =>
      rw [q_pow_succ]
      simp [nih (n + 1), q_mod_pow_succ]
      rw [nih n _]
      · apply Nat.lt.step; exact Nat.lt.base n

      
theorem pisano_period : ∀ m > 1, ∃ c, Function.Periodic (fun n => fib_mod m n) c := by
  intros m hm
  simp only [Function.Periodic, fib_add_two]


theorem pisano_period_bound (m : ℕ) {hm : m > 1} : ∃ c ≤ 6 * m, Function.Periodic (fun n => (fib n) % m) c := sorry

end Fib

-- theorem what : false := by
--   let a : ℕ := 1
--   have ha : a = 1 := rfl
--   have val_eq_zero : @ZMod.val 1 a = 0 := by simp
--   have a_neq_zero : a ≠ 0 := by simp
--   have a_eq_zero := (@ZMod.val_eq_zero 1 a).mp val_eq_zero
--   exact a_neq_zero a_eq_zero

  