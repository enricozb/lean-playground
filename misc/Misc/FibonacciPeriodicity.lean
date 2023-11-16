import Mathlib.Data.Nat.Basic
import Mathlib.Data.Matrix.Basic

-- TODO:
-- [x] prove Fib is equivalent to the matrix version
-- [ ] prove periodicity of Fib i mod n

namespace Fib

-- standard recursive definition of the fibonacci sequence
def seq_rec : ℕ → ℕ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => seq_rec (n + 1) + seq_rec (n)

-- matrix definition of the fibonacci sequence
def matrix: Matrix (Fin 2) (Fin 2) ℕ := ![
  ![1, 1],
  ![1, 0]
]

def seq_mat : ℕ → ℕ := fun
    | 0 => 0
    | 1 => 1
    | n + 2 => (matrix.mulVec ![seq_mat (n+1), seq_mat n]) 0

theorem seq_rec_eq_seq_mat : ∀ n, seq_rec n = seq_mat n := by
  intro n
  induction' n using Nat.strong_induction_on with n nih
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => 
      rw [seq_rec]
      have hle1 : n + 1 < n.succ.succ := by simp
      have hle2 : n < n.succ.succ := by apply Nat.lt.step; simp
      have h2 : seq_rec (n + 1) = seq_mat (n + 1) := nih (n + 1) hle1
      have h3 : seq_rec n = seq_mat n := nih n hle2
      rw [h2, h3, seq_mat, Fib.matrix, Matrix.mulVec, Matrix.vecCons]
      simp
      rw [Matrix.dotProduct]
      simp

end Fib