import Mathlib.Algebra.Periodic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Init.Function
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ZPow

namespace FibMod

/-- Wrapper class for adding modulus to the type class system.
This is used so the modulus can be inferred in the following `theorem`s and `def`s. -/
class Mod : Type where
  n : ℕ

/-- Coerce `Mod` into its inner value. -/
instance : Coe Mod ℕ := ⟨fun mod => mod.n⟩

/-- Coerce `mod : Mod` into `ZMod mod.n`. -/
instance : Coe Mod Type := ⟨fun mod => ZMod mod.n⟩

/-- Matrix used in the fibonacci sequence -/
def Q [mod : Mod] : Matrix (Fin 2) (Fin 2) ↑mod := ![
  ![1, 1],
  ![1, 0]
]

lemma Q_00 [Mod] : Q 0 0 = 1 := rfl
lemma Q_01 [Mod] : Q 0 1 = 1 := rfl
lemma Q_10 [Mod] : Q 1 0 = 1 := rfl
lemma Q_11 [Mod] : Q 1 1 = 0 := rfl

lemma Q_pow_two [Mod] : Q ^ 2 = Q + 1 := by
  apply funext; intro i; apply funext; intro j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [
    pow_two, zero_add, ne_eq,
    Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    Q_00, Q_01, Q_10, Q_11,
    Fin.mk_one, Fin.zero_eta, Fin.sum_univ_two
  ]
  all_goals ring

lemma Q_pow_succ [Mod] (n : ℕ) : Q ^ (n + 2) = Q ^ (n + 1) + Q ^ n := by
  rw [pow_add, Q_pow_two, mul_add, mul_one, add_left_inj, pow_add, pow_one]

lemma Q_det_eq_neg_one [Mod] : Q.det = -1 := by
  rw [Matrix.det_fin_two, Q_00, Q_01, Q_10, Q_11]
  ring_nf

lemma isUnit_Q_det [Mod] : IsUnit Q.det := by
  rw [Q_det_eq_neg_one, IsUnit.neg_iff]
  exact isUnit_one

lemma Q_exists_pow_eq [Mod] [h_mod_ge_one : Fact (Mod.n ≥ 1)] : ∃ a b, a > b ∧ Q ^ a = Q ^ b := by
  by_cases Mod.n = 1

  -- case Mod.n = 1
  · have h : Q ^ 2 = Q ^ 1 := by
      simp only [Q_pow_two, pow_one, add_right_eq_self]
      apply funext; intro i; apply funext; intro j
      all_goals fin_cases i
      all_goals fin_cases j
      all_goals { rw [h]; simp only }
      
    exact ⟨2, 1, (by simp only : 2 > 1), h⟩

  -- case Mod.n ≠ 1
  · have : Fact (Mod.n > 1) := by
      apply Fact.mk
      have h_mod_ne_one : Mod.n ≠ 1 := by rw [ne_eq]; exact h
      exact lt_iff_le_and_ne.mpr ⟨h_mod_ge_one.1, h_mod_ne_one.symm⟩

    have hQ_pow_not_inj : ¬Function.Injective (fun n => Q ^ n) := not_injective_infinite_finite _
    simp only [Function.Injective, not_forall, exists_prop] at hQ_pow_not_inj
    have ⟨a, b, hQ_pow_a_eq_Q_pow_b, ha_ne_b⟩ := hQ_pow_not_inj
    have ha_b_order : b > a ∨ a > b := Nat.lt_or_gt_of_ne ha_ne_b    
    cases ha_b_order with
    | inl hb_gt_a => exact ⟨b, a, hb_gt_a, hQ_pow_a_eq_Q_pow_b.symm⟩
    | inr ha_gt_b => exact ⟨a, b, ha_gt_b, hQ_pow_a_eq_Q_pow_b⟩

/-- Q has finite order -/
theorem Q_order_finite [mod : Mod] [hm : Fact (mod.n ≥ 1)] : ∃ c > 0, Q ^ c = 1 := by
  have ⟨a, b, ha_gt_b, hQ_pow_a_eq_Q_pow_b⟩ := Q_exists_pow_eq
  have a_ge_b : a ≥ b := Nat.le_of_lt ha_gt_b 
  have ha_sub_b_gt_zero : a - b > 0 := by simp only [ge_iff_le, gt_iff_lt, tsub_pos_iff_lt, ha_gt_b]
  have hQ_pow_c_eq_one : Q ^ (a - b) = 1 := by
    simp only [
      ge_iff_le, ne_eq, le_refl, tsub_eq_zero_of_le, pow_zero,
      Matrix.pow_sub' (Q) isUnit_Q_det (a_ge_b), ←hQ_pow_a_eq_Q_pow_b,
      Matrix.det_pow, ←Matrix.pow_sub' (Q) isUnit_Q_det (by rfl)
    ]
    
  exact ⟨a - b, ha_sub_b_gt_zero, hQ_pow_c_eq_one⟩

end FibMod