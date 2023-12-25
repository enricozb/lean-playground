import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Basic
import Std.Data.Rat.Basic

lemma nm_contradiction (n m : ℤ) (h : ((↑n : ℝ) / ↑m) ^ (↑m / ↑n) = 1 / 2) : n = m := by
  sorry

theorem exists_irrational_and_self_inv_pow_rational : ∃ x : ℝ, Irrational x ∧ ¬ Irrational (x ^ (1 / x)) := by
  
  let f (x : ℝ) : ℝ := x ^ (1 / x)
  
  -- not actually true; f x is continuous for x > 0, not sure how to encode that
  have h_cont : Continuous f := by sorry

  have ⟨x, hx⟩ : ∃ x : ℝ, f x = 1 / 2 := by
    apply Set.mem_range.mp
    apply mem_range_of_exists_le_of_exists_ge
    exact h_cont
    apply Exists.intro (1 / 2)
    norm_num
    apply Exists.intro 1
    norm_num

  -- by contradiction on (n / m) ^ (m / n) = 1 / 2 → n = m
  have h_x_irr : Irrational x := by
    apply (irrational_iff_ne_rational x).mpr
    intro n m hxnm
    rw [hxnm] at hx
    simp only at hx
    conv at hx => lhs; rw [one_div, inv_div]
    have := nm_contradiction n m hx
    rw [this] at hx
    sorry

  have h_half_rat : ¬ Irrational (1 / 2) := by
    intro h_irr
    rw [irrational_iff_ne_rational] at h_irr
    have h := h_irr 1 2
    simp only [one_div, Int.cast_one, Int.int_cast_ofNat, ne_eq, not_true] at h
  
  apply Exists.intro x
  apply And.intro h_x_irr
  rw [←hx] at h_half_rat
  exact h_half_rat