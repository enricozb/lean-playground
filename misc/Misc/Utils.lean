import Mathlib.Order.WellFoundedSet

namespace Utils

theorem dvd_le {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) : a ≤ b := by
  have ⟨c, hc⟩ := hab
  rw [hc]
  conv => lhs; rw [←mul_one a]
  apply Nat.mul_le_mul
  exact Nat.le_refl a
  show 0 < c
  apply Classical.byContradiction
  intro hnot_c_gt_zero
  have hc_eq_zero : c = 0 := Nat.eq_zero_of_not_pos hnot_c_gt_zero
  rw [hc_eq_zero, mul_zero] at hc
  exact hb hc

/-- If two sets are equal then their `Set.IsWf.min` are equal.
TODO: this should be generalized to any `α` with a `Preorder`. -/
theorem set_iswf_min_eq
  {s₁ s₂ : Set ℕ}
  (heq : s₁ = s₂)
  (hs₁ : Set.IsWf s₁) (hn₁ : s₁.Nonempty)
  (hs₂ : Set.IsWf s₂) (hn₂ : s₂.Nonempty)
  : Set.IsWf.min hs₁ hn₁ = Set.IsWf.min hs₂ hn₂ := by
      let a₁ := Set.IsWf.min hs₁ hn₁
      let a₂ := Set.IsWf.min hs₂ hn₂

      have ha₁_mem_s₁ : a₁ ∈ s₁ := Set.IsWf.min_mem hs₁ hn₁
      have ha₁_mem_s₂ : a₁ ∈ s₂ := by rw [←heq]; assumption
      have ha₂_mem_s₂ : a₂ ∈ s₂ := Set.IsWf.min_mem hs₂ hn₂
      have ha₂_mem_s₁ : a₂ ∈ s₁ := by rw [heq]; assumption
      
      apply Classical.byContradiction; intro hne;
      apply Or.elim (Nat.lt_or_gt.1 hne)

      · intro ha₁_lt_a₂
        exact Set.IsWf.not_lt_min hs₂ hn₂ ha₁_mem_s₂ ha₁_lt_a₂

      · intro ha₂_lt_a₁
        exact Set.IsWf.not_lt_min hs₁ hn₁ ha₂_mem_s₁ ha₂_lt_a₁

/-- Pisano periods for `m ≥ 1` are the minimum period of `fib`.
TODO: this should be generalized to any `α` with a `Preorder`.
-/
theorem set_iswf_min_iff {s : Set ℕ} (hs : Set.IsWf s) (hn : s.Nonempty) (p : ℕ) :
  Set.IsWf.min hs hn = p ↔ p ∈ s ∧ ∀ p' < p, p' ∉ s := by

  apply Iff.intro
  · intro hp_min
    have hp_mem : p ∈ s := by
      rw [←hp_min]
      apply Set.IsWf.min_mem

    apply And.intro hp_mem
    intro p' hp'_lt_p hp'mem
    have hnot_p'_lt_p : ¬p' < p := by
      rw [←hp_min]
      apply Set.IsWf.not_lt_min
      exact hp'mem

    exact hnot_p'_lt_p hp'_lt_p

  · intro ⟨hpmem, hp_min⟩
    let p' := Set.IsWf.min hs hn
    have hp'_mem : p' ∈ s := by apply Set.IsWf.min_mem

    -- assume p' ≠ p, then p' < p or p < p'
    apply Classical.byContradiction; intro h_ne_p; apply Or.elim (Nat.lt_or_gt.1 h_ne_p)

    · intro hp'_lt_p
      exact hp_min p' hp'_lt_p hp'_mem

    · intro hp_lt_p'
      have h_not_p_lt_p' : ¬ p < p' := by
        apply Set.IsWf.not_lt_min
        exact hpmem
      exact h_not_p_lt_p' hp_lt_p'

end Utils