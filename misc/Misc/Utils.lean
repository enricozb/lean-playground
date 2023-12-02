import Mathlib.Order.WellFoundedSet

namespace Utils

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

end Utils