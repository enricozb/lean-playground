import Mathlib.Data.Nat.Basic

inductive Vector (α : Type u) : ℕ → Type u where
| nil : Vector α 0
| cons {n} : α → Vector α n → Vector α (n + 1)

/-
  TODO:
    - Vector α n is Finite if α is Finite
-/