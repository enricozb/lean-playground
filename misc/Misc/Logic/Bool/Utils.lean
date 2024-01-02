import Mathlib.Data.FinEnum

/--
  A notation for vectors.

  A definition cannot be used as inductive constructors can't contain `def`s.
-/
notation "[" α ";" n "]" => Fin n → α

instance : FinEnum Bool := ⟨
  -- card
  2,
  -- mappings between Bool and Fin 2
  (fun b => if b then 1 else 0),
  (fun i => if i = 0 then false else true),
  -- proofs that above maps are inverses of each other
  (by simp only),
  (by simp only)
⟩

/-- Folds over `Fin n` from the right: `foldr 3 f x = f 0 (f 1 (f 2 x))`. -/
-- TODO: this is in std4 now, should update...
@[inline] def Fin.foldr (n) (f : Fin n → α → α) (init : α) : α := loop ⟨n, Nat.le_refl n⟩ init where
  /-- Inner loop for `Fin.foldr`. `Fin.foldr.loop n f i x = f 0 (f ... (f (i-1) x))`  -/
  loop : {i // i ≤ n} → α → α
  | ⟨0, _⟩, x => x
  | ⟨i+1, h⟩, x => loop ⟨i, Nat.le_of_lt h⟩ (f ⟨i, h⟩ x)
