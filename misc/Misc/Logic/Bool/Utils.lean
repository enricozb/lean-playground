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
