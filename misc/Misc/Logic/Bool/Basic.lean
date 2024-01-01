import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Set
import Mathlib.Tactic.LibrarySearch
import «Misc».Logic.Bool.FunctionalComplete

def sig_tnoa := Signature.mk₁₂ {(¬)} {(∨), (∧)}
def sig_no := Signature.mk₁₂ {(¬)} {(∨)}
def sig_na := Signature.mk₁₂ {(¬)} {(∧)}

def sig_tnoa_subsumes_nOA : sig_tnoa.subsumes sig_nOA := fun {n} φ =>
  match φ with
  | Signature.Formula.var i => ⟨Signature.Formula.var i, rfl⟩
  | @Signature.Formula.apply _ _ a f hf φs =>
    match a with
    | 0 =>
      -- TODO: simplify this if-statement with some lemmas, esp the final `else`.
      if h_or : f.repr = "⋁" then
        -- should actually be false (or bot or something, don't need another symbol though)
        ⟨@Signature.Formula.apply sig_tnoa n 0 (⊤) _ _, _⟩
      else if h_and : f.repr = "⋀" then
        ⟨@Signature.Formula.apply sig_tnoa n 0 (⊤) _ _, _⟩
      else by
        have hf : f.repr = "⋁" ∨ f.repr = "⋀" := by
          apply Or.elim hf
          · intro hf_or; apply Or.inl; rw [hf_or]
          · intro hf_and; apply Or.inr; rw [hf_and]
        have := not_or.mpr ⟨h_or, h_and⟩ hf
        contradiction
    | 1 => sorry
    | _ => sorry

  -- intro a f hf
  -- match a with
  -- | 0 =>
  --   simp [bigand', bigor', *] at hf

  --   if h_or : f.repr = "⋁" then
  --     exact ⟨fun _ => false, rfl⟩
  --   else if h_and : f.repr = "⋀" then
  --     sorry
  --   else
  --     have hf : f.repr = "⋁" ∨ f.repr = "⋀" := by
  --       apply Or.elim hf
  --       · intro hf_or; apply Or.inl; rw [hf_or]
  --       · intro hf_and; apply Or.inr; rw [hf_and]
  --     have := not_or.mpr ⟨h_or, h_and⟩ hf
  --     contradiction

  -- | 1 => sorry
  -- | 2 => sorry
  -- | n => sorry


-- theorem sig_noa_subsumes_nOA : sig_noa.subsumes sig_nOA := by
--   intro n φ

--   let rec embed (φ : sig_nOA.Formula n) : sig_noa.Formula n :=
--     match φ with
--     | Signature.Formula.var i => Signature.Formula.var i
--     | Signature.Formula.apply a f hf φs => match a with
--       | 0 => by
--         have : f = (⋁ 0) := hf
--         exact 
--       | 1 => by
--         have : f = (¬) ∨ f = (⋁ 1) := hf
--       | 2 => sorry
--       | n => sorry

--   let ψ := embed φ
--   have hψ : φ.value = ψ.value := sorry
  
--   exact ⟨ψ, hψ⟩ 

/--
  Theorem 2.1 from Chapter 1.

  The signature `{⊤, ¬, ∧, ∨}` is functional complete.
-/
theorem sig_tnoa_functional_complete : sig_tnoa.functional_complete :=
  Signature.subsumes_functional_complete
    sig_nOA_functional_complete
    sig_tnoa_subsumes_nOA
