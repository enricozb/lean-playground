import «Misc».Logic.Bool.Signature

/--
  A signature is _functional complete_ if any function of any arity is
  representable by some formula.
-/
def Signature.functional_complete {S : Signature} : Prop :=
  ∀ {n} (f : [Bool; n] → Bool), ∃ (φ : S.Formula n), f = φ.value

/--
  A signature `S₁` is a subset of a signature `S₂` if the symbols
  in `S₁` are also in `S₂`.
-/
def Signature.subset (S₁ S₂ : Signature) : Prop :=
  ∀ (n : ℕ), S₁.symbols n ⊆ S₂.symbols n

/--
  A signature `S₁` is _subsumes_ a signature `S₂` if every _formula_
  `φ` of signature `S₂` can be represented by a formula `ψ` of signature `S₁`.
-/
def Signature.subsumes (S₁ S₂ : Signature) :=
  ∀ {n} (φ : S₂.Formula n), (ψ : S₁.Formula n) ×' (φ.value = ψ.value)

/--
  Embeds a formula `φ` of a signature `S₁` into a signature `S₂` assuming `S₁ ⊆ S₂`. 
-/
def Signature.subset_map {S₁ S₂ : Signature} (hs : S₁.subset S₂) (φ : S₁.Formula n) : S₂.Formula n :=
  match φ with
  | Formula.var i => Formula.var i
  | Formula.apply f hf ψs =>
    Formula.apply f
      (Set.mem_of_subset_of_mem (hs _) hf)
      (fun i => subset_map hs (ψs i))

/--
  If signature `S₁` is a subset of signature `S₂`, then `S₂` subsumes `S₁`.
-/
def Signature.subset_subsumes {S₁ S₂ : Signature} (hs : S₁.subset S₂) :
  S₂.subsumes S₁ := by
    intro n φ
    let ψ := subset_map hs φ
    have h : φ.value = (subset_map hs φ).value := by
      funext vars
      induction φ
      · rfl
      · rename_i a f hf φs hφs
        have hφ : (Formula.apply f hf φs).value vars = f.2 (fun i => (φs i).value vars) := rfl
        have hψ : ψ.value vars = f.2 (fun i => (subset_map hs (φs i)).value vars) := rfl
        rw [hφ, hψ, funext hφs]
    
    exact ⟨ψ, h⟩

/--
  If a signature `S₁` can subsume a functional complete signature `S₂`, then
  `S₁` is also functional complete.
-/
theorem Signature.subsumes_functional_complete {S₁ S₂ : Signature} (hfc : S₁.functional_complete) (hs : S₂.subsumes S₁) :
  S₂.functional_complete := by
  intro n f
  have ⟨φ, hφ⟩ := hfc f
  have ⟨ψ, hψ⟩ := hs φ
  rw [hφ.symm] at hψ
  exact ⟨ψ, hψ⟩

/--
  If a signature `S₁` is the subset of a functional complete signature `S₂`, then
  `S₁` is also functional complete.
-/
theorem Signature.subset_functional_complete {S₁ S₂ : Signature} (hfc : S₁.functional_complete) (hs : S₁.subset S₂) :
  S₂.functional_complete := by
  have hr : S₂.subsumes S₁ := S₁.subset_subsumes hs
  exact @subsumes_functional_complete S₁ S₂ hfc hr
