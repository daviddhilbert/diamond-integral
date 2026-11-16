import «section 6».FocusCovarianceParameterLoci

/-! Universal tests on an entire graph and an arbitrary finite input
block give definable parameter loci. This includes invariance of the
current source and of every protected piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ι τ σ : Type} [Finite ι] [Finite τ] [Finite σ]

def graphUniversalParameterLocus (R : Set (ι ⊕ τ → M))
    (C : Set (ι ⊕ (τ ⊕ σ) → M)) : Set (ι → M) :=
  {t | ∀ x,Sum.elim t x ∈ R → ∀ y,Sum.elim t (Sum.elim x y) ∈ C}

theorem graphUniversalParameterLocus_definable (R : Set (ι ⊕ τ → M))
    (C : Set (ι ⊕ (τ ⊕ σ) → M)) (hR : S.Definable LRV R) (hC : S.Definable LRV C) :
    S.Definable LRV (graphUniversalParameterLocus R C) := by
  let edge : ι ⊕ τ → (ι ⊕ τ) ⊕ σ := Sum.inl
  let both : ι ⊕ (τ ⊕ σ) → (ι ⊕ τ) ⊕ σ :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  have hBad := (hR.preimage_comp edge).inter (hC.preimage_comp both).compl
  convert (hBad.exists_of_finite.exists_of_finite).compl using 1
  ext t
  have he (x : τ → M) (y : σ → M) : Sum.elim (Sum.elim t x) y ∘ edge=Sum.elim t x := rfl
  have hb (x : τ → M) (y : σ → M) : Sum.elim (Sum.elim t x) y ∘ both=Sum.elim t (Sum.elim x y) := by
    funext i; rcases i with i | (i | i) <;> rfl
  change (∀ x,Sum.elim t x ∈ R → ∀ y,Sum.elim t (Sum.elim x y) ∈ C) ↔
    ¬ ∃ (x : τ → M) (y : σ → M),Sum.elim (Sum.elim t x) y ∘ edge ∈ R ∧
      Sum.elim (Sum.elim t x) y ∘ both ∉ C
  simp only [he,hb,not_exists,not_and,not_not]
  constructor
  · intro h x y hx
    exact h x hx y
  · intro h x hx y
    exact h x y hx

end DiamondIntegral.Section6
