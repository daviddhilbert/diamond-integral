import «section 3».GammaRVFiniteRows
import «section 3».GammaRVFibreDichotomy
import «section 3».FiniteColumnPartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

/-- A finite/cofinite Gamma-indexed family has only finitely many distinct
columns. This uses proved finite projection, not an orthogonality input. -/
theorem gammaRV_finite_columns_of_finite_sides {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    (F : GammaRVFamily (M := M) S) (D : Set M) (hD : DefinableAt S .rv D)
    (hside : ∀ γ, {t | F.relation γ t}.Finite ∨ {t | t ∈ D ∧ ¬ F.relation γ t}.Finite) :
    (relationColumn F.relation '' D).Finite := by
  obtain ⟨N,hT⟩ := gammaRV_finite_minority hκ hs h00 hsmall F D hD hside
  let T := (gammaRVMinority F D hD N).nonemptyDomain
  apply finite_columns_of_constant_off_finite F.relation D T hT
  intro x hx u hu hxT huT
  ext γ
  change F.relation γ x ↔ F.relation γ u
  by_cases h : gammaRVSmallRow F N γ
  · apply iff_of_false
    · intro hg
      exact hxT ⟨γ,Or.inl ⟨h,hg⟩⟩
    · intro hg
      exact huT ⟨γ,Or.inl ⟨h,hg⟩⟩
  · apply iff_of_true
    · by_contra hg
      exact hxT ⟨γ,Or.inr ⟨h,hx,hg⟩⟩
    · by_contra hg
      exact huT ⟨γ,Or.inr ⟨h,hu,hg⟩⟩

theorem gammaRV_value_fibre_finite_columns {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    (F : GammaRVFamily (M := M) S) (D : Set M) (hD : DefinableAt S .rv D)
    (δ : Values.Gamma (M := M))
    (hδ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = δ.val)
    (hsub : ∀ γ t, F.relation γ t → t ∈ D) :
    (relationColumn F.relation '' D).Finite :=
  gammaRV_finite_columns_of_finite_sides hκ hs h00 hsmall F D hD
    (gammaRV_value_fibre_dichotomy F D hD δ hδ hsub)
end DiamondIntegral.Section3
