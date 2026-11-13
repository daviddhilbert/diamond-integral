import «section 3».GammaGroundFamilyBranchImages
import «section 3».GammaGroundGammaCategories
import «section 3».GammaGroundAffineFiniteCover
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}
variable {A D : GammaGroundGammaObject hc B n}

/-- A finite original-ground unimodular partition on each source/target
branch. Since both tag sets are finite, this is a finite partition of
the whole family; the translation coefficients are actual definable RV
points, never arbitrary names for Gamma values. -/
def GammaGroundPiecewiseGLZ (H : GammaGroundFamilyBijection A D) : Prop :=
  ∀ i j, ∃ N : ℕ, ∃ F : Fin N → OriginalGroundAffineRVFormula hc B n,
    ∃ P : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)),
      (∀ q, (P q).carrier ⊆ (H.toFamilyMap.branchSource i j).carrier) ∧
      (∀ γ : H.toFamilyMap.branchSource i j, ∃! q, γ.val ∈ (P q).carrier) ∧
      ∀ q (γ : H.toFamilyMap.branchSource i j), γ.val ∈ (P q).carrier →
        ((H.toFamilyMap.branchMap i j) γ).val = rvUnitTupleValues (F q).coefficient *
          integerMonomialMap (G := Values.Gamma (M := M)) (F q).matrix γ.val

/-- Compactness upgrades pointwise formulas to the finite branchwise
piecewise-GL(Z) criterion, over exactly the original ground. -/
theorem gammaGroundPiecewiseGLZ_of_pointwise {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (H : GammaGroundFamilyBijection A D)
    (hpoint : ∀ γ : A.Carrier, ∃ F : OriginalGroundAffineRVFormula hc B n,
      (H.equiv γ).2.val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.2.val) : GammaGroundPiecewiseGLZ H := by
  intro i j
  apply gammaGroundAffine_finite_partition hκ hs hsmall hγsmall
    (H.toFamilyMap.branchSource i j) (H.toFamilyMap.branchMap i j).image (H.branchBijection i j).map
  intro γ
  exact hpoint ⟨i,⟨γ.val,H.toFamilyMap.branchSource_subset i j γ.property⟩⟩

/-- The finite criterion in particular gives a unimodular formula at
each actual tagged Gamma point. -/
theorem gammaGroundPiecewiseGLZ_pointwise (H : GammaGroundFamilyBijection A D) (hH : GammaGroundPiecewiseGLZ H)
    (γ : A.Carrier) : ∃ F : OriginalGroundAffineRVFormula hc B n,
      (H.equiv γ).2.val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.2.val := by
  let i := γ.1
  let j := (H.equiv γ).1
  have hm : γ.2.val ∈ (H.toFamilyMap.branchSource i j).carrier :=
    (H.toFamilyMap.mem_branchSource_iff_tag i j γ.2).mpr rfl
  let a : H.toFamilyMap.branchSource i j := ⟨γ.2.val,hm⟩
  obtain ⟨N,F,P,_,hcover,hform⟩ := hH i j
  obtain ⟨q,hq,_⟩ := hcover a
  exact ⟨F q,hform q a hq⟩

end DiamondIntegral.Section3
