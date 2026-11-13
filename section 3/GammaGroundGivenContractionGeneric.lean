import «section 3».GammaGroundUnitFamilyCodeTransport
import «section 3».GammaGroundFamilyEqualizers
import «section 3».GammaGroundGenericFullPreimages
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

/-- Pointwise contraction implies generic agreement on every whole
source piece. The converse is not asserted for the original RV lift. -/
theorem gammaGroundUnitFamily_contraction_is_generic {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (A D : GammaGroundGammaObject hc B n)
    (H : GammaGroundFamilyBijection A D) (L : GammaGroundFamilyBijection A.unitFamily D.unitFamily)
    (hL : ∀ u, D.unitValueFamilyMap.toFun (L.equiv u) = H.equiv (A.unitValueFamilyMap.toFun u)) :
    ∀ i, (gammaGroundRVGenericValueImage hs h00 B hsmall
      ((D.unitValueFamilyMap.comp L.toFamilyMap).equalizerPiece
        (H.toFamilyMap.comp A.unitValueFamilyMap) i)).carrier = (A.piece i).carrier := by
  intro i
  have hE : (D.unitValueFamilyMap.comp L.toFamilyMap).equalizerPiece
      (H.toFamilyMap.comp A.unitValueFamilyMap) i = gammaGroundRVUnitGammaPreimage (A.piece i) := by
    let F := D.unitValueFamilyMap.comp L.toFamilyMap
    let G := H.toFamilyMap.comp A.unitValueFamilyMap
    have hcarriers : (F.equalizerPiece G i).carrier = (A.unitFamily.piece i).carrier := by
      apply Set.Subset.antisymm (F.equalizerPiece_subset G i)
      intro x hx
      exact (F.mem_equalizerPiece_at G i ⟨x,hx⟩).mpr (hL ⟨i,⟨x,hx⟩⟩)
    have heq (X Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
        (he : X.carrier = Y.carrier) : X = Y := by
      cases X
      cases Y
      cases he
      rfl
    exact heq _ _ hcarriers
  rw [hE]
  exact gammaGroundRVGenericValueImage_full_preimage hs h00 B hsmall hκ (A.piece i)

end DiamondIntegral.Section3
