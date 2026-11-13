import «section 3».GammaGroundMeasuredGammaProductLaws
import «section 3».GammaGroundGammaProductPairing
/-! The Gamma distributive tag permutation preserves the full measured
forms. Consequently actual cartesian products distribute on positive classes. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

theorem gammaGroundMeasuredGammaProduct_combined_pair (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l)
    (a : A.underlying.Carrier) (b : B.underlying.Carrier) :
    (A.product B).combinedWeight (gammaGroundGammaProductPair A.underlying B.underlying a b) = A.combinedWeight a * B.combinedWeight b :=
  by
    have h := gammaGroundMeasuredGammaProduct_factor A B (gammaGroundGammaProductPair A.underlying B.underlying a b)
    have he : A.underlying.productCarrierEquiv B.underlying (gammaGroundGammaProductPair A.underlying B.underlying a b) = (a, b) :=
      (A.underlying.productCarrierEquiv B.underlying).apply_symm_apply (a, b)
    rw [he] at h
    exact h

def gammaGroundMeasuredGammaProductRightDistribHom (A : GammaGroundMeasuredGammaObject hc ground k) (B D : GammaGroundMeasuredGammaObject hc ground l) :
    GammaGroundMeasuredGammaHom (A.product (B.coprod D)) ((A.product B).coprod (A.product D)) where
  underlying := gammaGroundGammaProductRightDistribHom A.underlying B.underlying D.underlying
  preserves x := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (A.underlying.productCarrierEquiv (B.underlying.coprod D.underlying)).symm.surjective x
    rcases gammaGroundFamilyCoprod_cases B.underlying D.underlying b with ⟨b, rfl⟩ | ⟨d, rfl⟩
    · calc
        _ = A.combinedWeight a * (B.coprod D).combinedWeight (gammaGroundFamilyCoprodInl B.underlying D.underlying b) :=
          gammaGroundMeasuredGammaProduct_combined_pair A (B.coprod D) a _
        _ = A.combinedWeight a * B.combinedWeight b := congrArg (A.combinedWeight a * ·) (gammaGroundMeasuredGammaCoprod_combined_left B D b)
        _ = ((A.product B).coprod (A.product D)).combinedWeight
            (gammaGroundFamilyCoprodInl _ _ (gammaGroundGammaProductPair A.underlying B.underlying a b)) :=
          ((gammaGroundMeasuredGammaCoprod_combined_left (A.product B) (A.product D) _).trans
            (gammaGroundMeasuredGammaProduct_combined_pair A B a b)).symm
        _ = _ := congrArg ((A.product B).coprod (A.product D)).combinedWeight
          (gammaGroundGammaProductDistrib_pair_left A.underlying B.underlying D.underlying a b).symm
    · calc
        _ = A.combinedWeight a * (B.coprod D).combinedWeight (gammaGroundFamilyCoprodInr B.underlying D.underlying d) :=
          gammaGroundMeasuredGammaProduct_combined_pair A (B.coprod D) a _
        _ = A.combinedWeight a * D.combinedWeight d := congrArg (A.combinedWeight a * ·) (gammaGroundMeasuredGammaCoprod_combined_right B D d)
        _ = ((A.product B).coprod (A.product D)).combinedWeight
            (gammaGroundFamilyCoprodInr _ _ (gammaGroundGammaProductPair A.underlying D.underlying a d)) :=
          ((gammaGroundMeasuredGammaCoprod_combined_right (A.product B) (A.product D) _).trans
            (gammaGroundMeasuredGammaProduct_combined_pair A D a d)).symm
        _ = _ := congrArg ((A.product B).coprod (A.product D)).combinedWeight
          (gammaGroundGammaProductDistrib_pair_right A.underlying B.underlying D.underlying a d).symm

theorem gammaGroundMeasuredGammaClass_product_coprod (A : GammaGroundMeasuredGammaObject hc ground k) (B D : GammaGroundMeasuredGammaObject hc ground l) :
    gammaGroundMeasuredGammaClass (A.product (B.coprod D)) = gammaGroundMeasuredGammaClass (A.product B) + gammaGroundMeasuredGammaClass (A.product D) :=
  (gammaGroundMeasuredGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaProductRightDistribHom A B D))).trans (gammaGroundMeasuredGammaClass_coprod _ _)

end DiamondIntegral.Section3
