import «section 3».MeasuredGammaProductLaws
import «section 3».GammaProductPairing

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

theorem measuredGammaProduct_combined_pair (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l)
    (a : A.underlying.Carrier) (b : B.underlying.Carrier) :
    (A.product B).combinedWeight (gammaProductPair A.underlying B.underlying a b) = A.combinedWeight a * B.combinedWeight b :=
  by
    have h := measuredGammaProduct_factor A B (gammaProductPair A.underlying B.underlying a b)
    have he : A.underlying.productCarrierEquiv B.underlying (gammaProductPair A.underlying B.underlying a b) = (a, b) :=
      (A.underlying.productCarrierEquiv B.underlying).apply_symm_apply (a, b)
    rw [he] at h
    exact h

def measuredGammaProductRightDistribHom (A : MeasuredGammaObject hc S k) (B D : MeasuredGammaObject hc S l) :
    MeasuredGammaHom (A.product (B.coprod D)) ((A.product B).coprod (A.product D)) where
  underlying := gammaProductRightDistribHom A.underlying B.underlying D.underlying
  preserves x := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (A.underlying.productCarrierEquiv (B.underlying.coprod D.underlying)).symm.surjective x
    rcases familyCoprod_cases B.underlying D.underlying b with ⟨b, rfl⟩ | ⟨d, rfl⟩
    · calc
        _ = A.combinedWeight a * (B.coprod D).combinedWeight (familyCoprodInl B.underlying D.underlying b) :=
          measuredGammaProduct_combined_pair A (B.coprod D) a _
        _ = A.combinedWeight a * B.combinedWeight b := congrArg (A.combinedWeight a * ·) (measuredGammaCoprod_combined_left B D b)
        _ = ((A.product B).coprod (A.product D)).combinedWeight
            (familyCoprodInl _ _ (gammaProductPair A.underlying B.underlying a b)) :=
          ((measuredGammaCoprod_combined_left (A.product B) (A.product D) _).trans
            (measuredGammaProduct_combined_pair A B a b)).symm
        _ = _ := congrArg ((A.product B).coprod (A.product D)).combinedWeight
          (gammaProductDistrib_pair_left A.underlying B.underlying D.underlying a b).symm
    · calc
        _ = A.combinedWeight a * (B.coprod D).combinedWeight (familyCoprodInr B.underlying D.underlying d) :=
          measuredGammaProduct_combined_pair A (B.coprod D) a _
        _ = A.combinedWeight a * D.combinedWeight d := congrArg (A.combinedWeight a * ·) (measuredGammaCoprod_combined_right B D d)
        _ = ((A.product B).coprod (A.product D)).combinedWeight
            (familyCoprodInr _ _ (gammaProductPair A.underlying D.underlying a d)) :=
          ((measuredGammaCoprod_combined_right (A.product B) (A.product D) _).trans
            (measuredGammaProduct_combined_pair A D a d)).symm
        _ = _ := congrArg ((A.product B).coprod (A.product D)).combinedWeight
          (gammaProductDistrib_pair_right A.underlying B.underlying D.underlying a d).symm

theorem measuredGammaClass_product_coprod (A : MeasuredGammaObject hc S k) (B D : MeasuredGammaObject hc S l) :
    measuredGammaClass (A.product (B.coprod D)) = measuredGammaClass (A.product B) + measuredGammaClass (A.product D) :=
  (measuredGammaClass_iso (asIso (show _ ⟶ _ from measuredGammaProductRightDistribHom A B D))).trans (measuredGammaClass_coprod _ _)

end DiamondIntegral.Section3
