import «section 3».GammaGroundGammaRVProductCodeMaps
import «section 3».GammaGroundMeasuredGammaProducts
import «section 3».GammaGroundMeasuredRVProductLaws
import «section 3».GammaGroundMeasuredRVIsomorphismClasses
import «section 3».GammaGroundMeasuredGammaProductWeights
/-! The measured Gamma lift respects cartesian products pointwise. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundMeasuredGammaProductLiftHom (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l) :
    GammaGroundMeasuredRVHom (A.product B).rvLift (A.rvLift.product B.rvLift) where
  bijection := gammaGroundGammaRVProductBijection A.underlying B.underlying
  preserves x := by
    obtain ⟨⟨i, c⟩, rfl⟩ := (A.product B).underlying.rvEncodeCode_surjective x
    obtain ⟨a, b, rfl⟩ := gammaGroundGammaProductCode_surjective
      (A.underlying.piece (finProdFinEquiv.symm i).1)
      (B.underlying.piece (finProdFinEquiv.symm i).2) c
    change _ = (A.rvLift.product B.rvLift).combinedWeight
      ((gammaGroundGammaRVProductBijection A.underlying B.underlying).map _)
    have he := gammaGroundGammaRVProductBijection_code A.underlying B.underlying
      (show Fin (A.underlying.tags * B.underlying.tags) from i) a b
    calc
      _ = (A.product B).combinedWeight ((A.product B).underlying.decode
          ⟨i, gammaGroundGammaProductCode _ _ a b⟩) := gammaGroundMeasuredGammaLift_combined _ _
      _ = A.combinedWeight (A.underlying.decode ⟨(finProdFinEquiv.symm i).1, a⟩) *
          B.combinedWeight (B.underlying.decode ⟨(finProdFinEquiv.symm i).2, b⟩) :=
        gammaGroundMeasuredGammaProduct_combined_code A B i a b
      _ = A.rvLift.combinedWeight (A.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).1, a⟩) *
          B.rvLift.combinedWeight (B.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
        rw [gammaGroundMeasuredGammaLift_combined, gammaGroundMeasuredGammaLift_combined]
      _ = (A.rvLift.product B.rvLift).combinedWeight
          (gammaGroundRVPackPair A.rvLift.underlying.domain B.rvLift.underlying.domain
            (A.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).1, a⟩)
            (B.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).2, b⟩)) :=
        (GammaGroundMeasuredRVObject.product_combined_pair A.rvLift B.rvLift _ _).symm
      _ = _ := congrArg (A.rvLift.product B.rvLift).combinedWeight he.symm

theorem gammaGroundMeasuredGammaRVClass_product (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l) :
    gammaGroundMeasuredRVClass (A.product B).rvLift = gammaGroundMeasuredRVClass (A.rvLift.product B.rvLift) :=
  gammaGroundMeasuredRVClass_iso (asIso (show (A.product B).rvLift ⟶ A.rvLift.product B.rvLift from
    gammaGroundMeasuredGammaProductLiftHom A B))

def gammaGroundMeasuredGammaUnitLiftHom :
    GammaGroundMeasuredRVHom (GammaGroundMeasuredGammaObject.unit hc ground).rvLift (GammaGroundMeasuredRVObject.unit (M := M) hc ground) where
  bijection := gammaGroundGammaRVUnitBijection
  preserves x := by
    obtain ⟨c, rfl⟩ := (GammaGroundMeasuredGammaObject.unit hc ground).underlying.rvEncodeCode_surjective x
    rw [gammaGroundMeasuredGammaLift_combined, GammaGroundMeasuredRVObject.unit_combinedWeight]
    change gammaGroundFormValue (gammaGroundOneForm _) _ * (∏ j : Fin 0, _) = 1
    rw [gammaGroundOneForm_value, Fin.prod_univ_zero, mul_one]

theorem gammaGroundMeasuredGammaRVClass_unit :
    gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.unit hc ground).rvLift =
      gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.unit (M := M) hc ground) :=
  gammaGroundMeasuredRVClass_iso (asIso (show (GammaGroundMeasuredGammaObject.unit hc ground).rvLift ⟶ GammaGroundMeasuredRVObject.unit hc ground from
    gammaGroundMeasuredGammaUnitLiftHom))

end DiamondIntegral.Section3
