import «section 3».GammaGroundRVProductPairLaws
import «section 3».GammaGroundMeasuredRVSemiring

/-! Genuine measured cartesian associativity, commutativity and units
retain all Gamma forms over the original complete Gamma ground. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l j n : ℕ}

def GammaGroundMeasuredRVObject.reindexVolume (U : GammaGroundMeasuredRVObject hc ground k)
    (e : Fin n ≃ Fin k) : GammaGroundMeasuredRVObject hc ground n := ⟨U.underlying.reindexVolume e, U.form⟩

@[simp] theorem GammaGroundMeasuredRVObject.reindex_combinedWeight
    (U : GammaGroundMeasuredRVObject hc ground k) (e : Fin n ≃ Fin k) (a : U.underlying.domain) :
    (U.reindexVolume e).combinedWeight a = U.combinedWeight a := by
  unfold GammaGroundMeasuredRVObject.combinedWeight
  change gammaGroundFormValue U.form a * (∏ i, Section2.rvFiniteValue (U.underlying.target a (e i))) = _
  exact congrArg (fun t => gammaGroundFormValue U.form a * t)
    (e.prod_comp (fun i => Section2.rvFiniteValue (U.underlying.target a i)))

def gammaGroundMeasuredRVProductCommHom (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) :
    GammaGroundMeasuredRVHom (U.product V) ((V.product U).reindexVolume finAddFlip) where
  bijection := gammaGroundRVProductCommBijection U.underlying V.underlying
  preserves p := by
    obtain ⟨a, b, rfl⟩ := exists_gammaGroundRVPackPair U.underlying.domain V.underlying.domain p
    rw [GammaGroundMeasuredRVObject.reindex_combinedWeight, gammaGroundRVProductCommBijection_pair]
    simp only [GammaGroundMeasuredRVObject.product_combined_pair]
    exact mul_comm _ _

def gammaGroundMeasuredRVProductAssocHom (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) (W : GammaGroundMeasuredRVObject hc ground j) :
    GammaGroundMeasuredRVHom ((U.product V).product W)
      ((U.product (V.product W)).reindexVolume (finCongr (Nat.add_assoc k l j))) where
  bijection := gammaGroundRVProductAssocBijection U.underlying V.underlying W.underlying
  preserves p := by
    obtain ⟨ab, c, rfl⟩ := exists_gammaGroundRVPackPair (U.product V).underlying.domain W.underlying.domain p
    obtain ⟨a, b, rfl⟩ := exists_gammaGroundRVPackPair U.underlying.domain V.underlying.domain ab
    rw [GammaGroundMeasuredRVObject.reindex_combinedWeight]
    change _ = (U.product (V.product W)).combinedWeight
      ((gammaGroundRVProductAssocBijection U.underlying V.underlying W.underlying).map _)
    have he := gammaGroundRVProductAssocBijection_pair U.underlying V.underlying W.underlying a b c
    calc
      _ = (U.combinedWeight a * V.combinedWeight b) * W.combinedWeight c := by
        simp only [GammaGroundMeasuredRVObject.product_combined_pair]
      _ = U.combinedWeight a * (V.combinedWeight b * W.combinedWeight c) := mul_assoc _ _ _
      _ = (U.product (V.product W)).combinedWeight
          (gammaGroundRVPackPair U.underlying.domain (V.product W).underlying.domain a
            (gammaGroundRVPackPair V.underlying.domain W.underlying.domain b c)) := by
        simp only [GammaGroundMeasuredRVObject.product_combined_pair]
      _ = _ := congrArg (U.product (V.product W)).combinedWeight he.symm

@[simp] theorem GammaGroundMeasuredRVObject.unit_combinedWeight
    (a : (GammaGroundMeasuredRVObject.unit hc ground).underlying.domain) :
    (GammaGroundMeasuredRVObject.unit hc ground).combinedWeight a = 1 := by
  simp [GammaGroundMeasuredRVObject.combinedWeight, GammaGroundMeasuredRVObject.unit,
    GammaGroundMeasuredRVObject.withZeroForm]

def gammaGroundMeasuredRVProductRightUnitHom (U : GammaGroundMeasuredRVObject hc ground k) :
    GammaGroundMeasuredRVHom (U.product (GammaGroundMeasuredRVObject.unit hc ground)) U where
  bijection := gammaGroundRVProductRightUnitBijection U.underlying
  preserves p := by
    rw [GammaGroundMeasuredRVObject.product_combined, GammaGroundMeasuredRVObject.unit_combinedWeight, mul_one]
    rfl

end DiamondIntegral.Section3
