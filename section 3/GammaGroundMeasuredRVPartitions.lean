import «section 3».GammaGroundMeasuredRVMapCoproducts
import «section 3».GammaGroundRVPartitions

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundMeasuredRVPartitionHom (U : GammaGroundMeasuredRVObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    GammaGroundMeasuredRVHom
      ((U.restrict X hX).coprod (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1))) U where
  bijection := gammaGroundRVBijectionOfMapIso
    (gammaGroundRVMapPartitionIso (⟨U.underlying⟩ : GammaGroundRVMapObject hc ground k) X hX)
  preserves a := by
    let A := U.restrict X hX
    let B := U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1)
    let il : (⟨A.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨U.underlying⟩ := GammaGroundMap.inclusion hX
    let ir : (⟨B.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨U.underlying⟩ := GammaGroundMap.inclusion (fun _ h => h.1)
    change (A.coprod B).combinedWeight a = U.combinedWeight (gammaGroundRVMapDesc il ir a)
    rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
    · have ha : gammaGroundRVCoprodLeft A.underlying B.underlying u = a := Subtype.ext hu
      rw [← ha, gammaGroundMeasuredRVCoprod_combined_left]
      have hf := congrArg (fun h : (⟨A.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨U.underlying⟩ => h u)
        (gammaGroundRVMapInl_desc il ir)
      change U.combinedWeight (il u) = _
      exact congrArg U.combinedWeight hf.symm
    · have ha : gammaGroundRVCoprodRight A.underlying B.underlying v = a := Subtype.ext hv
      rw [← ha, gammaGroundMeasuredRVCoprod_combined_right]
      have hf := congrArg (fun h : (⟨B.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨U.underlying⟩ => h v)
        (gammaGroundRVMapInr_desc il ir)
      change U.combinedWeight (ir v) = _
      exact congrArg U.combinedWeight hf.symm

end DiamondIntegral.Section3
