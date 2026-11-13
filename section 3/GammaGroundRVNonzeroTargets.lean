import «section 3».GammaGroundRVDimension
import «section 3».RVDimensionBridge
import «section 3».GammaGroundRVRankUpper
import «section 3».GammaGroundRVFiniteMapRank
import «section 3».GammaGroundRealization
import «section 3».GammaGroundFiniteGluing
import Section4.RVDimensionRank
import Section4.GammaRVIndependence
import Section3.GammaProjection
import «section 3».GammaGroundRealFibres
import «section 3».GammaGroundMapImages
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundSyntaxBridge
import Section4.RelationFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {n : ℕ}
variable {k : ℕ}
theorem gammaGroundRVHasFiniteMap_iff_nonzero
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    GammaGroundRVHasFiniteMap A k ↔
      ∃ f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)),
        f.FiniteFibres ∧ ∀ a i, ((f a).val i).val ≠ iRVZero := by
  constructor
  · rintro ⟨f, hf⟩
    let U := GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)
    let C : GammaGroundMap U U := GammaGroundMap.ofGlobal _ _
      (cleanRVMap (DefSet.univ (rawRVSpace (M := M) k) ground.real)) (fun _ => Set.mem_univ _)
    have hC : C.FiniteFibres := cleanRVMap_finite (DefSet.univ (rawRVSpace (M := M) k) ground.real)
    refine ⟨C.comp f, hC.comp hf, ?_⟩
    intro a i
    exact cleanRV_nonzero (f a).val i
  · rintro ⟨f, hf, _⟩
    exact ⟨f, hf⟩

end DiamondIntegral.Section3
