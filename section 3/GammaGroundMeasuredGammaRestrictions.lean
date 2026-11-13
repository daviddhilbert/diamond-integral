import «section 3».GammaGroundGammaCodeFormRestrictions
import «section 3».GammaGroundMeasuredGammaRVLift
import «section 3».GammaGroundGammaRVScissors
import «section 3».GammaGroundRVFamilyDescRestrictions
import «section 3».GammaGroundGammaScissors
/-! The full measured Gamma lift commutes with restricting every tagged
piece and inheriting its original Gamma form. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredGammaLiftForm_restrict (U : GammaGroundMeasuredGammaObject hc ground k)
    (X : Fin U.underlying.tags → GammaGroundGammaPiece hc ground k)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier) :
    gammaGroundMeasuredGammaLiftForm (U.restrict X hX) = (gammaGroundMeasuredGammaLiftForm U).comp
      (GammaGroundMap.inclusion (U.underlying.rvLift_restrict_subset X hX)) := by
  let P : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k) :=
    ⟨U.underlying.tags, fun i => (gammaGroundGammaCodeToRV (U.underlying.piece i)).image⟩
  let Y (i : Fin U.underlying.tags) : GammaGroundDefSet hc ground (rawRVSpace (M := M) k) := (gammaGroundGammaCodeToRV (X i)).image
  let hY (i : Fin U.underlying.tags) : (Y i).carrier ⊆ (P.piece i).carrier := gammaGroundGammaRVCodeLift_mono (hX i)
  let f (i : Fin U.underlying.tags) : GammaGroundMap (P.piece i) (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)) :=
    gammaGroundGammaRVCodeForm (U.underlying.piece i) (U.form i)
  have hf (i : Fin U.underlying.tags) :
      gammaGroundGammaRVCodeForm (X i) ((U.form i).comp (GammaGroundMap.inclusion (hX i))) =
        (f i).comp (GammaGroundMap.inclusion (hY i)) := gammaGroundGammaRVCodeForm_restrict (hX i) (U.form i)
  apply GammaGroundMap.ext
  intro a
  change gammaGroundRVFamilyDesc ⟨U.underlying.tags, Y⟩ (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc))
      (fun i => gammaGroundGammaRVCodeForm (X i) ((U.form i).comp (GammaGroundMap.inclusion (hX i)))) a =
    gammaGroundRVFamilyDesc P (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)) f
      (GammaGroundMap.inclusion (gammaGroundRVFamilyRealization_mono P.piece Y hY) a)
  calc
    _ = gammaGroundRVFamilyDesc ⟨U.underlying.tags, Y⟩ (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc))
        (fun i => (f i).comp (GammaGroundMap.inclusion (hY i))) a := by
      exact congrArg (fun F : ∀ i, GammaGroundMap (Y i) (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)) =>
        gammaGroundRVFamilyDesc ⟨U.underlying.tags, Y⟩ (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)) F a) (funext hf)
    _ = _ := gammaGroundRVFamilyDesc_restrict P (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)) f Y hY a

end DiamondIntegral.Section3
