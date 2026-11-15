import «section 5».GammaRVTaggedFamilies
import «section 3».RVDimensionBridge
import «section 3».GammaGroundRESScissors

/-! Literal finite-value RV domains over a mixed Gamma ground are
actual RES objects, using the same finite zero-to-one label map as in
the original real-base presentation. The domain and base are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : GammaParameters.Base (M := M))

def gammaGroundCleanRVMap {n : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace n)) :=
  (GammaGroundMap.ofReal (cleanRVMap (DefSet.univ (rawRVSpace n) B.real))).restrict (fun _ _ => trivial)

theorem gammaGroundCleanRVMap_finite {n : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    (gammaGroundCleanRVMap hc B A).FiniteFibres := by
  let f := GammaGroundMap.ofReal (hc := hc) (ground := B)
    (cleanRVMap (DefSet.univ (rawRVSpace (M := M) n) B.real))
  have hf : f.FiniteFibres := cleanRVMap_finite _
  exact hf.comp (GammaGroundMap.finiteFibres_of_injective
    (show Function.Injective (GammaGroundMap.inclusion (A := A)
      (B := GammaGroundDefSet.univ hc B (rawRVSpace n)) (fun _ _ => trivial)) from
        fun _ _ h => Subtype.ext (congrArg
          (fun z : GammaGroundDefSet.univ hc B (rawRVSpace n) => z.val) h)))

def nativeRESObjectOfGammaSet {n : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (hA : GammaRVFiniteValues hc B A) : GammaGroundRESObject hc B n :=
  ⟨{
    arity := n
    domain := A
    volume := gammaGroundCleanRVMap hc B A
    finite := gammaGroundCleanRVMap_finite hc B A
    nonzero := by
      intro a i
      simpa only [gammaGroundCleanRVMap, GammaGroundMap.restrict, GammaGroundMap.comp,
        GammaGroundMap.inclusion, GammaGroundMap.ofReal, cleanRVMap, Map.ofCodes_apply] using
        cleanRV_nonzero a.val i }, hA⟩

theorem nativeRESObjectOfGammaSet_domain {n : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (hA : GammaRVFiniteValues hc B A) : (nativeRESObjectOfGammaSet hc B A hA).obj.domain = A := rfl

end DiamondIntegral.Section5
