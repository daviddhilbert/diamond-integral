import «section 3».GammaNativeRetainedRVIsomorphisms
import «section 3».GammaGroundFormExtensionByOne

/-! The universal internal RV presentation changes only its code base.
Actual original-Gamma isomorphisms, coordinates and old labels survive
literally, so the existing geometric exports can carry total Gamma forms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def gammaNativeFiniteAt (U : GammaRVFiniteObject B n) : GammaObjectAt B Set.univ n :=
  gammaObjectAtExtend U (Set.subset_univ _)

def gammaNativeFiniteIso {U V : GammaRVFiniteObject B n}
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    GammaRVIso (gammaNativeFiniteAt U).toGamma.toGammaRVObject (gammaNativeFiniteAt V).toGamma.toGammaRVObject :=
  gammaIsoOfFiniteEquiv (gammaNativeFiniteAt U).toGamma (gammaNativeFiniteAt V).toGamma e.equiv e.graph e.weight

def gammaNativeTotalRVForm (U : GammaObjectAt B Set.univ n)
    (ρ : Fin r → Fin (rvObjectArity U.object.obj))
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) r))) :=
  gammaNativeRVRetainedForm U (GammaGroundDefSet.univ hc B (rawRVSpace r)) ρ (fun _ => Set.mem_univ _) ω

end DiamondIntegral.Section3
