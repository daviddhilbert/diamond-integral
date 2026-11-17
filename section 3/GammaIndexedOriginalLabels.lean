import «section 3».GammaNativeStructuralValues
import Integration7.GammaIndexedOrdinaryUnitComparisons

/-! Indexed finite-row presentations retain the original RV labels as
an actual original-ground coordinate projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d : ℕ}
variable {T : Set (Fin p → CanonicalRV.RVSort M)}
variable {R : (Fin p → CanonicalRV.RVSort M) → (Fin d → CanonicalRV.RVSort M) → Prop}

def gammaIndexedOriginalLabelMap
    (BP : GammaFiniteGraphPresentation B p d T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv)) (P : F.IndexedPresentation BP)
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hA : ∀ t ∈ T, F.rowDomain (rvValues t) ⊆ A.carrier) :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) A :=
  (gammaGroundRVSelectCoordinates (Fin.natAdd p)
    (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma))).corestrict (fun u => by
      let v := Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u
      have hv := (Set.ext_iff.mp P.domain_eq v.val).mp v.property
      exact hA _ hv.1 hv.2)

@[simp] theorem gammaIndexedOriginalLabelMap_val
    (BP : GammaFiniteGraphPresentation B p d T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv)) (P : F.IndexedPresentation BP)
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hA : ∀ t ∈ T, F.rowDomain (rvValues t) ⊆ A.carrier)
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    (gammaIndexedOriginalLabelMap BP F P A hA u).val = u.val ∘ Fin.natAdd p := rfl

end DiamondIntegral.Section3
