import «section 3».GammaNativeMeasuredNormalization
import IntegrationSection6.GammaFiniteRestrictionIsomorphisms
import IntegrationSection6.GammaWeightSeparation

/-! Actual original-ground RV isomorphisms restrict to their full-weight
parts. The restricted map is the original label map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaNativeHighRestrictionIso {U V : GammaObjectAt B S (n+1)} (e : GammaIsoAt U V) :
    GammaIsoAt (gammaHighRestrictionAt U) (gammaHighRestrictionAt V) := by
  let A := @complement M N S (n+1) U.object.obj (@rvLowDomain M N S n U.object.obj)
  let D := @complement M N S (n+1) V.object.obj (@rvLowDomain M N S n V.object.obj)
  apply gammaRestrictIsoAt e A D (fun _ h => h.1) (fun _ h => h.1)
    (gammaHighRestrictionAt U).domain_graph (gammaHighRestrictionAt V).domain_graph
  intro u
  have hw := gammaIsoAt_normalized_weight e u
  constructor
  · rintro ⟨_,hu⟩
    refine ⟨(isoAtMap e.iso u).property,?_⟩
    intro hv
    exact hu ((@mem_rvLowDomain M N S n U.object.obj u).mpr
      (hw.le.trans ((@mem_rvLowDomain M N S n V.object.obj (isoAtMap e.iso u)).mp hv)))
  · rintro ⟨_,hv⟩
    refine ⟨u.property,?_⟩
    intro hu
    exact hv ((@mem_rvLowDomain M N S n V.object.obj (isoAtMap e.iso u)).mpr
      (hw.symm.le.trans ((@mem_rvLowDomain M N S n U.object.obj u).mp hu)))

theorem gammaNativeHighRestrictionIso_value {U V : GammaObjectAt B S (n+1)} (e : GammaIsoAt U V)
    (u : rvObjectDomain (gammaHighRestrictionAt U).object.obj) :
    ((gammaNativeHighRestrictionIso e).toGamma.equiv u).val =
      (e.toGamma.equiv ⟨u.val,u.property.1⟩).val := rfl

end DiamondIntegral.Section3
