import Section9.LiftLabelRepresentatives
import «section 6».MeasuredRVIsomorphisms
import «section 6».MixedGammaJacobianException

/-! The product of VF values on a literal RV lift is exactly the
Gamma volume of its retained label. Actual label-graph membership
identifies the target label, including every auxiliary coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open scoped BigOperators

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem liftLabelMap_volume (U : RVObject (M := M) S k) (p : rvLift U) :
    U.value (liftLabelMap U p) = SpecialTransformations.Section4.tupleRV p.val.1 := by
  obtain ⟨u,hu,hvol⟩ := p.property
  have he : liftLabelMap U p = u := Subtype.ext hu.symm
  exact he ▸ hvol

theorem rvLift_volume_gamma_value (U : MeasuredRVObject (M := M) S k) (p : rvLift U.object) :
    (U.volumeGamma (liftLabelMap U.object p)).val = vfValue (∏ i, p.val.1 i) := by
  change Values.gammaValHom (∏ i, Values.gammaOf (U.object.value (liftLabelMap U.object p) i)
    (U.nonzero (liftLabelMap U.object p) i)) = _
  rw [map_prod]
  change (∏ i, Values.vrv (U.object.value (liftLabelMap U.object p) i)) = Values.vfValueHom (∏ i, p.val.1 i)
  rw [map_prod,liftLabelMap_volume]
  rfl

theorem liftLabelMap_target_of_graph
    {U V : RVObject (M := M) S k} (F : Map U.domain V.domain)
    (f : Map (rvLift U) (rvLift V))
    (hLabel : ∀ p : rvLift U, F.graph p.val.2 (f p).val.2) (p : rvLift U) :
    liftLabelMap V (f p) = F (liftLabelMap U p) := by
  obtain ⟨u,hu,hF⟩ := hLabel p
  have he : u = liftLabelMap U p := Subtype.ext hu
  subst u
  exact Subtype.ext hF.symm

end DiamondIntegral.Section6
