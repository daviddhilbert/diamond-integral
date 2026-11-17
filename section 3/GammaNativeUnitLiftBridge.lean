import «section 3».GammaNativeUnitElementaryLift
import «section 3».GammaMeasuredClassLift
import «section 3».GammaMeasuredPointFocus
import «section 5».Completed18LocalLift

/-! The native unit-form lift is the literal local measured lift. The
normalized point therefore has the actual elementary unit-form VF image,
with no volume-comparison input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeUnitLiftBridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundRVObject hc B k) : GammaGroundMeasuredVFHom hκ hs hr hv
      (gammaNativeUnitLift (hc := hc) (Section5.groundRVAt U).toGamma)
      (gammaGroundMeasuredObjectLift (.withZeroForm U)) :=
  gammaMeasuredHomOfCarrierEq hκ hs hr hv rfl
    (heq_of_eq (gammaDefSet_eq_of_carrierEq (Section5.groundRVAt_lift_domain U)))
    (fun _ _ _ => rfl)

theorem gammaMeasuredPoint_elementary_lift_class
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaGroundMeasuredObjectLift (gammaMeasuredPointZeroArity hc B)) =
      gammaGroundMeasuredVFClass hκ.le hs hr hv
        (gammaNativeUnitLift (hc := hc) (FiniteRV.gammaElementaryAt hκ.le hs h00 hr
          (Section5.groundRVAt (gammaMeasuredPointZeroArity hc B).underlying) 0 gammaMeasuredPoint_admissible).toGamma) := by
  obtain ⟨D⟩ := gammaMeasuredPoint_focus_exists (hc := hc) hκ hs h00 hr hg hB
  exact (gammaGroundMeasuredVFClass_iso hκ.le hs hr hv
    (gammaNativeUnitLiftBridge hκ.le hs hr hv (gammaMeasuredPointZeroArity hc B).underlying)).symm.trans
    (gammaGroundMeasuredVFClass_iso hκ.le hs hr hv (gammaNativeUnitElementaryHom hκ.le hs h00 hr hv
      (Section5.groundRVAt (gammaMeasuredPointZeroArity hc B).underlying) 0 gammaMeasuredPoint_admissible D))

end DiamondIntegral.Section3
