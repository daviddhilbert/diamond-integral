import «section 3».GammaZeroMeasuredCuts

/-! A genuine positive additive descent in degree zero. The invariant
respects literal cuts and retains arbitrary finite families of weights. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaZeroMeasuredVFDescentInvariant :
    PositiveAdditiveGrothendieck.Invariant
      (gammaGroundMeasuredVFPresentation (hc := hc) (ground := B) hκ hs hS hv 0)
      (A := GammaGroundMeasuredRVKPlus hc B 0) where
  toFun U := gammaGroundMeasuredRVClass (gammaZeroRVOfVF U)
  iso := by
    rintro U V ⟨f⟩
    exact gammaGroundMeasuredRVClass_iso (asIso (gammaZeroRVHomOfVFHom f))
  empty := by
    apply gammaGroundMeasuredRVClass_of_empty
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨u,_⟩
    exact u.property
  scissor := by
    rintro A D E F ⟨U,X,hX,hA,hD,hE,hF⟩
    subst A
    subst D
    subst E
    subst F
    have hEmpty : gammaGroundMeasuredRVClass
        (gammaZeroRVOfVF (GammaGroundMeasuredVFData.empty hc B 0)) = 0 := by
      apply gammaGroundMeasuredRVClass_of_empty
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨u,_⟩
      exact u.property
    change gammaGroundMeasuredRVClass (gammaZeroRVOfVF (U.restrict X hX)) +
      gammaGroundMeasuredRVClass (gammaZeroRVOfVF (U.restrict (U.domain.sdiff X) (fun _ h => h.1))) =
      gammaGroundMeasuredRVClass (gammaZeroRVOfVF U) + _
    rw [hEmpty,add_zero,
      gammaGroundMeasuredRVClass_iso (gammaZeroRVRestrictionIso U X hX),
      gammaGroundMeasuredRVClass_iso
        (gammaZeroRVRestrictionIso U (U.domain.sdiff X) (fun _ h => h.1))]
    let Y := gammaZeroCutImage U X hX
    let Y' := gammaZeroCutImage U (U.domain.sdiff X) (fun _ h => h.1)
    let W := gammaZeroRVOfVF U
    let f : W.restrict Y' (gammaZeroCutImage_subset U (U.domain.sdiff X) (fun _ h => h.1)) ⟶
        W.restrict (W.underlying.domain.sdiff Y) (fun _ h => h.1) := {
      bijection := GammaGroundBijection.ofCarrierEq (gammaZeroCutImage_complement U X hX)
      preserves := fun _ => rfl }
    rw [gammaGroundMeasuredRVClass_iso (asIso f)]
    exact gammaGroundMeasuredRVClass_scissor W Y (gammaZeroCutImage_subset U X hX)

def gammaZeroMeasuredVFClassDescent :
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ hs hS hv 0 →+
      GammaGroundMeasuredRVKPlus hc B 0 :=
  PositiveAdditiveGrothendieck.lift
    (gammaGroundMeasuredVFPresentation (hc := hc) (ground := B) hκ hs hS hv 0)
    (gammaZeroMeasuredVFDescentInvariant hκ hs hS hv)

@[simp] theorem gammaZeroMeasuredVFClassDescent_class (U : GammaGroundZeroMeasuredVF hc B) :
    gammaZeroMeasuredVFClassDescent hκ hs hS hv
      (gammaGroundMeasuredVFClass hκ hs hS hv U) =
        gammaGroundMeasuredRVClass (gammaZeroRVOfVF U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

@[simp] theorem gammaZeroMeasuredVFClassDescent_lift (U : GammaGroundMeasuredRVObject hc B 0) :
    gammaZeroMeasuredVFClassDescent hκ hs hS hv
      (gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift U)) =
        gammaGroundMeasuredRVClass U := by
  rw [gammaZeroMeasuredVFClassDescent_class,
    gammaGroundMeasuredRVClass_iso (gammaZeroRVRepresentationIso U)]

theorem gammaZeroMeasuredLift_class_injective {U V : GammaGroundMeasuredRVObject hc B 0}
    (h : gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift U) =
      gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift V)) :
    gammaGroundMeasuredRVClass U = gammaGroundMeasuredRVClass V := by
  simpa only [gammaZeroMeasuredVFClassDescent_lift] using
    congrArg (gammaZeroMeasuredVFClassDescent hκ hs hS hv) h

end DiamondIntegral.Section3
