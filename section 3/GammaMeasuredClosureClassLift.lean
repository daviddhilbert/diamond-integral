import «section 3».GammaMeasuredHomLiftClosure
import «section 3».GammaMeasuredClassSurjectivity
import «section 3».GammaGroundContext
import «section 2».GeneralDiscPoints

/-! The forward degreewise measured lift at the exact manuscript
context. Only genuine VF generation is assumed; definable closure is
internal and eliminated before constructing any local measured arrow. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hB : VFGammaGeneratedBase (closureBase B))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaMeasuredClosureArrowLift {n : ℕ} {U V : GammaGroundMeasuredRVObject hc B n}
    (e : GammaGroundMeasuredRVHom U V) :
    GammaGroundMeasuredVFHom hκ.le hs hr hv (gammaGroundMeasuredObjectLift U) (gammaGroundMeasuredObjectLift V) := by
  cases n with
  | zero => exact gammaGroundZeroMeasuredRVLiftHom e
  | succ n =>
    let H := gammaMeasuredHom_lift_bijection_closure hκ hs h00 hr hγ hB hv e
    exact gammaPositiveMeasuredHomOfBijection hκ.le hs hr hv H.choose H.choose_spec.2

def gammaMeasuredClosureRVLiftInvariant :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundMeasuredRVPresentation hc B k)
      (A := GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ.le hs hr hv k) where
  toFun U := gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaGroundMeasuredObjectLift U)
  iso := by
    rintro U V ⟨e⟩
    exact gammaGroundMeasuredVFClass_iso hκ.le hs hr hv
      (gammaMeasuredClosureArrowLift hκ hs h00 hr hγ hB hv e.hom)
  empty := gammaMeasuredLift_class_empty hκ.le hs hr hv
  scissor := by
    rintro A D E F ⟨U,X,hX,hA,hD,hE,hF⟩
    subst A
    subst D
    subst E
    subst F
    simpa only [gammaMeasuredLift_class_empty hκ.le hs hr hv,add_zero] using
      gammaMeasuredLift_class_scissor hκ.le hs hr hv U X hX

def gammaMeasuredClosureRVClassLift : GammaGroundMeasuredRVKPlus hc B k →+
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ.le hs hr hv k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredRVPresentation hc B k)
    (gammaMeasuredClosureRVLiftInvariant hκ hs h00 hr hγ hB hv)

@[simp] theorem gammaMeasuredClosureRVClassLift_class (U : GammaGroundMeasuredRVObject hc B k) :
    gammaMeasuredClosureRVClassLift hκ hs h00 hr hγ hB hv (gammaGroundMeasuredRVClass U) =
      gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaGroundMeasuredObjectLift U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaMeasuredClosureRVClassLift_surjective :
    Function.Surjective (gammaMeasuredClosureRVClassLift (hc := hc) (k := k) hκ hs h00 hr hγ hB hv) := by
  apply positiveAdditiveHom_surjective_of_classes
    (gammaGroundMeasuredVFPresentation (hc := hc) (ground := B) hκ.le hs hr hv k)
  intro U
  obtain ⟨W,hW⟩ := gammaMeasuredVFObject_class_preimage hκ hs h00 hr hv U
  exact ⟨gammaGroundMeasuredRVClass W,(gammaMeasuredClosureRVClassLift_class hκ hs h00 hr hγ hB hv W).trans hW.symm⟩

def gammaContextMeasuredDegreeLift (C : GammaGroundContext M)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (k : ℕ) :
    GammaGroundMeasuredRVKPlus hc C.base k →+
      GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k :=
  gammaMeasuredClosureRVClassLift C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv

theorem gammaContextMeasuredDegreeLift_surjective (C : GammaGroundContext M)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (k : ℕ) :
    Function.Surjective (gammaContextMeasuredDegreeLift C hc hv k) :=
  gammaMeasuredClosureRVClassLift_surjective C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv

end DiamondIntegral.Section3
