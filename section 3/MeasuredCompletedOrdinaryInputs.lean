import «section 3».MeasuredRealGroundVFInputs
import «section 3».MeasuredRealGroundLiftCompatibility
import «section 3».GammaCompletedMeasuredInputs
import «section 3».CitedMeasuredIntegral

/-! The exact ordinary-base measured kernels follow from the proved
Gamma-ground kernels through inverse literal category comparisons.
Both ordinary input records are constructed without new kernel inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
open MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def completedMeasuredSemiringLift : MeasuredRVPositiveSemiring hc (C.base : Set M) →+* MeasuredVFPositiveSemiring C hc :=
  (vfSemiringToReal C hc B hv).comp
    ((gammaContextMeasuredSemiringLift (measuredRealGroundContext C B) hc hv).comp (rvSemiringFromReal C hc B))

theorem completedMeasuredSemiringLift_class {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    completedMeasuredSemiringLift C hc B hv (measuredRVSemiringClass hc U) =
      measuredVFObjectSemiringClass C hc (measuredObjectLift hc C k U) := by
  change vfSemiringToReal C hc B hv (gammaContextMeasuredSemiringLift (measuredRealGroundContext C B) hc hv
    (rvSemiringFromReal C hc B (measuredRVSemiringClass hc U))) = _
  rw [rvSemiringFromReal_class,gammaContextMeasuredSemiringLift_class]
  have h := gammaGroundMeasuredVFSemiringClass_iso (measuredRealGroundContext C B) hc hv (liftFromRealHom C hc B hv U)
  rw [← h,vfSemiringToReal_class,vfToReal_fromReal]
  rfl

theorem completedMeasuredSemiringLift_surjective : Function.Surjective (completedMeasuredSemiringLift C hc B hv) := by
  intro a
  obtain ⟨b,hb⟩ := gammaContextMeasuredSemiringLift_surjective (measuredRealGroundContext C B) hc hv (vfSemiringFromReal C hc B hv a)
  refine ⟨rvSemiringToReal C hc B b,?_⟩
  change vfSemiringToReal C hc B hv (gammaContextMeasuredSemiringLift (measuredRealGroundContext C B) hc hv
    (rvSemiringFromReal C hc B (rvSemiringToReal C hc B b))) = a
  rw [rvSemiringFromReal_toReal,hb,vfSemiringToReal_fromReal]

theorem completedMeasuredSemiringLift_kernel :
    measuredRVSpecialCongruence hc (C.base : Set M) = RingCon.ker (completedMeasuredSemiringLift C hc B hv) := by
  ext a b
  change measuredRVSpecialCongruence hc (C.base : Set M) a b ↔
    vfSemiringToReal C hc B hv (gammaContextMeasuredSemiringLift (measuredRealGroundContext C B) hc hv (rvSemiringFromReal C hc B a)) =
    vfSemiringToReal C hc B hv (gammaContextMeasuredSemiringLift (measuredRealGroundContext C B) hc hv (rvSemiringFromReal C hc B b))
  rw [← rvSpecial_fromReal_iff C hc B a b,gammaContextMeasuredSemiringLift_kernel]
  change (_ = _) ↔ (_ = _)
  constructor
  · exact congrArg (vfSemiringToReal C hc B hv)
  · intro h
    simpa only [vfSemiringFromReal_toReal] using congrArg (vfSemiringFromReal C hc B hv) h

def completedMeasuredLiftInput : YinMeasuredLiftInput C hc B where
  lift := completedMeasuredSemiringLift C hc B hv
  lift_class := completedMeasuredSemiringLift_class C hc B hv
  surjective := completedMeasuredSemiringLift_surjective C hc B hv
  kernel := completedMeasuredSemiringLift_kernel C hc B hv

def completedMeasuredDegreeLift (k : ℕ) : MeasuredRVKPlus hc (C.base : Set M) k →+ MeasuredVFKPlus C hc k :=
  (vfDegreeToReal C hc B hv k).comp
    ((gammaContextMeasuredDegreeLift (measuredRealGroundContext C B) hc hv k).comp (rvDegreeFromReal C hc B k))

theorem completedMeasuredDegreeLift_class {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    completedMeasuredDegreeLift C hc B hv k (measuredRVClass hc U) =
      positiveClass (measuredVFPresentation C hc k) (measuredObjectLift hc C k U) := by
  change vfDegreeToReal C hc B hv k (gammaContextMeasuredDegreeLift (measuredRealGroundContext C B) hc hv k
    (rvDegreeFromReal C hc B k (measuredRVClass hc U))) = _
  rw [rvDegreeFromReal_class]
  have hL : gammaContextMeasuredDegreeLift (measuredRealGroundContext C B) hc hv k
      (gammaGroundMeasuredRVClass (rvFromReal C hc B U)) =
      gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small hv
        (gammaGroundMeasuredObjectLift (rvFromReal C hc B U)) :=
    (completedGammaGroundDegreeMeasuredLiftInput (measuredRealGroundContext C B) hc hv).lift_class _
  rw [hL]
  have h := gammaGroundMeasuredVFClass_iso C.uncountable.le C.saturated C.small hv (liftFromRealHom C hc B hv U)
  rw [← h,vfDegreeToReal_class,vfToReal_fromReal,MeasuredVFData.to_ofObject]

theorem completedMeasuredDegreeLift_surjective (k : ℕ) : Function.Surjective (completedMeasuredDegreeLift C hc B hv k) := by
  intro a
  obtain ⟨b,hb⟩ := gammaContextMeasuredDegreeLift_surjective (measuredRealGroundContext C B) hc hv k (vfDegreeFromReal C hc B hv k a)
  refine ⟨rvDegreeToReal C hc B k b,?_⟩
  change vfDegreeToReal C hc B hv k (gammaContextMeasuredDegreeLift (measuredRealGroundContext C B) hc hv k
    (rvDegreeFromReal C hc B k (rvDegreeToReal C hc B k b))) = a
  rw [rvDegreeFromReal_toReal,hb,vfDegreeToReal_fromReal]

theorem completedMeasuredDegreeLift_kernel (k : ℕ) :
    measuredRVFixedSpecialCongruence C hc k = AddCon.ker (completedMeasuredDegreeLift C hc B hv k) := by
  have hRel (a b : MeasuredRVKPlus hc (C.base : Set M) k) :
      measuredRVFixedSpecialCongruence C hc k a b ↔
        gammaGroundMeasuredRVFixedSpecialCongruence (measuredRealGroundContext C B) hc k
          (rvDegreeFromReal C hc B k a) (rvDegreeFromReal C hc B k b) := by
    change (_ = _) ↔ (_ = _)
    change (measuredRVSpecialCongruence hc (C.base : Set M)).mk' (measuredRVKPlusToSemiring hc a) =
      (measuredRVSpecialCongruence hc (C.base : Set M)).mk' (measuredRVKPlusToSemiring hc b) ↔
      (gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk'
        (gammaGroundMeasuredRVKPlusToSemiring (rvDegreeFromReal C hc B k a)) =
      (gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk'
        (gammaGroundMeasuredRVKPlusToSemiring (rvDegreeFromReal C hc B k b))
    rw [← rvSemiringFromReal_fixed,← rvSemiringFromReal_fixed]
    exact (measuredRVSpecialCongruence hc (C.base : Set M)).eq.trans
      ((rvSpecial_fromReal_iff C hc B _ _).symm.trans
        (gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base).eq.symm)
  ext a b
  rw [hRel a b,gammaContextMeasuredDegreeLift_kernel]
  change (_ = _) ↔ vfDegreeToReal C hc B hv k
    (gammaContextMeasuredDegreeLift (measuredRealGroundContext C B) hc hv k (rvDegreeFromReal C hc B k a)) =
    vfDegreeToReal C hc B hv k
    (gammaContextMeasuredDegreeLift (measuredRealGroundContext C B) hc hv k (rvDegreeFromReal C hc B k b))
  constructor
  · exact congrArg (vfDegreeToReal C hc B hv k)
  · intro h
    simpa only [vfDegreeFromReal_toReal] using congrArg (vfDegreeFromReal C hc B hv k) h

def completedDegreeMeasuredLiftInput : YinDegreeMeasuredLiftInput C hc B where
  lift := completedMeasuredDegreeLift C hc B hv
  lift_class := completedMeasuredDegreeLift_class C hc B hv
  surjective := completedMeasuredDegreeLift_surjective C hc B hv
  kernel := completedMeasuredDegreeLift_kernel C hc B hv

end DiamondIntegral.Section3
