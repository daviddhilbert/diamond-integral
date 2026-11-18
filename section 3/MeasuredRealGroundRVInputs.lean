import «section 3».MeasuredRealGroundRVSemirings
import «section 3».GammaPrincipalGeometricReflection
import «section 3».MeasuredRVGenerators

/-! Degree inclusions and the exact homogeneous principal relation
commute with the ordinary/redundant-Gamma RV comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)

def realRVDegreeCoefficient (k : ℕ) : MeasuredRVPositiveSemiring hc (C.base : Set M) →+
    MeasuredRVKPlus hc (C.base : Set M) k where
  toFun a := (measuredRVPresentationToDirectSum a) k
  map_zero' := congrArg (fun s : MeasuredRVDirectSum hc (C.base : Set M) => s k)
    (measuredRVPresentationToDirectSum (M := M) (hc := hc) (S := (C.base : Set M))).map_zero
  map_add' a b := congrArg (fun s : MeasuredRVDirectSum hc (C.base : Set M) => s k)
    ((measuredRVPresentationToDirectSum (M := M) (hc := hc) (S := (C.base : Set M))).map_add a b)

theorem realRVDegreeCoefficient_class {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    realRVDegreeCoefficient C hc k (measuredRVSemiringClass hc U) = measuredRVClass hc U := by
  change (measuredRVPresentationToDirectSum (measuredRVSemiringClass hc U)) k = _
  rw [measuredRVPresentationToDirectSum_class]
  exact DirectSum.of_eq_same k _

def rvDegreeFromReal (k : ℕ) : MeasuredRVKPlus hc (C.base : Set M) k →+
    GammaGroundMeasuredRVKPlus hc (measuredRealGroundContext C B).base k :=
  (gammaMeasuredDegreeCoefficient k).comp ((rvSemiringFromReal C hc B).toAddMonoidHom.comp (measuredRVKPlusToSemiring hc))

def rvDegreeToReal (k : ℕ) : GammaGroundMeasuredRVKPlus hc (measuredRealGroundContext C B).base k →+
    MeasuredRVKPlus hc (C.base : Set M) k :=
  (realRVDegreeCoefficient C hc k).comp ((rvSemiringToReal C hc B).toAddMonoidHom.comp gammaGroundMeasuredRVKPlusToSemiring)

theorem rvDegreeFromReal_class {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    rvDegreeFromReal C hc B k (measuredRVClass hc U) = gammaGroundMeasuredRVClass (rvFromReal C hc B U) := by
  change gammaMeasuredDegreeCoefficient k (rvSemiringFromReal C hc B (measuredRVKPlusToSemiring hc (measuredRVClass hc U))) = _
  rw [measuredRVKPlusToSemiring_class,rvSemiringFromReal_class,gammaMeasuredDegreeCoefficient_class]

theorem rvDegreeToReal_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k) :
    rvDegreeToReal C hc B k (gammaGroundMeasuredRVClass U) = measuredRVClass hc (rvToReal C hc B U) := by
  change realRVDegreeCoefficient C hc k (rvSemiringToReal C hc B (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U))) = _
  rw [gammaGroundMeasuredRVKPlusToSemiring_class,rvSemiringToReal_class,realRVDegreeCoefficient_class]

theorem rvDegreeToReal_fromReal (k : ℕ) (a : MeasuredRVKPlus hc (C.base : Set M) k) :
    rvDegreeToReal C hc B k (rvDegreeFromReal C hc B k a) = a := by
  obtain ⟨U,rfl⟩ := measuredRVClass_surjective hc a
  rw [rvDegreeFromReal_class,rvDegreeToReal_class]
  exact measuredRVClass_iso hc (asIso (rvRealRoundTrip C hc B U))

theorem rvDegreeFromReal_toReal (k : ℕ) (a : GammaGroundMeasuredRVKPlus hc (measuredRealGroundContext C B).base k) :
    rvDegreeFromReal C hc B k (rvDegreeToReal C hc B k a) = a := by
  obtain ⟨U,rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  rw [rvDegreeToReal_class,rvDegreeFromReal_class]
  exact gammaGroundMeasuredRVClass_iso (asIso (rvGroundRoundTrip C hc B U))

theorem rvSemiringFromReal_fixed (k : ℕ) (a : MeasuredRVKPlus hc (C.base : Set M) k) :
    rvSemiringFromReal C hc B (measuredRVKPlusToSemiring hc a) =
      gammaGroundMeasuredRVKPlusToSemiring (rvDegreeFromReal C hc B k a) := by
  obtain ⟨U,rfl⟩ := measuredRVClass_surjective hc a
  rw [measuredRVKPlusToSemiring_class,rvSemiringFromReal_class,rvDegreeFromReal_class,gammaGroundMeasuredRVKPlusToSemiring_class]

theorem rvFromReal_principal_pair (positive : Bool) :
    rvSemiringFromReal C hc B (measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc
      (if positive then rvPositiveObject hc (C.base : Set M) else rvOneObject (C.base : Set M)))) =
    gammaGroundMeasuredRVSemiringClass (if positive then gammaGroundMeasuredRVPositive hc (measuredRealGroundContext C B).base
      else gammaGroundMeasuredRVOne hc (measuredRealGroundContext C B).base) := by
  cases positive <;> rw [rvSemiringFromReal_class] <;>
    exact gammaGroundMeasuredRVSemiringClass_iso (asIso (show GammaGroundMeasuredRVHom _ _ from
      ⟨GammaGroundBijection.id _,fun _ => rfl⟩))

theorem rvToReal_principal_pair (positive : Bool) :
    rvSemiringToReal C hc B (gammaGroundMeasuredRVSemiringClass
      (if positive then gammaGroundMeasuredRVPositive hc (measuredRealGroundContext C B).base
        else gammaGroundMeasuredRVOne hc (measuredRealGroundContext C B).base)) =
    measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc
      (if positive then rvPositiveObject hc (C.base : Set M) else rvOneObject (C.base : Set M))) := by
  cases positive <;> rw [rvSemiringToReal_class] <;>
    exact measuredRVSemiringClass_iso hc (asIso (show MeasuredRVHom _ _ from
      ⟨DefinableBijection.id _,fun _ => rfl⟩))

theorem rvSpecial_fromReal {a b : MeasuredRVPositiveSemiring hc (C.base : Set M)}
    (h : measuredRVSpecialCongruence hc (C.base : Set M) a b) :
    gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base
      (rvSemiringFromReal C hc B a) (rvSemiringFromReal C hc B b) := by
  let q := (gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk'
  have hle : measuredRVSpecialCongruence hc (C.base : Set M) ≤ RingCon.ker (q.comp (rvSemiringFromReal C hc B)) := by
    apply RingCon.ringConGen_le.mpr
    rintro x y ⟨rfl,rfl⟩
    change q (rvSemiringFromReal C hc B _) = q (rvSemiringFromReal C hc B _)
    rw [show rvSemiringFromReal C hc B (measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvOneObject (C.base : Set M)))) = _ from rvFromReal_principal_pair C hc B false,
      show rvSemiringFromReal C hc B (measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvPositiveObject hc (C.base : Set M)))) = _ from rvFromReal_principal_pair C hc B true]
    exact (gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base).eq.mpr
      (RingConGen.Rel.of _ _ ⟨rfl,rfl⟩)
  exact (gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base).eq.mp (hle h)

theorem rvSpecial_toReal {a b : GammaGroundMeasuredRVPositiveSemiring hc (measuredRealGroundContext C B).base}
    (h : gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base a b) :
    measuredRVSpecialCongruence hc (C.base : Set M) (rvSemiringToReal C hc B a) (rvSemiringToReal C hc B b) := by
  let q := (measuredRVSpecialCongruence hc (C.base : Set M)).mk'
  have hle : gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base ≤
      RingCon.ker (q.comp (rvSemiringToReal C hc B)) := by
    apply RingCon.ringConGen_le.mpr
    rintro x y ⟨rfl,rfl⟩
    change q (rvSemiringToReal C hc B _) = q (rvSemiringToReal C hc B _)
    rw [show rvSemiringToReal C hc B (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVOne hc (measuredRealGroundContext C B).base)) = _ from rvToReal_principal_pair C hc B false,
      show rvSemiringToReal C hc B (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVPositive hc (measuredRealGroundContext C B).base)) = _ from rvToReal_principal_pair C hc B true]
    exact (measuredRVSpecialCongruence hc (C.base : Set M)).eq.mpr (RingConGen.Rel.of _ _ ⟨rfl,rfl⟩)
  exact (measuredRVSpecialCongruence hc (C.base : Set M)).eq.mp (hle h)

theorem rvSpecial_fromReal_iff (a b : MeasuredRVPositiveSemiring hc (C.base : Set M)) :
    gammaGroundMeasuredRVSpecialCongruence hc (measuredRealGroundContext C B).base
      (rvSemiringFromReal C hc B a) (rvSemiringFromReal C hc B b) ↔ measuredRVSpecialCongruence hc (C.base : Set M) a b := by
  constructor
  · intro h
    simpa only [rvSemiringToReal_fromReal] using rvSpecial_toReal C hc B h
  · exact rvSpecial_fromReal C hc B

end DiamondIntegral.Section3.MeasuredRealGround
