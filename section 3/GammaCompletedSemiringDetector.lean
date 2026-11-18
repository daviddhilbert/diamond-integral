import «section 3».GammaCompletedDegreeDetectors
import «section 3».GammaMeasuredVFProductArrows
import «section 3».GammaMeasuredObjectArrowSurjectivity
import «section 3».GammaMeasuredSemiringLift

/-! The degreewise detectors assemble to a semiring detector. Actual
measured arrows to lifts and their Cartesian products prove its product
law, including zero-degree factors. No global kernel is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaCompletedObjectValue {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :=
  gammaCompletedDegreeDetector C hc hv k (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv U)

theorem gammaCompletedObjectValue_iso {k : ℕ} {U V : GammaGroundMeasuredVFData hc C.base k}
    (f : GammaGroundMeasuredVFHom C.uncountable.le C.saturated C.small_real hv U V) :
    gammaCompletedObjectValue C hc hv U = gammaCompletedObjectValue C hc hv V :=
  congrArg (gammaCompletedDegreeDetector C hc hv k)
    (gammaGroundMeasuredVFClass_iso C.uncountable.le C.saturated C.small_real hv f)

theorem gammaCompletedObjectValue_empty (k : ℕ) :
    gammaCompletedObjectValue C hc hv (GammaGroundMeasuredVFData.empty hc C.base k) = 0 := by
  unfold gammaCompletedObjectValue
  rw [gammaGroundMeasuredVFClass_empty,map_zero]

theorem gammaCompletedObjectValue_lift {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k) :
    gammaCompletedObjectValue C hc hv (gammaGroundMeasuredObjectLift U) = gammaMeasuredPrincipalValue U :=
  gammaCompletedDegreeDetector_lift_class C hc hv U

theorem gammaCompletedObjectValue_unit :
    gammaCompletedObjectValue C hc hv (GammaGroundMeasuredVFData.unit hc C.base) = 1 := by
  have h := gammaCompletedObjectValue_iso C hc hv (k := 0) gammaMeasuredUnitLiftHom
  apply h.symm.trans
  rw [gammaCompletedObjectValue_lift]
  unfold gammaMeasuredPrincipalValue
  rw [gammaGroundMeasuredRVSemiringClass_unit,map_one]

theorem gammaCompletedObjectValue_product {k l : ℕ}
    (U : GammaGroundMeasuredVFData hc C.base k) (V : GammaGroundMeasuredVFData hc C.base l) :
    gammaCompletedObjectValue C hc hv (U.product V) =
      gammaCompletedObjectValue C hc hv U * gammaCompletedObjectValue C hc hv V := by
  obtain ⟨W,⟨hW⟩⟩ := gammaMeasuredVFObject_arrow_preimage C.uncountable C.saturated C.model00 C.small_real hv U
  obtain ⟨Z,⟨hZ⟩⟩ := gammaMeasuredVFObject_arrow_preimage C.uncountable C.saturated C.model00 C.small_real hv V
  have hU := (gammaCompletedObjectValue_iso C hc hv hW).trans (gammaCompletedObjectValue_lift C hc hv W)
  have hV := (gammaCompletedObjectValue_iso C hc hv hZ).trans (gammaCompletedObjectValue_lift C hc hv Z)
  have hP := gammaCompletedObjectValue_iso C hc hv
    (gammaMeasuredVFProductHom C.uncountable.le C.saturated C.small_real hv hW hZ)
  have hL := gammaCompletedObjectValue_iso C hc hv
    (gammaMeasuredLiftProductHom C.uncountable.le C.saturated C.small_real hv W Z)
  apply hP.trans
  apply hL.symm.trans
  rw [gammaCompletedObjectValue_lift,hU,hV]
  unfold gammaMeasuredPrincipalValue
  rw [gammaGroundMeasuredRVSemiringClass_product,map_mul]

theorem gammaCompletedObjectValue_scissor {k : ℕ} {A B D E : GammaGroundMeasuredVFData hc C.base k}
    (h : gammaGroundMeasuredVFScissor A B D E) :
    gammaCompletedObjectValue C hc hv A + gammaCompletedObjectValue C hc hv B =
      gammaCompletedObjectValue C hc hv D + gammaCompletedObjectValue C hc hv E := by
  let χ := gammaCompletedDegreeDetector C hc hv k
  have hC := congrArg χ (positiveClass_scissor
    (gammaGroundMeasuredVFPresentation (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k) h)
  exact (χ.map_add _ _).symm.trans (hC.trans (χ.map_add _ _))

def gammaCompletedVFInvariant : PositiveGrothendieck.Invariant (gammaGroundMeasuredVFSemiringPresentation C hc hv)
    (R := (gammaGroundMeasuredRVSpecialCongruence hc C.base).Quotient) where
  toFun A := gammaCompletedObjectValue C hc hv A.2
  iso := by
    rintro A B ⟨k,U,V,⟨e⟩,rfl,rfl⟩
    exact gammaCompletedObjectValue_iso C hc hv e
  empty := gammaCompletedObjectValue_empty C hc hv 0
  unit := gammaCompletedObjectValue_unit C hc hv
  product A B := gammaCompletedObjectValue_product C hc hv A.2 B.2
  scissor := by
    rintro A B D E (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · exact gammaCompletedObjectValue_scissor C hc hv h
    · simp only [gammaCompletedObjectValue_empty,add_zero]

def gammaCompletedSemiringDetector : GammaGroundMeasuredVFPositiveSemiring C hc hv →+*
    (gammaGroundMeasuredRVSpecialCongruence hc C.base).Quotient :=
  PositiveGrothendieck.lift (gammaGroundMeasuredVFSemiringPresentation C hc hv) (gammaCompletedVFInvariant C hc hv)

theorem gammaCompletedSemiringDetector_class {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :
    gammaCompletedSemiringDetector C hc hv (gammaGroundMeasuredVFSemiringClass C hc hv U) =
      gammaCompletedObjectValue C hc hv U :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredVFSemiringPresentation C hc hv)
    (gammaCompletedVFInvariant C hc hv) ⟨k,U⟩

theorem gammaCompletedSemiringDetector_lift :
    (gammaCompletedSemiringDetector C hc hv).comp (gammaContextMeasuredSemiringLift C hc hv) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' := by
  apply positivePresentationHom_ext (gammaGroundMeasuredRVSemiringPresentation hc C.base)
    (F := (gammaCompletedSemiringDetector C hc hv).comp (gammaContextMeasuredSemiringLift C hc hv))
    (G := (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk')
  rintro ⟨k,U⟩
  change gammaCompletedSemiringDetector C hc hv (gammaContextMeasuredSemiringLift C hc hv
    (gammaGroundMeasuredRVSemiringClass U)) = gammaMeasuredPrincipalValue U
  rw [gammaContextMeasuredSemiringLift_class,gammaCompletedSemiringDetector_class,gammaCompletedObjectValue_lift]

end DiamondIntegral.Section3
