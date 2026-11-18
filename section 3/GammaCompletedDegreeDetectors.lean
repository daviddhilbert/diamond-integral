import «section 3».GammaMeasuredDegreeKernel

/-! The proved degree kernel gives additive detectors valued in the
original principal semiring quotient, uniformly in all degrees. This
factorization uses only surjectivity and equality of fibres. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3

def additiveFactorOfSurjective {R V W : Type*} [AddMonoid R] [AddMonoid V] [AddMonoid W]
    (L : R →+ V) (q : R →+ W) (hs : Function.Surjective L)
    (hr : ∀ {a b}, L a = L b → q a = q b) : V →+ W where
  toFun v := q (hs v).choose
  map_zero' := (hr ((hs 0).choose_spec.trans L.map_zero.symm)).trans q.map_zero
  map_add' v w := by
    have h := hr ((hs (v+w)).choose_spec.trans
      ((L.map_add (hs v).choose (hs w).choose).trans
        (congrArg₂ (· + ·) (hs v).choose_spec (hs w).choose_spec)).symm)
    exact h.trans (q.map_add _ _)

theorem additiveFactorOfSurjective_apply {R V W : Type*} [AddMonoid R] [AddMonoid V] [AddMonoid W]
    (L : R →+ V) (q : R →+ W) (hs : Function.Surjective L)
    (hr : ∀ {a b}, L a = L b → q a = q b) (a : R) :
    additiveFactorOfSurjective L q hs hr (L a) = q a := hr (hs (L a)).choose_spec

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaCompletedDegreeDetector (k : ℕ) :
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k →+
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).Quotient :=
  additiveFactorOfSurjective (gammaContextMeasuredDegreeLift C hc hv k) (gammaGroundMeasuredRVFixedSpecialHom C hc k)
    (gammaContextMeasuredDegreeLift_surjective C hc hv k) (by
      intro a b h
      have hker : (AddCon.ker (gammaContextMeasuredDegreeLift C hc hv k)) a b := h
      rw [← gammaContextMeasuredDegreeLift_kernel C hc hv k] at hker
      exact hker)

theorem gammaCompletedDegreeDetector_lift (k : ℕ) (a : GammaGroundMeasuredRVKPlus hc C.base k) :
    gammaCompletedDegreeDetector C hc hv k (gammaContextMeasuredDegreeLift C hc hv k a) =
      gammaGroundMeasuredRVFixedSpecialHom C hc k a := by
  unfold gammaCompletedDegreeDetector
  exact additiveFactorOfSurjective_apply (gammaContextMeasuredDegreeLift C hc hv k)
    (gammaGroundMeasuredRVFixedSpecialHom C hc k) (gammaContextMeasuredDegreeLift_surjective C hc hv k)
    (by
      intro x y h
      have hker : (AddCon.ker (gammaContextMeasuredDegreeLift C hc hv k)) x y := h
      rw [← gammaContextMeasuredDegreeLift_kernel C hc hv k] at hker
      exact hker) a

theorem gammaCompletedDegreeDetector_lift_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k) :
    gammaCompletedDegreeDetector C hc hv k
      (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv (gammaGroundMeasuredObjectLift U)) =
      gammaMeasuredPrincipalValue U := by
  have h := gammaMeasuredClosureRVClassLift_class C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv U
  change gammaContextMeasuredDegreeLift C hc hv k (gammaGroundMeasuredRVClass U) = _ at h
  rw [← h,gammaCompletedDegreeDetector_lift]
  change (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk'
    (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U)) = _
  rw [gammaGroundMeasuredRVKPlusToSemiring_class]
  rfl

end DiamondIntegral.Section3
