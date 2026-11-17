import «section 3».GammaPositiveDegreeReverseKernel
import «section 3».GammaMeasuredZeroKernel
import «section 3».GammaNativeMeasuredElementaryLift
import «section 3».GammaElementaryClosureExistence
import «section 3».GammaGroundCitedMeasuredIntegral

/-! The measured degree kernel is proved in every degree at the exact
Gamma-ground context. Native elementary lift diagrams give the forward
direction; the positive detector and literal zero comparison give the
reverse direction. This constructs the degreewise input record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaContextMeasuredDegreeLift_elementary (n : ℕ) :
    GammaNativeElementaryInvariant C.uncountable.le C.saturated C.model00 C.small_real
      (gammaContextMeasuredDegreeLift C hc hv (n+1)) := by
  intro U ω i hAd
  obtain ⟨D⟩ := gammaElementaryDiagram_exists_original C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) (U := U.toGamma.toGammaRVObject) (Set.subset_univ _) hAd
  let V := gammaElementaryAt C.uncountable.le C.saturated C.model00 C.small_real U i hAd
  let η := ω.comp (gammaNativeElementaryOldLabel C.uncountable.le C.saturated C.model00 C.small_real U i hAd)
  have hU := gammaMeasuredClosureRVClassLift_class C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv (gammaNativeMeasuredNormalization U ω)
  have hV := gammaMeasuredClosureRVClassLift_class C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv (gammaNativeMeasuredNormalization V η)
  exact hU.trans ((gammaNativeMeasuredNormalization_lift_class C.uncountable.le C.saturated C.small_real hv U ω).symm.trans
    ((gammaGroundMeasuredVFClass_iso C.uncountable.le C.saturated C.small_real hv
      (gammaNativeMeasuredElementaryHom C.uncountable.le C.saturated C.model00 C.small_real hv U i hAd D ω)).trans
      ((gammaNativeMeasuredNormalization_lift_class C.uncountable.le C.saturated C.small_real hv V η).trans hV.symm)))

theorem gammaContextMeasuredDegreeLift_kernel (k : ℕ) :
    gammaGroundMeasuredRVFixedSpecialCongruence C hc k = AddCon.ker (gammaContextMeasuredDegreeLift C hc hv k) := by
  cases k with
  | zero => exact gammaContextMeasuredDegreeLift_zero_kernel C hc hv
  | succ n =>
    ext a b
    change (_ = _) ↔ (_ = _)
    constructor
    · intro h
      obtain ⟨U,rfl⟩ := gammaGroundMeasuredRVClass_surjective a
      obtain ⟨V,rfl⟩ := gammaGroundMeasuredRVClass_surjective b
      change (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U)) =
        (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass V)) at h
      rw [gammaGroundMeasuredRVKPlusToSemiring_class,gammaGroundMeasuredRVKPlusToSemiring_class] at h
      exact gammaPrincipal_preserves_fixed_degree_additive C.uncountable.le C.saturated C.model00 C.small_real
        (gammaContextMeasuredDegreeLift C hc hv (n+1)) (gammaContextMeasuredDegreeLift_elementary C hc hv n) h
    · exact gammaContextMeasuredDegreeLift_positive_reverse_kernel C hc hv n

def completedGammaGroundDegreeMeasuredLiftInput : YinGammaGroundDegreeMeasuredLiftInput C hc hv where
  lift := gammaContextMeasuredDegreeLift C hc hv
  lift_class U := gammaMeasuredClosureRVClassLift_class C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv U
  surjective := gammaContextMeasuredDegreeLift_surjective C hc hv
  kernel := gammaContextMeasuredDegreeLift_kernel C hc hv

end DiamondIntegral.Section3
