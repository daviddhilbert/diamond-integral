import «section 5».NativeVFIntegral

/-! The Section 3 positive lifting/kernel presentation over an actual
parameter base. Contextual data give this presentation directly; naming
it separately lets a fibre retain precisely F together with its displayed
parameters before any definable-closure presentation adapter is applied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

structure OriginalBaseUnmeasuredLiftInput (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  lift : GammaGroundRVPositiveSemiring hc B →+* GammaGroundVFPositiveSemiring hc B
  lift_class : ∀ {k : ℕ} (U : GammaGroundRVObject hc B k),
    lift (gammaGroundRVSemiringClass U) = gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)
  surjective : Function.Surjective lift
  kernel : gammaGroundRVSpecialCongruence hc B = RingCon.ker lift

def originalBaseLiftInputOfContext {C : GammaGroundContext M} (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    OriginalBaseUnmeasuredLiftInput hc C.base := ⟨H.lift,H.lift_class,H.surjective,H.kernel⟩

def originalBasePositiveIntegral (H : OriginalBaseUnmeasuredLiftInput hc B) :
    GammaGroundVFPositiveSemiring hc B ≃+* (gammaGroundRVSpecialCongruence hc B).Quotient :=
  semiringIntegralFromKernel H.lift H.surjective _ H.kernel

theorem originalBasePositiveIntegral_lift_class (H : OriginalBaseUnmeasuredLiftInput hc B)
    {k : ℕ} (U : GammaGroundRVObject hc B k) :
    originalBasePositiveIntegral H (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)) =
      (gammaGroundRVSpecialCongruence hc B).mk' (gammaGroundRVSemiringClass U) := by
  exact (semiringIntegralFromKernel_characterization H.lift H.surjective _ H.kernel _ _).mpr (H.lift_class U).symm

def originalBaseVFIntegralPositive (H : OriginalBaseUnmeasuredLiftInput hc B) :
    GammaGroundVFPositiveSemiring hc B →+* RVOrdinaryPNormalization.Ring B :=
  (nativeRVPositiveNormalized (hc := hc) (B := B)).comp (originalBasePositiveIntegral H).toRingHom

def originalBaseVFIntegral (H : OriginalBaseUnmeasuredLiftInput hc B) :
    GammaGroundVFGrothendieckRing hc B →+* RVOrdinaryPNormalization.Ring B :=
  liftRingHom (originalBaseVFIntegralPositive H)

theorem originalBaseVFIntegral_lift_class (H : OriginalBaseUnmeasuredLiftInput hc B)
    {k : ℕ} (U : GammaGroundRVObject hc B k) :
    originalBaseVFIntegral H (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
      RVOrdinaryPNormalization.quotient B (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) := by
  rw [originalBaseVFIntegral,liftRingHom_apply_of]
  change nativeRVPositiveNormalized (originalBasePositiveIntegral H
    (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) = _
  rw [originalBasePositiveIntegral_lift_class]
  change (gammaGroundRVSpecialCongruence hc B).lift
    ((nativeRVChartNormalized hc B).comp ofRingHom) _
    ((gammaGroundRVSpecialCongruence hc B).mk' (gammaGroundRVSemiringClass U)) = _
  rw [RingCon.lift_mk']
  change RVOrdinaryPNormalization.quotient B
    (Section3RVChartRingMaps.ordinary hc B (ordinaryClass U)) = _
  rw [Section3RVChartRingMaps.ordinary_class]

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def originalBaseVFBoundedValue (H : OriginalBaseUnmeasuredLiftInput hc B) :
    GammaGroundVFGrothendieckRing hc B →+* RESDimensionFreeReduction.Ring B :=
  (RVT001OrdinaryNormalization.bounded h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)).comp (originalBaseVFIntegral H)

theorem originalBaseVFBoundedValue_lift_class (H : OriginalBaseUnmeasuredLiftInput hc B)
    {k : ℕ} (U : GammaGroundRVObject hc B k) :
    originalBaseVFBoundedValue h00 linear hκ hs hr hγ hΓ H
      (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
      nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ .bounded (ordinaryClass U) := by
  change RVT001OrdinaryNormalization.bounded h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)
    (originalBaseVFIntegral H _) = _
  rw [originalBaseVFIntegral_lift_class,nativeGroundRVEvaluation_class]
  rfl

theorem originalBaseVFIntegral_ofContext {C : GammaGroundContext M}
    (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    originalBaseVFIntegral (originalBaseLiftInputOfContext H) = nativeVFChartIntegral H := rfl

theorem originalBaseVFBoundedValue_ofContext {C : GammaGroundContext M}
    (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    originalBaseVFBoundedValue C.model00 linear C.uncountable.le C.saturated
      C.small_real C.small_gamma C.nontrivial_definable_gamma (originalBaseLiftInputOfContext H) =
        nativeVFBoundedValue linear H := rfl

end DiamondIntegral.Section5
