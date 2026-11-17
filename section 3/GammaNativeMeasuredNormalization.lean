import «section 3».GammaNativeHighLiftDomain
import «section 3».GammaNativeMeasuredLifts

/-! Every native Gamma form has a genuine full-weight local RV
normalization with the same essential measured VF lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaNativeHighLabelInclusion (U : GammaObjectAt B Set.univ (n+1)) :
    GammaGroundMap (Section5.nativeRVGroundDomain (gammaHighRestrictionAt U))
      (Section5.nativeRVGroundDomain (hc := hc) U) :=
  GammaGroundMap.inclusion (fun _ hx =>
    (Section5.nativeRVGroundDomain_carrier U).ge
      (((Section5.nativeRVGroundDomain_carrier (gammaHighRestrictionAt U)).le hx).1))

def gammaNativeMeasuredNormalization (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundMeasuredRVObject hc B (n+1) :=
  ⟨Section5.nativeRVGroundObject (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U),
    ω.comp (gammaNativeHighLabelInclusion U)⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeMeasuredNormalization_lift_class
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    gammaGroundMeasuredVFClass hκ hs hr hv (gammaNativeMeasuredLift U ω) =
      gammaGroundMeasuredVFClass hκ hs hr hv
        (gammaGroundMeasuredObjectLift (gammaNativeMeasuredNormalization U ω)) := by
  let V := gammaNativeMeasuredLift U ω
  let E := Section5.nativeVFZeroStratum V.domain Finset.univ
  have hE := Section5.nativeVFZeroStratum_subset V.domain Finset.univ
  have hsmall : Section2.vfDimension (V.domain.sdiff E).carrier < ((n+1 : ℕ) : WithBot ℕ) := by
    apply gammaGround_small_complement_of_generic V.domain E hκ hs hr hv (Nat.zero_lt_succ n)
    intro p
    apply (Section5.nativeVFZeroStratum_mem V.domain Finset.univ p.val.val).mpr
    exact ⟨p.val.property,fun i => ⟨fun _ => p.property.ne_zero i,fun _ => Finset.mem_univ _⟩⟩
  have h := gammaMeasuredCofullRestrictionHom hκ hs hr hv V E hE hsmall
  have e := gammaMeasuredHomOfCarrierEq hκ hs hr hv
    (U := V.restrict E hE) (V := gammaGroundMeasuredObjectLift (gammaNativeMeasuredNormalization U ω)) rfl
    (heq_of_eq (gammaDefSet_eq_of_carrierEq (gammaNativeHighLift_carrier U)))
    (fun p q hpq => by
      have he : p.val = q.val := eq_of_heq hpq
      let a : V.domain := ⟨p.val,hE p.property⟩
      let b := gammaGroundObjectLiftLabel (gammaNativeMeasuredNormalization U ω).underlying q
      change (gammaGroundFormValue ω (gammaNativeLiftLabel U a)).val =
        (gammaGroundFormValue ω (gammaNativeHighLabelInclusion U b)).val
      congr 2
      apply Subtype.ext
      exact congrArg Prod.snd he)
  exact (gammaGroundMeasuredVFClass_iso hκ hs hr hv h).trans
    (gammaGroundMeasuredVFClass_iso hκ hs hr hv e)

end DiamondIntegral.Section3
