import «section 3».GammaSelectedLiftCarriers
import «section 3».GammaMixedRetainedDensityNormalization
import Integration7.GammaSelectedRVVFTailPartialPrograms

/-! Selected native lifts and their existing VF-tail realizations carry
the same arbitrary retained Gamma form. The comparison is the actual
identity on every VF and RV coordinate, with all zero strata retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {a k : ℕ}
variable (C : DefSet (M := M) S 0 a) (ρ : Fin k → Fin a)
variable (P : GammaFiniteGraphPresentation B a k
  {r | (Fin.elim0,r) ∈ carrier C} (fun r y => (Fin.elim0,r) ∈ carrier C ∧ r ∘ ρ = y))
variable (R : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (hR : ∀ q : C, q.val.2 ∈ R.carrier)

def gammaSelectedNativeLabels :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) R :=
  GammaGroundMap.inclusion (fun r hr => hR
    ⟨(Fin.elim0,r),P.domain_eq.le ((Section5.nativeRVGroundDomain_carrier _).le hr)⟩)

def gammaSelectedNativeForm (η : GammaGroundVolumeForm hc B R) :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :=
  η.comp (gammaSelectedNativeLabels C ρ P R hR)

def gammaSelectedTailDomain (hC : GammaSetDefinable B (carrier C)) :=
  Section5.nativeGammaPointDomain (hc := hc) (carrier (nativeProgramSelectedRVVFTailLift (n := 0) (d := k) hc C ρ))
    (gamma_native_program_selected_rv_vf_tail_lift hc C ρ hC)

include hR in
theorem gammaSelectedTailLabels (hC : GammaSetDefinable B (carrier C))
    (q : gammaSelectedTailDomain (hc := hc) C ρ hC) : q.val.2 ∈ R.carrier := by
  have hOld := (native_program_selected_zero_tail_carrier hc C ρ q.val).mp q.property
  exact hR ⟨(Fin.elim0,q.val.2),hOld.1⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaSelectedLiftFullMeasuredBridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hC : GammaSetDefinable B (carrier C)) (η : GammaGroundVolumeForm hc B R) :
    let Y := gammaSelectedTailDomain (hc := hc) C ρ hC
    ∃ hfin : ∀ x, {r | (x,r) ∈ Y.carrier}.Finite,
    ∃ F : GammaFullMeasuredBijection
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaSelectedNativeForm C ρ P R hR η))
      (⟨a,Y,hfin,gammaMixedRetainedForm Y R (gammaSelectedTailLabels C ρ R hR hC) η⟩ :
        GammaGroundMeasuredVFData hc B k),
      ∀ p, (F.map.map p).val = p.val := by
  intro Y
  let U := gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaSelectedNativeForm C ρ P R hR η)
  have hfin : ∀ x, {r | (x,r) ∈ Y.carrier}.Finite := by
    intro x
    apply (U.finite x).subset
    intro r hr
    exact (gammaSelectedLift_carrier C ρ P).ge hr
  let V : GammaGroundMeasuredVFData hc B k :=
    ⟨a,Y,hfin,gammaMixedRetainedForm Y R (gammaSelectedTailLabels C ρ R hR hC) η⟩
  let e : GammaGroundBijection U.domain V.domain := GammaGroundBijection.ofCarrierEq (gammaSelectedLift_carrier C ρ P)
  let F : GammaFullMeasuredBijection U V := gammaFullMeasuredFixedVF hκ hs hr hv e (fun _ => rfl) (by
    intro p
    rfl)
  exact ⟨hfin,F,fun _ => rfl⟩

end DiamondIntegral.Section3
