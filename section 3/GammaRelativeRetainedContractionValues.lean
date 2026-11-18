import «section 3».GammaStandardRelativeMeasuredValues
import «section 3».GammaNativeRetainedFullMaps

/-! The standard relatively unary comparison applies directly to the
actual native Jacobian-one maps used by the RV-density constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRelative_retained_contraction_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n a b : ℕ}
    {H : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    (hH : GammaSetDefinable B (carrier H)) (hA : GammaSetDefinable B (carrier A))
    (hfinH : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (η : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) b)))
    (f : SpecialTransformations.Section5.Map H A) (hf : Function.Bijective f)
    (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hForm : ∀ p : H, η ⟨(f p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩)
    (hJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    {σ : Equiv.Perm (Fin (n+1))} (hi : UnaryRelative f (σ 0))
    (T : StandardContraction H σ) (W : StandardContraction A σ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hH hfinH T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfinA W hW η) := by
  let F := gammaNativeRetainedFullMap C hBC hv (Nat.zero_lt_succ n) hH hA hfinH hfinA ω η f hf hfΓ hJ hForm
  apply gammaStandard_relative_measured_values C hBC hv hg δ hδ hδ1 hH hA hfinH hfinA ω η F _ T W hT hW
  intro p j hj
  rw [gammaNativeRetainedFullMap_apply]
  exact hi ⟨p.val,p.property⟩ j hj

end DiamondIntegral.Section3
