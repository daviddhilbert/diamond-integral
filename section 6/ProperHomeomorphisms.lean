import «section 6».RestrictedFibres

/-! Lemma 6.8, including the restriction to every proper invariant source
subset and its actual definable image. Graph domains are clopen by proper
covariance; continuity means continuity on all these actual fibers. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure ProperCovariantHomeomorphism (f : Map A B) : Prop where
  bijective : Function.Bijective f
  covariant : ProperCovariant f
  continuous : ContinuousOnGraphFibres f
  inverseCovariant : ProperCovariant (f.inverse bijective)
  inverseContinuous : ContinuousOnGraphFibres (f.inverse bijective)

theorem properHomeomorphism_of_properCovariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hcov : ProperCovariant f) (hf : Function.Bijective f)
    (hcont : ContinuousOnGraphFibres f) : ProperCovariantHomeomorphism f :=
  ⟨hf,hcov,hcont,hcov.inverse_properCovariant h00 hc linear hκ hs hv hsmall hΓ hf hcont,
    hcov.inverse_continuous h00 hc hκ hs hv hf hcont⟩

theorem ProperCovariantHomeomorphism.restrict
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} (h : ProperCovariantHomeomorphism f)
    (C : DefSet (rawMixedSpace (M := M) n r) S) (hCA : C.carrier ⊆ A.carrier)
    (hC : ProperInvariant S C.carrier) : ProperCovariantHomeomorphism (f.restrict hCA).toImage := by
  have hCG := h.covariant.restrict h00 hc linear hκ hs hv hsmall hΓ h.bijective h.continuous hCA hC
  apply properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    (f.restrict hCA).toImage hCG.toImage (restrict_toImage_bijective f h.bijective.injective hCA)
  exact continuousOnGraphFibres_restrict h.continuous hCA

/-- Lemma 6.8. Source/target invariance, inverse covariance and continuity,
and every proper invariant restriction are proved over the original base. -/
theorem lemma_6_8
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hcov : ProperCovariant f) (hf : Function.Surjective f) :
    ProperInvariant S A.carrier ∧ ProperInvariant S B.carrier ∧
      (Function.Injective f → ContinuousOnGraphFibres f →
        ProperCovariantHomeomorphism f ∧
        ∀ (C : DefSet (rawMixedSpace (M := M) n r) S) (hCA : C.carrier ⊆ A.carrier),
          ProperInvariant S C.carrier → ProperCovariantHomeomorphism (f.restrict hCA).toImage) := by
  refine ⟨hcov.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ,
    hcov.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hf,fun hinj hcont => ?_⟩
  have h := properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ f hcov ⟨hinj,hf⟩ hcont
  exact ⟨h,fun C hCA hC => h.restrict h00 hc linear hκ hs hv hsmall hΓ C hCA hC⟩

end DiamondIntegral.Section6
