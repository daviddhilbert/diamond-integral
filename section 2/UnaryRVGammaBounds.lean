import «section 2».RVValueFinite
import «section 2».GammaAbsoluteValues
import «section 2».GammaFamilyFibres
import «section 2».CitedGammaLinearity

/-! The unary RV-to-Gamma case in the author's proof of 2.41. The
finite output set over each input value has a definable supremum of its
absolute values. The unary Gamma bound then controls the original map. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem unary_rv_gamma_image_doubly_bounded
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S D : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hD : DefinableAt S .rv D) (hNZ : ∀ t ∈ D, GammaParameters.NonzeroRV t)
    (f : M → Gamma M)
    (hf : S.Definable LRV (rawGammaFamilyGraph {x : Fin 1 → M | x 0 ∈ D} (fun x => {f (x 0)})))
    (hbounded : ∃ β : Gamma M, ∀ t ∈ D,
      β⁻¹ ≤ GammaParameters.codeValue t ∧ GammaParameters.codeValue t ≤ β) :
    ∃ γ : Gamma M, ∀ t ∈ D, γ⁻¹ ≤ f t ∧ f t ≤ γ := by
  classical
  let V := rvValueDomain D
  let P (γ : Gamma M) := gammaAbs '' rvValueFamily D f γ
  have hV := rvValueDomain_codes_definable S D hD.raw_definable
  have hP := rawGammaFamilyGraph_abs_definable hc S _ _ (rvValueFamily_graph_definable S D f hf)
  have hex (γ : Gamma M) (hγ : γ ∈ V) : ∃ c : Gamma M, IsLUB (P γ) c := by
    obtain ⟨v,hvNZ,hvγ⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
    let a : Fin 1 → M := fun _ => v
    have ha : a ∈ gammaDomainCodes V := ⟨hvNZ,hvγ.symm ▸ hγ⟩
    have hne : (P γ).Nonempty := (rvValueFamily_nonempty D f γ hγ).image gammaAbs
    have hfinite : (P γ).Finite := (rvValueFamily_finite hc hκ hs S D hsmall hD f hf γ).image gammaAbs
    have hne' : (P (GammaParameters.codeValue (a 0))).Nonempty := by
      change (P (GammaParameters.codeValue v)).Nonempty
      rwa [hvγ]
    have hb' : BddAbove (P (GammaParameters.codeValue (a 0))) := by
      change BddAbove (P (GammaParameters.codeValue v))
      rw [hvγ]
      exact hfinite.bddAbove
    have h := rawGammaFamilyGraph_exists_lub hc h00 S (gammaDomainCodes V)
      (fun x => P (GammaParameters.codeValue (x 0))) hP a ha hne' hb'
    change ∃ c, IsLUB (P (GammaParameters.codeValue v)) c at h
    rwa [hvγ] at h
  obtain ⟨g,hg,hLUB⟩ := uniform_gamma_domain_supremum hc S V P hV hP hex
  have hVbounded : ∃ β : Gamma M, ∀ γ ∈ V, β⁻¹ ≤ γ ∧ γ ≤ β := by
    obtain ⟨β,hβ⟩ := hbounded
    refine ⟨β,?_⟩
    rintro γ ⟨t,ht,hNZt,he⟩
    rw [← he]
    exact hβ t ht
  obtain ⟨γ,hγ⟩ := gamma_definable_image_doubly_bounded h00 linear S hΓ V g hg hVbounded
  refine ⟨γ,fun t ht => ?_⟩
  have htV : GammaParameters.codeValue t ∈ V := ⟨t,ht,hNZ t ht,rfl⟩
  have htP : gammaAbs (f t) ∈ P (GammaParameters.codeValue t) :=
    ⟨f t,⟨t,⟨ht,hNZ t ht,rfl⟩,rfl⟩,rfl⟩
  have hsup := (hLUB _ htV).1 htP
  have hgb := (hγ (g (GammaParameters.codeValue t)) ⟨GammaParameters.codeValue t,htV,rfl⟩).2
  exact (gammaAbs_le_iff (f t) γ).mp (hsup.trans hgb)

end DiamondIntegral.Section2
