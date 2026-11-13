import «section 3».RVGammaUnaryOrthogonality
import «section 3».RVFiniteValueGammaClosure
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Finite Gamma rows over a unary finite-value-support RV set have finite
union. This includes finite correspondences without a choice of outputs. -/
theorem rv_finite_value_gamma_correspondence_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (R : Values.Gamma (M := M) → M → Prop) (hsort : ∀ γ t, R γ t → iRV t)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite)
    (hrows : ∀ t ∈ D, {γ | R γ t}.Finite) :
    {γ | ∃ t ∈ D, R γ t}.Finite := by
  have hC := gammaRVBase_finite_value_columns hκ hs h00 B hsmall R hsort hR D hD hvalues
  have hcf (c : Set (Values.Gamma (M := M))) (hc : c ∈ relationColumn R '' D) : c.Finite := by
    obtain ⟨t,ht,rfl⟩ := hc
    exact hrows t ht
  apply (hC.biUnion hcf).subset
  rintro γ ⟨t,ht,hγ⟩
  exact Set.mem_iUnion.mpr ⟨relationColumn R t,Set.mem_iUnion.mpr ⟨⟨t,ht,rfl⟩,hγ⟩⟩

theorem nativeGamma_named_of_finite_scalar (B : GammaParameters.Base (M := M))
    (Y : Set (Values.Gamma (M := M))) (hY : Y.Finite)
    (hdef : FullGammaSyntax.Scalar (integrationGammaBase B) Y)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Y) : GammaDefinableClosureAtBase B γ := by
  have he : (hY.toFinset : Set (Values.Gamma (M := M))) = Y := hY.coe_toFinset
  have hdefF : FullGammaSyntax.Scalar (integrationGammaBase B) (hY.toFinset : Set (Values.Gamma (M := M))) :=
    he.symm ▸ hdef
  exact nativeGamma_named_of_full_scalar B γ
    (FullGammaPoint.finset_element_definable hY.toFinset hdefF γ (hY.mem_toFinset.mpr hγ))

theorem rv_finite_value_gamma_correspondence_named {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (R : Values.Gamma (M := M) → M → Prop) (hsort : ∀ γ t, R γ t → iRV t)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite)
    (hrows : ∀ t ∈ D, {γ | R γ t}.Finite) (t : M) (ht : t ∈ D)
    (γ : Values.Gamma (M := M)) (hγ : R γ t) : GammaDefinableClosureAtBase B γ := by
  let Y : Set (Values.Gamma (M := M)) := {γ | ∃ t ∈ D, R γ t}
  have hY := rv_finite_value_gamma_correspondence_finite hκ hs h00 B hsmall R hsort hR D hD hvalues hrows
  have hdef := gammaRVColumnValues_definable B R hR {z | z 0 ∈ D} hD
  have he : gammaRVColumnValues R {z | z 0 ∈ D} = Y := by
    ext γ
    exact ⟨fun ⟨z,hz,hr⟩ => ⟨z 0,hz,hr⟩,fun ⟨x,hx,hr⟩ => ⟨![x],hx,hr⟩⟩
  exact nativeGamma_named_of_finite_scalar B Y hY (he ▸ hdef) γ ⟨t,ht,hγ⟩
end DiamondIntegral.Section3
