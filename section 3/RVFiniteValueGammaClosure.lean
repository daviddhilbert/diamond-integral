import «section 3».RVFiniteValueGammaImages
import «section 3».IntegrationGammaParameters
import IntegrationSection3ACVF.FullGammaPoint
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

theorem gammaRVFunction_range_definable (B : GammaParameters.Base (M := M))
    (D : Set M) (f : D → Values.Gamma (M := M))
    (hf : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ ∃ d : D, d.val = z 1 ∧ f d = codeValue (z 0)}) :
    FullGammaSyntax.Scalar (integrationGammaBase B) (Set.range f) := by
  have hr := FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable hf)
    (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have hp := FullBaseAtomicity.OverBase.exists_block hr
  change FullBaseAtomicity.OverBase (integrationGammaBase B)
    {a : Fin 1 → M | a 0 ∈ Values.gammaPullback (Set.range f)}
  convert hp using 1
  ext a
  change (a 0 ∈ Values.gammaPullback (Set.range f)) ↔ _
  rw [GammaSyntax.mem_gammaPullback_iff]
  change (NonzeroRV (a 0) ∧ ∃ d, f d = codeValue (a 0)) ↔
    ∃ z : Fin 1 → M, NonzeroRV (a 0) ∧ ∃ d : D, d.val = z 0 ∧ f d = codeValue (a 0)
  constructor
  · rintro ⟨hn,d,hd⟩
    exact ⟨![d.val],hn,d,rfl,hd⟩
  · rintro ⟨z,hn,d,_,hd⟩
    exact ⟨hn,d,hd⟩

theorem nativeGamma_named_of_full_scalar (B : GammaParameters.Base (M := M))
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar (integrationGammaBase B) {γ}) :
    GammaParameters.GammaDefinableClosureAtBase B γ := by
  apply (integrationGammaDefinable_iff ?_).mpr hγ
  intro z hz i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact hz.choose

/-- A unary finite-value-support RV function cannot define a new Gamma
value: every value of the function is already definable over the old base. -/
theorem rv_finite_value_support_gamma_value_named {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite)
    (f : D → Values.Gamma (M := M))
    (hf : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ ∃ d : D, d.val = z 1 ∧ f d = codeValue (z 0)}) (d : D) :
    GammaParameters.GammaDefinableClosureAtBase B (f d) := by
  have hfin := rv_finite_value_support_gamma_image_finite hκ hs h00 B hsmall D hD hvalues f hf
  have hdef := gammaRVFunction_range_definable B D f hf
  have he : (hfin.toFinset : Set (Values.Gamma (M := M))) = Set.range f := hfin.coe_toFinset
  have hdefF : FullGammaSyntax.Scalar (integrationGammaBase B) (hfin.toFinset : Set (Values.Gamma (M := M))) :=
    he.symm ▸ hdef
  apply nativeGamma_named_of_full_scalar B (f d)
  exact FullGammaPoint.finset_element_definable hfin.toFinset hdefF (f d)
    (hfin.mem_toFinset.mpr (Set.mem_range_self d))
end DiamondIntegral.Section3
