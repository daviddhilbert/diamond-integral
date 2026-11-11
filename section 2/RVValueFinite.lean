import «section 2».RVValueFamilies
import «section 2».RVGammaCuts
import «section 2».GammaFamilyRestrictions
import Section3.SmallFiniteParameters

/-! The actual finite output value sets over each input value. Temporary
real names used to prove finiteness do not enter the uniform family graph. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rvValueFamily_nonempty (D : Set M) (f : M → Gamma M) (γ : Gamma M)
    (hγ : γ ∈ rvValueDomain D) : (rvValueFamily D f γ).Nonempty := by
  obtain ⟨t,ht,hNZ,he⟩ := hγ
  exact ⟨f t,t,⟨ht,hNZ,he⟩,rfl⟩

theorem rvValueFamily_finite (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S D : Set M) (hsmall : Cardinal.mk S < κ) (hD : DefinableAt S .rv D)
    (f : M → Gamma M)
    (hf : S.Definable LRV (rawGammaFamilyGraph {x : Fin 1 → M | x 0 ∈ D} (fun x => {f (x 0)})))
    (γ : Gamma M) : (rvValueFamily D f γ).Finite := by
  classical
  let tγ := GammaParameters.raw (GammaParameters.representative γ)
  let T := insert tγ S
  let E := D ∩ Values.gammaPullback {γ}
  have hTsmall : Cardinal.mk T < κ := small_insert hκ S hsmall tγ
  have hE : DefinableAt T .rv E :=
    (hD.mono (Set.subset_insert tγ S)).inter (GammaParameters.value_fibre_domain_definable S γ)
  have hEγ : ∀ t : RVInfinity M, t.val ∈ E → Values.vrv t = γ.val := by
    intro t ht
    obtain ⟨hRV,hNZ,hmem⟩ := ht.2
    have he : Values.gammaOf ⟨t.val,hRV⟩ hNZ = γ := hmem
    exact congrArg Subtype.val he
  have hF := rawGammaFamilyGraph_restrict_definable T
    {x : Fin 1 → M | x 0 ∈ D} {x : Fin 1 → M | x 0 ∈ E}
    (fun _ hx => hx.1) hE.raw_definable (fun x => {f (x 0)}) (hf.mono (Set.subset_insert tγ S))
  have hfinite := rv_gamma_image_finite_on_value_fibre hc hs T E hTsmall hE γ hEγ f hF
  have hEq : E = {t | t ∈ D ∧ GammaParameters.NonzeroRV t ∧ GammaParameters.codeValue t = γ} := by
    ext t
    constructor
    · rintro ⟨htD,htγ⟩
      have hNZ : GammaParameters.NonzeroRV t := ⟨htγ.1,htγ.2.1⟩
      exact ⟨htD,hNZ,(GammaParameters.gammaPullback_mem_codeValue_iff {γ} t hNZ).mp htγ⟩
    · rintro ⟨htD,hNZ,he⟩
      exact ⟨htD,(GammaParameters.gammaPullback_mem_codeValue_iff {γ} t hNZ).mpr he⟩
  change (f '' {t | t ∈ D ∧ GammaParameters.NonzeroRV t ∧ GammaParameters.codeValue t = γ}).Finite
  rwa [hEq] at hfinite

end DiamondIntegral.Section2
