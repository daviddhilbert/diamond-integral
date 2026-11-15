import IntegrationSection6.GammaPreparedRowAgreements
import IntegrationSection6.GammaWitnessVFCodesInBase
import IntegrationSection6.GammaFieldBaseReduction
import IntegrationSection6.GammaSpecialBaseReduction
import IntegrationSection6.GammaVFCodePreparation

/-! A single genuine special bijection prepares an arbitrary finite family
of full RV predicates. The temporary generated coefficient field is internal;
both the chain and every descended predicate retain the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem prepare_finite_original_base_RV_predicates {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    {ι : Type} [Finite ι] (a : ι → ℕ)
    (D : (i : ι) → GammaDomainFormula B p (a i) (fun _ => .vf)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ (i : ι) (x : C), (GammaParameterRecode.prepared T hT).DomainAgreement (D i)
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  letI := Fintype.ofFinite ι
  let CF := vfFieldNamedBase B
  let R := S ∪ CF.real
  have hSR : S ⊆ R := Set.subset_union_left
  let A' := SpecialTransformations.Section5.extendBase A hSR
  have hA' : GammaSetDefinable CF (carrier A') :=
    hA.mono Set.subset_union_left (Set.Subset.refl _)
  let L : GammaFormulaBaseChange B CF :=
    ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hCode : GammaVFRowCode CF p (fun z t => ∀ i : ι,
      (GammaParameterRecode.identity B p (fun _ => .vf)).DomainAgreement (D i) z t) :=
    (GammaVFRowCode.finset Finset.univ _
      (fun i _ => gamma_domain_vf_code_in_base L (vfFieldNamedBase_field B) (D i))).mono
        (fun _ _ h i => h i (Finset.mem_univ i))
  obtain ⟨l, C, T, hTC, hC, hrows⟩ := gamma_prepare_vf_row_code (B := CF) hs h00
    (vfFieldNamedBase_small B hκ hsmall) (vfFieldNamedBase_field B)
    Set.subset_union_right A' hA' _ hCode
  have hT : GammaChainDefinable B T.chain :=
    (vfFieldBaseReduction B).chainDefinable T.chain hTC
  exact ⟨R, hSR, (fun _ hc => Or.inr (Or.inl hc)), l, C, T, hT, hC,
    fun i x => gamma_prepared_domain_agreement T hT (D i)
      (fun x y hxy => hrows x y hxy i) x⟩

end DiamondIntegral.Section5
