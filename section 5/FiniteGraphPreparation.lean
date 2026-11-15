import «section 5».FiniteFormulaPreparation
import «section 5».RESBijectionSchemata

/-! One genuine special bijection prepares a finite family of domains and
full relation graphs. Native RES validity is preserved as one whole package. -/
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

theorem prepare_finite_original_base_RV_graphs {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    {ι η : Type} [Finite ι] [Finite η] (a : ι → ℕ) (b c : η → ℕ)
    (D : (i : ι) → GammaDomainFormula B p (a i) (fun _ => .vf))
    (H : (j : η) → GammaRelationFormula B p (b j) (c j) (fun _ => .vf)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      (∀ (i : ι) (x : C), (GammaParameterRecode.prepared T hT).DomainAgreement (D i)
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ (j : η) (x : C), (GammaParameterRecode.prepared T hT).RelationAgreement (H j)
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) := by
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite η
  let CF := vfFieldNamedBase B
  let R := S ∪ CF.real
  have hSR : S ⊆ R := Set.subset_union_left
  let A' := SpecialTransformations.Section5.extendBase A hSR
  have hA' : GammaSetDefinable CF (carrier A') :=
    hA.mono Set.subset_union_left (Set.Subset.refl _)
  let L : GammaFormulaBaseChange B CF :=
    ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hCode : GammaVFRowCode CF p (fun z t =>
      (∀ i : ι, (GammaParameterRecode.identity B p (fun _ => .vf)).DomainAgreement (D i) z t) ∧
      (∀ j : η, (GammaParameterRecode.identity B p (fun _ => .vf)).RelationAgreement (H j) z t)) :=
    ((GammaVFRowCode.finset Finset.univ _
      (fun i _ => gamma_domain_vf_code_in_base L (vfFieldNamedBase_field B) (D i))).mono
        (fun _ _ h i => h i (Finset.mem_univ i))).and
    ((GammaVFRowCode.finset Finset.univ _
      (fun j _ => gamma_relation_vf_code_in_base L (vfFieldNamedBase_field B) (H j))).mono
        (fun _ _ h j => h j (Finset.mem_univ j)))
  obtain ⟨l, C, T, hTC, hC, hrows⟩ := gamma_prepare_vf_row_code (B := CF) hs h00
    (vfFieldNamedBase_small B hκ hsmall) (vfFieldNamedBase_field B)
    Set.subset_union_right A' hA' _ hCode
  have hT : GammaChainDefinable B T.chain :=
    (vfFieldBaseReduction B).chainDefinable T.chain hTC
  exact ⟨R, hSR, (fun _ hc => Or.inr (Or.inl hc)), l, C, T, hT, hC,
    fun i x => gamma_prepared_domain_agreement T hT (D i)
      (fun x y hxy => (hrows x y hxy).1 i) x,
    fun j x => gamma_prepared_relation_agreement T hT (H j)
      (fun x y hxy => (hrows x y hxy).2 j) x⟩

theorem prepare_finite_res_bijection_schemata (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    {ι : Type} [Finite ι] (a b : ι → ℕ)
    (F : (i : ι) → RESSetSchema B p (a i) (fun _ => .vf))
    (G : (i : ι) → RESSetSchema B p (b i) (fun _ => .vf))
    (H : (i : ι) → RESBijectionSchema (F i) (G i)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ (i : ι) (x : C), (H i).Valid hc (rawVFParameter (T.inverseMap x).val) ↔
        ((H i).recode (GammaParameterRecode.prepared T hT)).Valid hc (rawPreparedKey x.val) := by
  let ar : ι ⊕ ι → ℕ := Sum.elim a b
  let dom : (i : ι ⊕ ι) → GammaDomainFormula B p (ar i) (fun _ => .vf) :=
    Sum.rec (fun i => (F i).domain) (fun i => (G i).domain)
  obtain ⟨R, hSR, hBR, l, C, T, hT, hC, hD, hH⟩ :=
    prepare_finite_original_base_RV_graphs hκ hs h00 B hsmall A hA ar a b dom (fun i => (H i).graph)
  refine ⟨R, hSR, hBR, l, C, T, hT, hC, ?_⟩
  intro i x
  exact (H i).recode_valid_iff hc (GammaParameterRecode.prepared T hT) _ _
    (fun j => ((T.inverseMap x).val.1 j).property)
    (fun j => ((flatKey x.val).2 j).property)
    (hD (Sum.inl i) x) (hD (Sum.inr i) x) (hH i x)

end DiamondIntegral.Section5
