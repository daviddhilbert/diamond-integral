import «section 2».RawTaggedPolydiscs
import «section 2».TypePolydiscImages

/-! The pointwise complete-type implication used in Corollary 2.30's
compactness argument. No good-disc or multivariable image conclusion is
assumed: both are assembled from the proved coordinate-chain results. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem type_good_tagged_polydisc_code (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {n : ℕ} (d : Fin (n+n) → M) (hd : rawOpenPolydiscProper d)
    (A : Set (Fin n → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : rawOpenPolydisc d ⊆ A) (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (hrv : ∀ x ∈ rawOpenPolydisc d, Set.InjOn iRv {y | (x,y) ∈ F}) :
    d ∈ rawGoodTaggedPolydiscCodes F := by
  obtain ⟨a,δ,he⟩ := rawOpenPolydisc_presentation d hd
  let P := namedPolydisc (fun _ => false) a δ
  change rawOpenPolydisc d = P at he
  have hPA : P ⊆ A := he ▸ hsub
  have hcommon : ∀ p ∈ P, ∀ q ∈ P,
      iRv '' {y | (p,y) ∈ F} = iRv '' {y | (q,y) ∈ F} :=
    type_polydisc_rv_rows_constant h00 B hΓ unary rvbase a δ A hA hPA F hF
  have hrvP : ∀ x ∈ P, Set.InjOn iRv {y | (x,y) ∈ F} := he ▸ hrv
  constructor
  · intro t ht x hx
    obtain ⟨y,u,hu,huy,hyt⟩ := ht
    change ∃ y, (x,y) ∈ F ∧ iRv y = t 0
    have htag : t 0 ∈ iRv '' {y | (u,y) ∈ F} := ⟨y,huy,hyt⟩
    rw [hcommon u (he ▸ hu) x (he ▸ hx)] at htag
    exact htag
  · intro t
    apply rawDiscShapeCodes_of_shape
    intro hne
    obtain ⟨y,x,hx,hxy,hyt⟩ := hne
    have hrow : (Fin.snoc x y : Fin (n+1) → M) ∈
        {z : Fin (n+1) → M | (Fin.init z,z (Fin.last n)) ∈ F} := by
      simpa only [Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last] using hxy
    have hyVF : iVF y := by
      simpa only [Fin.snoc_last,sortEval,iVF] using hF.proper (Fin.snoc x y) hrow (Fin.last n)
    let tag := rv M (⟨y,hyVF⟩ : VF M)
    have htag : tag.val ∈ vfRelationTags P F := ⟨x,he ▸ hx,y,hxy,rfl⟩
    obtain ⟨g,hg⟩ := vfTagBranch_function P F hcommon hrvP tag htag
    have hbranch : ∀ u ∈ P, ∀ v, ((u,v) ∈ F ∧ iRv v = tag.val) ↔ g u = v := by
      intro u hu v
      exact ⟨fun hv => (hg u hu v).mp ⟨hu,hv⟩,fun hv => ((hg u hu v).mpr hv).2⟩
    have hshape := type_polydisc_tagged_branch_image h00 B hΓ unary rvbase image a δ A hA hPA F hF
      tag g hbranch
    have himage : rawTaggedPolydiscImage F (Sum.elim d t) = g '' P := by
      ext v
      constructor
      · rintro ⟨u,hu,huv,hvt⟩
        have hut : (u,v) ∈ F ∧ iRv v = tag.val := ⟨huv,hvt.trans hyt.symm⟩
        exact ⟨u,he ▸ hu,(hbranch u (he ▸ hu) v).mp hut⟩
      · rintro ⟨u,hu,rfl⟩
        have hf := (hbranch u hu (g u)).mpr rfl
        exact ⟨u,he.symm ▸ hu,hf.1,hf.2.trans hyt⟩
    rwa [himage]

end DiamondIntegral.Section2
