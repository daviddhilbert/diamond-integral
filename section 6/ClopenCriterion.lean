import «section 6».LeastRadiusGraph
import Section3.GammaParameterBridge

/-! Lemma 6.5. The least interior-radius graph, bounded partition theorem,
and definable supremum supply an invariant radius over the original base.
No representative parameters survive in the conclusion. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem gamma_real_codes_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (A : Set (Gamma M)) :
    GammaParameters.GammaDefinableOverBase (⟨S,∅⟩ : ParameterBase M) A ↔
      S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback A} := by
  rw [GammaParameters.GammaDefinableOverBase,GammaParameters.at_base_empty_iff,
    definableAt_iff_normalized_raw,normalize_eq_of_isCanonical hc]
  exact ⟨And.left,fun h => ⟨h,fun _ hx => hx.1⟩⟩

theorem vfGammaGraph_image_codes (A : Set (Fin n → VF M))
    (p : (Fin n → VF M) → Gamma M) :
    (fun z => z ∘ (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)) '' vfGammaGraph A p =
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (p '' A)} := by
  ext z
  constructor
  · rintro ⟨w,⟨ht,a,ha,_,he⟩,hw⟩
    have h0 : w (.inr 0) = z 0 := congrFun hw 0
    change z 0 ∈ Values.gammaPullback (p '' A)
    rw [← h0]
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr ⟨a,ha,he.symm⟩
  · intro hz
    let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    obtain ⟨a,ha,he⟩ := (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz
    refine ⟨Sum.elim (vfValues a) z,⟨ht,a,ha,rfl,he.symm⟩,?_⟩
    rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem clopen_has_named_invariant_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hclopen : IsClopen A)
    (hbounded : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i)) :
    ∃ δ : Gamma M,
      S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      AlphaInvariant (fun _ => δ) A := by
  by_cases hne : A.Nonempty
  · obtain ⟨p,hp,hgraph⟩ := exists_least_interior_radius_graph h00 hc hv A hA hclopen.isOpen
    have hvalues : GammaParameters.GammaDefinableOverBase (⟨S,∅⟩ : ParameterBase M) (p '' A) := by
      apply (gamma_real_codes_iff hc S _).mpr
      rw [← vfGammaGraph_image_codes A p]
      exact hgraph.image_comp Sum.inr
    obtain ⟨δ,hδ,hδdef⟩ := gamma_definable_supremum h00 _ _ hvalues (hne.image p)
      (lemma_2_53_vf h00 hc hκ hs hv A hA hclopen.isClosed hbounded p
        (least_interior_radii_partition p hp) hgraph).2
    exact ⟨δ,(gamma_real_codes_iff hc S _).mp hδdef,
      alphaInvariant_of_bounded_interior_radii p (fun a ha => (hp a ha).1.2) δ
        (fun a ha => hδ.1 ⟨a,ha,rfl⟩)⟩
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1,?_,?_⟩
    · apply (gamma_real_codes_iff hc S _).mp
      exact GammaParameters.real_definableAtBase (⟨S,∅⟩ : ParameterBase M) .rv _
        (GammaSyntax.one_definable S)
    · rw [he]
      exact fun _ _ _ => Iff.rfl

theorem properInvariant_fibre_definable {S : Set M} (A : Set (Mixed M n m))
    (hA : (rawMixedSpace (M := M) n m).Definable S A) (t : Fin m → RVInfinity M) :
    (S ∪ Set.range (rvValues t)).Definable LRV (vfValues '' vfFibre A t) := by
  let T := S ∪ Set.range (rvValues t)
  let P := rawMixedSpace (M := M) n m
  let f (z : Fin n → M) : Fin n ⊕ Fin m → M := Sum.elim z (rvValues t)
  have hf : T.DefinableMap LRV f := by
    rintro (i | i)
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
  have hAraw : S.Definable LRV (P.preimage A) := hA
  convert (hAraw.mono Set.subset_union_left).preimage_map hf using 1
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨mixedValues_mem_domain (a,t),?_⟩
    change P.decode ⟨mixedValues (a,t),_⟩ ∈ A
    change (a,t) ∈ A at ha
    simpa only [P,decode_mixedValues] using ha
  · rintro ⟨hz,ha⟩
    let q := P.decode ⟨f z,hz⟩
    have he : mixedValues q = f z := mixedValues_decode (M := M) ⟨f z,hz⟩
    have ht : q.2 = t := funext (fun i => Subtype.ext (congrFun he (.inr i)))
    exact ⟨q.1,by change (q.1,t) ∈ A; rw [← ht]; exact ha,
      funext (fun i => congrFun he (.inl i))⟩

/-- Lemma 6.5 with global bounds, all finite arities and original-base
radius names. Mixed clopenness is fiberwise in the existing RV labels. -/
theorem lemma_6_5
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Mixed M n m))
    (hA : (rawMixedSpace (M := M) n m).Definable S A)
    (hVF : VFBounded A) (hRV : RVSupportDoublyBounded A) :
    ProperInvariant S A ↔ ∀ t : Fin m → RVInfinity M, IsClopen (vfFibre A t) := by
  constructor
  · intro h t
    exact h.clopen_fibres hv t
  · intro hclopen
    refine ⟨hA,hVF,hRV,fun t => ?_⟩
    have hb : ∃ γ : Gamma M, ∀ x ∈ vfFibre A t, ∀ i, γ.val ≤ vfValue (x i) := by
      obtain ⟨γ,hγ⟩ := hVF
      exact ⟨γ,fun x hx i => hγ (x,t) hx i⟩
    obtain ⟨δ,hδdef,hδ⟩ := clopen_has_named_invariant_radius h00 hc hκ hs hv
      (vfFibre A t) (properInvariant_fibre_definable A hA t) (hclopen t) hb
    exact ⟨fun _ => δ,fun _ => hδdef,hδ⟩

end DiamondIntegral.Section6
