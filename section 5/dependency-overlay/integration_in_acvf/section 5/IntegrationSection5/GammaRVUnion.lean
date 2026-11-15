import IntegrationSection5.GammaRVIsomorphism
import Section4.RVUnionCoproduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b : ℕ}

abbrev normalizedRVUnionSet {r : ℕ} (A B : PresentedSet (rawRVSpace (M := M) r) S) :=
  @SpecialTransformations.DefinableGeometry.DefSet.union LRV M (@CanonicalStructure.normalize M sM) _ S A B
abbrev normalizedRVUnionMap {A B : PresentedSet (rawRVSpace (M := M) a) S}
    {C : PresentedSet (rawRVSpace (M := M) b) S} (f : Map A C) (g : Map B C) :=
  @SpecialTransformations.DefinableGeometry.Map.union LRV M (@CanonicalStructure.normalize M sM) _ _ S A B C f g
local notation "unionSet" => normalizedRVUnionSet
local notation "unionMap" => normalizedRVUnionMap

theorem normalizedRVUnionMap_left {A B : PresentedSet (rawRVSpace (M := M) a) S}
    {C : PresentedSet (rawRVSpace (M := M) b) S} (f : Map A C) (g : Map B C) (p : A) :
    normalizedRVUnionMap f g ⟨p.val,Or.inl p.property⟩ = f p := by
  simp [normalizedRVUnionMap,SpecialTransformations.DefinableGeometry.Map.union,p.property]
theorem normalizedRVUnionMap_right {A B : PresentedSet (rawRVSpace (M := M) a) S}
    {C : PresentedSet (rawRVSpace (M := M) b) S} (f : Map A C) (g : Map B C)
    (hd : Disjoint (carrier A) (carrier B)) (p : B) :
    normalizedRVUnionMap f g ⟨p.val,Or.inr p.property⟩ = g p := by
  have hn : p.val ∉ carrier A := fun h => Set.disjoint_left.mp hd h p.property
  simp [normalizedRVUnionMap,SpecialTransformations.DefinableGeometry.Map.union,hn]

theorem gamma_rvMap_union {A B : PresentedSet (rawRVSpace (M := M) a) S}
    {C : PresentedSet (rawRVSpace (M := M) b) S} (f : Map A C) (g : Map B C)
    (hd : Disjoint (carrier A) (carrier B))
    (hf : GammaGraphDefinable G (rvMapGraph f)) (hg : GammaGraphDefinable G (rvMapGraph g)) :
    GammaGraphDefinable G (rvMapGraph (unionMap f g)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).union_graph hf hg)
  intro p q
  constructor
  · rintro (⟨u,hu,hq⟩ | ⟨u,hu,hq⟩)
    · refine ⟨⟨u.val,Or.inl u.property⟩,hu,?_⟩
      rw [normalizedRVUnionMap_left f g]
      exact hq
    · refine ⟨⟨u.val,Or.inr u.property⟩,hu,?_⟩
      rw [normalizedRVUnionMap_right f g hd]
      exact hq
  · rintro ⟨u,hu,hq⟩
    rcases u.property with hl | hr
    · left
      refine ⟨⟨u.val,hl⟩,hu,?_⟩
      have he : u = ⟨u.val,Or.inl hl⟩ := rfl
      exact (congrArg (fun z : C => z.val) (normalizedRVUnionMap_left f g ⟨u.val,hl⟩)).symm.trans hq
    · right
      refine ⟨⟨u.val,hr⟩,hu,?_⟩
      have he : u = ⟨u.val,Or.inr hr⟩ := rfl
      exact (congrArg (fun z : C => z.val) (normalizedRVUnionMap_right f g hd ⟨u.val,hr⟩)).symm.trans hq

open SpecialTransformations.Section4
variable {k : ℕ}
local notation "restrictRV" => @SpecialTransformations.Section4.RVObject.restrict M (@CanonicalStructure.normalize M sM) S k
local notation "unionSubsetRV" => @SpecialTransformations.Section4.rvUnionSubset M (@CanonicalStructure.normalize M sM) S k
local notation "unionInlRV" => @SpecialTransformations.Section4.rvUnionInl M (@CanonicalStructure.normalize M sM) S k
local notation "unionInrRV" => @SpecialTransformations.Section4.rvUnionInr M (@CanonicalStructure.normalize M sM) S k
local notation "unionDescRV" => @SpecialTransformations.Section4.rvUnionDesc M (@CanonicalStructure.normalize M sM) S k
abbrev normalizedRVHomMap {U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k}
    (f : @SpecialTransformations.Section4.RVHom M (@CanonicalStructure.normalize M sM) S k U V) :=
  @SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S k U V f
local notation "mapRV" => normalizedRVHomMap
local notation "extRV" => @SpecialTransformations.Section4.RVHom.ext M (@CanonicalStructure.normalize M sM) S k _ _ _ _
local notation "homRV" => @SpecialTransformations.Section4.RVHom M (@CanonicalStructure.normalize M sM) S k

def gammaRVUnionIso
    (U V : @RVObject M (@CanonicalStructure.normalize M sM) S k)
    (A0 A1 : PresentedSet (SpecialTransformations.Section5.rawRVSpace (M := M) (rvObjectArity U)) S)
    (B0 B1 : PresentedSet (SpecialTransformations.Section5.rawRVSpace (M := M) (rvObjectArity V)) S)
    (hA0 : carrier A0 ⊆ carrier (rvObjectDomain U)) (hA1 : carrier A1 ⊆ carrier (rvObjectDomain U))
    (hB0 : carrier B0 ⊆ carrier (rvObjectDomain V)) (hB1 : carrier B1 ⊆ carrier (rvObjectDomain V))
    (hdA : Disjoint (carrier A0) (carrier A1)) (hdB : Disjoint (carrier B0) (carrier B1))
    (e0 : GammaRVIso G (restrictRV U A0 hA0) (restrictRV V B0 hB0))
    (e1 : GammaRVIso G (restrictRV U A1 hA1) (restrictRV V B1 hB1)) :
    GammaRVIso G (restrictRV U (unionSet A0 A1) (unionSubsetRV U A0 A1 hA0 hA1))
      (restrictRV V (unionSet B0 B1) (unionSubsetRV V B0 B1 hB0 hB1)) := by
  let f0 := e0.iso.hom ≫ unionInlRV V B0 B1 hB0 hB1
  let f1 := e1.iso.hom ≫ unionInrRV V B0 B1 hB0 hB1
  let g0 := e0.iso.inv ≫ unionInlRV U A0 A1 hA0 hA1
  let g1 := e1.iso.inv ≫ unionInrRV U A0 A1 hA0 hA1
  let F := unionDescRV U A0 A1 hA0 hA1 f0 f1
  let G0 := unionDescRV V B0 B1 hB0 hB1 g0 g1
  have h0 (p : A0) : rvIsoInvMap e0.iso (rvIsoHomMap e0.iso p) = p := by
    exact congrArg (fun h : homRV (restrictRV U A0 hA0) (restrictRV U A0 hA0) => mapRV h p) e0.iso.hom_inv_id
  have h1 (p : A1) : rvIsoInvMap e1.iso (rvIsoHomMap e1.iso p) = p := by
    exact congrArg (fun h : homRV (restrictRV U A1 hA1) (restrictRV U A1 hA1) => mapRV h p) e1.iso.hom_inv_id
  have h0' (p : B0) : rvIsoHomMap e0.iso (rvIsoInvMap e0.iso p) = p := by
    exact congrArg (fun h : homRV (restrictRV V B0 hB0) (restrictRV V B0 hB0) => mapRV h p) e0.iso.inv_hom_id
  have h1' (p : B1) : rvIsoHomMap e1.iso (rvIsoInvMap e1.iso p) = p := by
    exact congrArg (fun h : homRV (restrictRV V B1 hB1) (restrictRV V B1 hB1) => mapRV h p) e1.iso.inv_hom_id
  refine ⟨⟨F,G0,?_,?_⟩,?_,?_⟩
  · apply @SpecialTransformations.Section4.rvUnion_hom_ext M (@CanonicalStructure.normalize M sM) S k U A0 A1 hA0 hA1
    · have hF := @SpecialTransformations.Section4.rvUnion_inl_desc M (@CanonicalStructure.normalize M sM) S k U A0 A1 hA0 hA1 _ f0 f1
      have hG := @SpecialTransformations.Section4.rvUnion_inl_desc M (@CanonicalStructure.normalize M sM) S k V B0 B1 hB0 hB1 _ g0 g1
      rw [← Category.assoc,hF]
      change (e0.iso.hom ≫ unionInlRV V B0 B1 hB0 hB1) ≫ G0 = _
      rw [Category.assoc,hG]
      change e0.iso.hom ≫ (e0.iso.inv ≫ unionInlRV U A0 A1 hA0 hA1) = _
      rw [← Category.assoc,e0.iso.hom_inv_id,Category.id_comp,Category.comp_id]
    · have hF := @SpecialTransformations.Section4.rvUnion_inr_desc M (@CanonicalStructure.normalize M sM) S k U A0 A1 hA0 hA1 hdA _ f0 f1
      have hG := @SpecialTransformations.Section4.rvUnion_inr_desc M (@CanonicalStructure.normalize M sM) S k V B0 B1 hB0 hB1 hdB _ g0 g1
      rw [← Category.assoc,hF]
      change (e1.iso.hom ≫ unionInrRV V B0 B1 hB0 hB1) ≫ G0 = _
      rw [Category.assoc,hG]
      change e1.iso.hom ≫ (e1.iso.inv ≫ unionInrRV U A0 A1 hA0 hA1) = _
      rw [← Category.assoc,e1.iso.hom_inv_id,Category.id_comp,Category.comp_id]
  · apply @SpecialTransformations.Section4.rvUnion_hom_ext M (@CanonicalStructure.normalize M sM) S k V B0 B1 hB0 hB1
    · have hF := @SpecialTransformations.Section4.rvUnion_inl_desc M (@CanonicalStructure.normalize M sM) S k V B0 B1 hB0 hB1 _ g0 g1
      have hG := @SpecialTransformations.Section4.rvUnion_inl_desc M (@CanonicalStructure.normalize M sM) S k U A0 A1 hA0 hA1 _ f0 f1
      rw [← Category.assoc,hF]
      change (e0.iso.inv ≫ unionInlRV U A0 A1 hA0 hA1) ≫ F = _
      rw [Category.assoc,hG]
      change e0.iso.inv ≫ (e0.iso.hom ≫ unionInlRV V B0 B1 hB0 hB1) = _
      rw [← Category.assoc,e0.iso.inv_hom_id,Category.id_comp,Category.comp_id]
    · have hF := @SpecialTransformations.Section4.rvUnion_inr_desc M (@CanonicalStructure.normalize M sM) S k V B0 B1 hB0 hB1 hdB _ g0 g1
      have hG := @SpecialTransformations.Section4.rvUnion_inr_desc M (@CanonicalStructure.normalize M sM) S k U A0 A1 hA0 hA1 hdA _ f0 f1
      rw [← Category.assoc,hF]
      change (e1.iso.inv ≫ unionInrRV U A0 A1 hA0 hA1) ≫ F = _
      rw [Category.assoc,hG]
      change e1.iso.inv ≫ (e1.iso.hom ≫ unionInrRV V B0 B1 hB0 hB1) = _
      rw [← Category.assoc,e1.iso.inv_hom_id,Category.id_comp,Category.comp_id]
  · exact @gamma_rvMap_union M sM hM G S _ _ A0 A1 _ (mapRV f0) (mapRV f1) hdA e0.hom_graph e1.hom_graph
  · exact @gamma_rvMap_union M sM hM G S _ _ B0 B1 _ (mapRV g0) (mapRV g1) hdB e0.inv_graph e1.inv_graph

end IntegrationInACVF.Section5
