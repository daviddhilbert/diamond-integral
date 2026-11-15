import IntegrationSection5.FiniteRVComparison
import IntegrationSection5.UnaryRVCategory
import IntegrationSection5.GammaCellStandardExistence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
open CategoryTheory
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem lemma_5_3_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hfDef : GammaGraphDefinable G (pointMapGraph f))
    (hFinite : FiniteMixedRVFibres (carrier A)) :
    ∃ hVA : Map.FiniteFibres (rvObjectVolume (pullbackObject A)),
    ∃ hVB : Map.FiniteFibres (rvObjectVolume (pullbackObject B)),
    ∃ e : GammaRVFiniteIso G (⟨pullbackObject A,hVA⟩ : FiniteRVObject S 1)
      (⟨pullbackObject B,hVB⟩ : FiniteRVObject S 1),
      ∀ a : A, finiteRVHomMap e.iso.hom (Map.toImage (rawKeyMap A) a) = Map.toImage (rawKeyMap B) (f a) := by
  let F : GammaIso G (carrier A) (carrier B) := ⟨Equiv.ofBijective f hf,hfDef⟩
  have hFiniteB := GammaIso.finite_mixed_rv_fibres hκ hs hsmall F hFinite
  let hVA := pullbackObject_finiteVolume A hA hFinite
  let hVB := pullbackObject_finiteVolume B hB hFiniteB
  obtain ⟨e,hSquare,hG,hGi⟩ := lemma_5_3 hκ hs hsmall f hf hc hback hA hB hfDef
  let eG : GammaRVIso G (pullbackObject A) (pullbackObject B) := ⟨e,hG,hGi⟩
  exact ⟨hVA,hVB,GammaRVIso.toFinite eG hVA hVB,hSquare⟩

structure GammaFiniteCellStandardComparison (G : GammaParameters.Base (M := M))
    (R : Set (VF (M := M) × VF (M := M))) extends GammaCellStandardComparison G R where
  finite12 : Map.FiniteFibres (rvObjectVolume contraction12.contractionObject)
  finite21 : Map.FiniteFibres (rvObjectVolume contraction21.contractionObject)

def GammaFiniteCellStandardComparison.finiteComparison
    {R : Set (VF (M := M) × VF (M := M))} (C : GammaFiniteCellStandardComparison G R) :
    GammaRVFiniteIso G (⟨C.contraction12.contractionObject,C.finite12⟩ : FiniteRVObject C.codes 2)
      (⟨C.contraction21.contractionObject,C.finite21⟩ : FiniteRVObject C.codes 2) :=
  GammaRVIso.toFinite C.comparison C.finite12 C.finite21

open IntegrationInACVF.Section4.Cells

theorem lemma_5_7_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    {R : Set (VF (M := M) × VF (M := M))} (h : DefinableTwoCell G R) :
    Nonempty (GammaFiniteCellStandardComparison G R) := by
  obtain ⟨C⟩ := lemma_5_7_gamma hκ hs hsmall h00 δ hδ hδ1 F h
  have hFin : FiniteMixedRVFibres (carrier C.source) := fun _ => Set.toFinite _
  exact ⟨{
    toGammaCellStandardComparison := C
    finite12 := C.contraction12.finite_volume hκ hs hsmall C.real_contains C.source_gamma C.program12_gamma hFin
    finite21 := C.contraction21.finite_volume hκ hs hsmall C.real_contains C.source_gamma C.program21_gamma hFin }⟩

end IntegrationInACVF.Section5
