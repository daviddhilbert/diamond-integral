import IntegrationSection5.FiniteContraction
import IntegrationSection5.GammaRVIsomorphism
import IntegrationSection5.Corollary58

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
variable {G : GammaParameters.Base (M := M)} {S : Set M} {k : ℕ}

abbrev FiniteRVObject (S : Set M) (k : ℕ) :=
  @SpecialTransformations.Section4.RVFiniteObject M (@CanonicalStructure.normalize M sM) S k

def finiteRVHomMap {U V : FiniteRVObject (M := M) S k} (f : U ⟶ V) :
    Map (rvObjectDomain U.obj) (rvObjectDomain V.obj) :=
  @SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S k U.obj V.obj f.hom

/-- An isomorphism in the actual RV[k] full subcategory, with original-Gamma graphs. -/
structure GammaRVFiniteIso (G : GammaParameters.Base (M := M))
    (U V : FiniteRVObject (M := M) S k) where
  iso : U ≅ V
  hom_graph : GammaGraphDefinable G (rvMapGraph (finiteRVHomMap iso.hom))
  inv_graph : GammaGraphDefinable G (rvMapGraph (finiteRVHomMap iso.inv))

def GammaRVIso.toFinite
    {U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k}
    (e : GammaRVIso G U V) (hU : Map.FiniteFibres (rvObjectVolume U))
    (hV : Map.FiniteFibres (rvObjectVolume V)) :
    GammaRVFiniteIso G (⟨U,hU⟩ : FiniteRVObject S k) (⟨V,hV⟩ : FiniteRVObject S k) where
  iso := ObjectProperty.isoMk _ e.iso
  hom_graph := e.hom_graph
  inv_graph := e.inv_graph

variable {m : ℕ} {A : Set (Point (M := M) 2 m)}

structure GammaMixedFiniteStandardComparison (G : GammaParameters.Base (M := M))
    {m : ℕ} (A : Set (Point (M := M) 2 m)) extends GammaMixedStandardComparison G A where
  finite12 : Map.FiniteFibres (rvObjectVolume contraction12.contractionObject)
  finite21 : Map.FiniteFibres (rvObjectVolume contraction21.contractionObject)

def GammaMixedStandardComparison.toFinite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (C : GammaMixedStandardComparison G A) (hFinite : FiniteMixedRVFibres A) :
    GammaMixedFiniteStandardComparison G A where
  toGammaMixedStandardComparison := C
  finite12 := C.contraction12.finite_volume hκ hs hsmall C.real_contains C.source_gamma C.program12_gamma
    (C.source_eq.symm ▸ hFinite)
  finite21 := C.contraction21.finite_volume hκ hs hsmall C.real_contains C.source_gamma C.program21_gamma
    (C.source_eq.symm ▸ hFinite)

def GammaMixedFiniteStandardComparison.finiteComparison (C : GammaMixedFiniteStandardComparison G A) :
    GammaRVFiniteIso G (⟨C.contraction12.contractionObject,C.finite12⟩ : FiniteRVObject C.codes 2)
      (⟨C.contraction21.contractionObject,C.finite21⟩ : FiniteRVObject C.codes 2) :=
  GammaRVIso.toFinite C.comparison C.finite12 C.finite21

open IntegrationInACVF.Section3ACVF SpecialTransformations.Section3.GammaParameters
structure FiniteCorollary58Data (G : GammaParameters.Base (M := M)) {m : ℕ} (A : Set (Point (M := M) 2 m)) where
  injection : PositionedCellLabelInjection G A
  comparison : GammaMixedFiniteStandardComparison G injection.target

theorem lemma_5_8_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    {m : ℕ} (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A)
    (hFinite : FiniteMixedRVFibres A) : Nonempty (FiniteCorollary58Data G A) := by
  obtain ⟨C⟩ := lemma_5_8 hκ hs h00 G hsmall hGenerated δ hδ hδ1 F A hA
  have hFin := GammaIso.finite_mixed_rv_fibres hκ hs hsmall C.injection.iso hFinite
  exact ⟨⟨C.injection,GammaMixedStandardComparison.toFinite hκ hs hsmall C.comparison hFin⟩⟩

end IntegrationInACVF.Section5
