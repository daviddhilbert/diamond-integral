import «section 6».AmbientCoreBranchLabels

/-! A single special-covariant preparation on the whole ambient set
isolates selected offset cores into actual RV-label branches, with
proper doubly bounded RV-pullback geometry on both sides of the cut. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

structure AmbientCorePreparation (F : UnaryFocusData A)
    (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) 1 arity) S
  map : Map A target
  chain : SpecialCovariantChain (G := G) A target map
  bijective : Function.Bijective map
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  pullback : IsRVPullback target.carrier
  tagged : ∀ p ∈ target.carrier,∀ q ∈ target.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1
  corePullback : IsRVPullback (map.restrict (F.offsetCoreDomain_subset dMap)).image.carrier
  outsidePullback : IsRVPullback
    (map.restrict (show (properSubsetComplement A (F.offsetCoreDomain dMap)).carrier ⊆ A.carrier from fun _ hp => hp.1)).image.carrier
  coreLabels : ∀ p q : F.offsetCoreDomain dMap,
    (map ⟨p.val,F.offsetCoreDomain_subset dMap p.property⟩).val.2=
      (map ⟨q.val,F.offsetCoreDomain_subset dMap q.property⟩).val.2 ↔ p.val.2=q.val.2

namespace AmbientCorePreparation
variable {F : UnaryFocusData A}
variable {dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)}

def coreTags (T : AmbientCorePreparation (G := G) F dMap) : DefSet (rawRVSpace (M := M) T.arity) S :=
  locusTags T.target (T.map.restrict (F.offsetCoreDomain_subset dMap)).image

theorem core_iff_tags (T : AmbientCorePreparation (G := G) F dMap) (p : A) :
    p.val ∈ (F.offsetCoreDomain dMap).carrier ↔ (T.map p).val.2 ∈ T.coreTags.carrier :=
  prepared_subset_source_labels_iff T.map T.bijective.injective (F.offsetCoreDomain_subset dMap)
    T.corePullback T.tagged p

end AmbientCorePreparation

theorem UnaryFocusData.exists_ambient_core_preparation (F : UnaryFocusData A)
    (d : (Fin r → RVInfinity M) → VF M)
    (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)
    (hRV : IsRVPullback A.carrier)
    (hCenters : ∀ u ∈ F.activeTags.carrier,((fun _ : Fin 1 => F.focus u),u) ∈ A.carrier)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hSmall : ∀ u ∈ F.activeTags.carrier,vfValue (F.focus u) < vfValue (d u))
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    Nonempty (AmbientCorePreparation (G := G) F dMap) := by
  obtain ⟨E,hCoord,hActive,hFocus,hCore,hERv⟩ := F.exists_ambient_boundary_component d dMap hdMap hd
    (fun p hp hu => hSmall p.2 hu) hRV h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
  have hCoreRV := regularized_centripetal_restriction_rvPullback E (F.offsetCoreDomain dMap)
    (F.offsetCoreDomain_subset dMap)
    (F.ambient_boundary_core_image_rvPullback d dMap hdMap E hCoord hActive hFocus hCore hRV hCenters hd hSmall)
  have hGlobalRV := regularization_rvPullback E.map.image hERv
  refine ⟨{
    arity := 1+(1+r)
    target := (regularizeMap E.map.image).image
    map := centripetalStepMap E
    chain := .comp (.centripetal A E) (.regularize E.map.image
      (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded)
    bijective := centripetalStepMap_bijective E h00
    proper := regularization_properInvariant h00 hc hκ hs hv E.map.image
      (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded
    doublyBounded := regularized_vfDoublyBounded E.image_vfDoublyBounded
    pullback := hGlobalRV
    tagged := by rw [regularization_carrier]; exact regularized_tagged _
    corePullback := hCoreRV
    outsidePullback := image_complement_rvPullback (centripetalStepMap E) (centripetalStepMap_bijective E h00)
      (F.offsetCoreDomain_subset dMap) hGlobalRV hCoreRV
    coreLabels := ambient_boundary_core_labels_iff F d dMap hdMap E hCoord hActive hFocus hCore hRV hCenters hd hSmall h00 }⟩

end DiamondIntegral.Section6
