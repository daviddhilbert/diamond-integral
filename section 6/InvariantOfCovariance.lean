import «section 6».TaggedGraphProjections

/-! The first assertion of Lemma 6.8. The uniform mixed-radius argument
is applied before forgetting the variable endpoint's RV tag. The accepted
Gamma piecewise-linearity background retains its precise Section 2 type. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem ProperCovariant.source_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} (hcov : ProperCovariant f) : ProperInvariant S A.carrier := by
  apply (lemma_6_5 h00 hc hκ hs hv A.carrier A.definable
    hcov.sourceVFBounded hcov.sourceRVBounded).mpr
  intro u
  let T := S ∪ Set.range (rvValues u)
  let H := taggedRelationProjection f.graph u
  have hH : (rawMixedSpace (M := M) n s).Definable T H :=
    taggedRelationProjection_definable S f.graph f.graph_definable u
  have hgeom : ProperInvariantGeometry H := by
    refine ⟨?_,?_,fun v => ?_⟩
    · obtain ⟨γ,hγ⟩ := hcov.sourceVFBounded
      refine ⟨γ,?_⟩
      rintro a ⟨b,p,hp,_⟩ i
      exact hγ (a.1,u) (hp ▸ p.property) i
    · obtain ⟨γ,hγ⟩ := hcov.imageRVBounded
      refine ⟨γ,?_⟩
      rintro a ⟨b,p,_,hfp⟩ i
      exact hγ (b,a.2) ⟨p,hfp⟩ i
    · obtain ⟨α,β,_,_,hdom,_,_⟩ := hcov.radii u v
      exact ⟨α,hdom⟩
  have hsmallT : Cardinal.mk T < κ := small_union_range hκ.le S hsmall (rvValues u)
  have hΓT : NontrivialDefinableGamma (⟨T,∅⟩ : ParameterBase M) :=
    hΓ.mono Set.subset_union_left (Set.Subset.refl _)
  have hclosed := invariant_bounded_tagged_projection_isClopen h00 hc linear hκ hs hv T hsmallT hΓT H hH hgeom
  have he : Prod.fst '' H = vfFibre A.carrier u := by
    ext a
    constructor
    · rintro ⟨q,⟨b,p,hp,_⟩,he⟩
      change (a,u) ∈ A.carrier
      rw [← he]
      exact hp ▸ p.property
    · intro ha
      obtain ⟨v,b,p,hp,hfp⟩ := graphFibreSource_cover f u ha
      exact ⟨(a,v),⟨b,p,hp,hfp⟩,rfl⟩
  rwa [he] at hclosed

theorem ProperCovariant.target_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} (hcov : ProperCovariant f) (hf : Function.Surjective f) :
    ProperInvariant S B.carrier := by
  have himage : mixedMapRange f = B.carrier := by
    ext q
    constructor
    · rintro ⟨p,rfl⟩
      exact (f p).property
    · intro hq
      obtain ⟨p,hp⟩ := hf ⟨q,hq⟩
      exact ⟨p,congrArg Subtype.val hp⟩
  have hVF : VFBounded B.carrier := himage ▸ hcov.imageVFBounded
  have hRV : RVSupportDoublyBounded B.carrier := himage ▸ hcov.imageRVBounded
  apply (lemma_6_5 h00 hc hκ hs hv B.carrier B.definable hVF hRV).mpr
  intro v
  let T := S ∪ Set.range (rvValues v)
  let R (y : Mixed M m s) (x : Mixed M n r) := f.graph x y
  let H := taggedRelationProjection R v
  have hR : (rawMixedSpace (M := M) m s).RelationDefinable (rawMixedSpace n r) S R :=
    f.graph_definable.swap (rawMixedSpace n r) (rawMixedSpace m s)
  have hH : (rawMixedSpace (M := M) m r).Definable T H :=
    taggedRelationProjection_definable S R hR v
  have hgeom : ProperInvariantGeometry H := by
    refine ⟨?_,?_,fun u => ?_⟩
    · obtain ⟨γ,hγ⟩ := hcov.imageVFBounded
      refine ⟨γ,?_⟩
      rintro b ⟨a,p,_,hfp⟩ i
      exact hγ (b.1,v) ⟨p,hfp⟩ i
    · obtain ⟨γ,hγ⟩ := hcov.sourceRVBounded
      refine ⟨γ,?_⟩
      rintro b ⟨a,p,hp,_⟩ i
      exact hγ (a,b.2) (hp ▸ p.property) i
    · obtain ⟨α,β,_,_,_,hran,_⟩ := hcov.radii u v
      exact ⟨β,hran⟩
  have hsmallT : Cardinal.mk T < κ := small_union_range hκ.le S hsmall (rvValues v)
  have hΓT : NontrivialDefinableGamma (⟨T,∅⟩ : ParameterBase M) :=
    hΓ.mono Set.subset_union_left (Set.Subset.refl _)
  have hclosed := invariant_bounded_tagged_projection_isClopen h00 hc linear hκ hs hv T hsmallT hΓT H hH hgeom
  have he : Prod.fst '' H = vfFibre B.carrier v := by
    ext b
    constructor
    · rintro ⟨q,⟨a,p,_,hfp⟩,he⟩
      change (b,v) ∈ B.carrier
      rw [← he]
      exact hfp ▸ (f p).property
    · intro hb
      obtain ⟨u,a,p,hp,hfp⟩ := graphFibreRange_cover f hf v hb
      exact ⟨(b,u),⟨a,p,hp,hfp⟩,rfl⟩
  rwa [he] at hclosed

end DiamondIntegral.Section6
