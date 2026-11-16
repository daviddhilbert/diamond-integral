import «section 6».UnaryBoundaryCoreLabels
import «section 6».RVTagConjugation
import «section 6».ProtectedRootIteration
import «section 6».UnaryStepLabels

/-! Actual special preparation of whole core fibres, with a complete
label equivalence. A pair of these preparations preserves an existing
paired-core matching by the literal conjugation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure UnaryTagPreparation (A : DefSet (rawMixedSpace (M := M) 1 r) S) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) 1 arity) S
  map : Map A target
  bijective : Function.Bijective map
  chain : SpecialCovariantChain (G := G) A target map
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  pullback : IsRVPullback target.carrier
  leadingLabel : Fin arity
  leadingTerm : ∀ p ∈ target.carrier,rv M (p.1 0)=p.2 leadingLabel
  labels : ∀ p q : A,(map p).val.2=(map q).val.2 ↔ p.val.2=q.val.2

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem UnaryFocusData.exists_boundary_core_preparation (D : UnaryFocusData A)
    (d : (Fin r → RVInfinity M) → VF M)
    (dMap : Map (focusActive A D.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hdMap : ∀ p : focusActive A D.activeTags,(dMap p).val 0=d p.val.2)
    (hd : ∀ u ∈ D.activeTags.carrier,d u ≠ 0)
    (hAll : ∀ p ∈ A.carrier,p.2 ∈ D.activeTags.carrier)
    (hSmall : ∀ p ∈ A.carrier,p.2 ∈ D.activeTags.carrier → vfValue (D.focus p.2) < vfValue (d p.2))
    (hDiscs : ∀ u (hu : u ∈ D.activeTags.carrier) (x : VF M),
      ((fun _ : Fin 1 => x),u) ∈ A.carrier ↔ x ∈ centeredGammaDisc (D.focus u) (finiteValue (d u) (hd u hu)))
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    Nonempty (UnaryTagPreparation (G := G) A) := by
  obtain ⟨E,hCoord,hActive,hFocus,hCore,hImageRV⟩ := D.exists_boundary_core_component
    d dMap hdMap hd hAll hSmall hDiscs h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
  refine ⟨{
    arity := 1+(1+r)
    target := (regularizeMap E.map.image).image
    map := centripetalStepMap E
    bijective := centripetalStepMap_bijective E h00
    chain := .comp (.centripetal A E) (.regularize E.map.image (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded)
    proper := regularization_properInvariant h00 hc hκ hs hv E.map.image
      (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded
    doublyBounded := regularized_vfDoublyBounded E.image_vfDoublyBounded
    pullback := regularization_rvPullback E.map.image hImageRV
    leadingLabel := 0
    leadingTerm := fun p hp => UnaryRootFamily.step_image_leading_term E hp
    labels := unary_boundary_step_tags_iff D d E hCoord hActive hFocus hCore hAll hd hDiscs h00 }⟩

namespace UnaryTagPreparation
variable {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable (F : UnaryTagPreparation (G := G) A) (H : UnaryTagPreparation (G := G) B)

def conjugate (f : Map A B) : Map F.target H.target :=
  H.map.comp (f.comp (F.map.inverse F.bijective))

theorem conjugate_bijective (f : Map A B) (hf : Function.Bijective f) :
    Function.Bijective (F.conjugate H f) := by
  have hInv : Function.Bijective (F.map.inverse F.bijective) := by
    constructor
    · intro p q he
      have hh := congrArg F.map he
      simpa only [Map.apply_inverse] using hh
    · intro a
      exact ⟨F.map a,Map.inverse_apply F.map F.bijective a⟩
  exact H.bijective.comp (hf.comp hInv)

theorem conjugate_whole_fibres (f : Map A B) (hf : Function.Bijective f) (h : MapsWholeTagFibres f) :
    MapsWholeTagFibres (F.conjugate H f) :=
  h.conjugate f hf F.map F.bijective H.map H.bijective F.labels H.labels

theorem conjugate_at (f : Map A B) (p : A) : F.conjugate H f (F.map p)=H.map (f p) := by
  change H.map (f (F.map.inverse F.bijective (F.map p)))=H.map (f p)
  rw [Map.inverse_apply]

end UnaryTagPreparation
end DiamondIntegral.Section6
