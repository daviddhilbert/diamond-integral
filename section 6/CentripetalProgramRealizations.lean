import «section 6».CentripetalProgramTemplates
import «section 6».FocusComponentTemplateRealizations
import «section 6».SynchronizedChainTransport
import «section 6».CentripetalPullbackPreservation

/-! Exact runtime certificates for finite component programs. The
computed target and every protected family specialize to the literal
images of a common permitted chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem map_image_eq_target_of_surjective
    {P Q : SpecialTransformations.DefinableGeometry.Space LRV M}
    {A : DefSet P S} {B : DefSet Q S} (f : Map A B) (hf : Function.Surjective f) : f.image=B := by
  apply defSet_eq_of_carrier_eq
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact (f x).property
  · intro hy
    obtain ⟨x,hx⟩ := hf ⟨y,hy⟩
    exact ⟨x,congrArg Subtype.val hx⟩

theorem VFDoublyBounded.mono {A B : Set (Mixed M n r)}
    (h : VFDoublyBounded A) (hBA : B ⊆ A) : VFDoublyBounded B := by
  obtain ⟨γ,hγ⟩ := h
  exact ⟨γ,fun x hx => hγ x (hBA hx)⟩

theorem SpecialCovariantChain.target_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    (h : SpecialCovariantChain (G := G) A B f) : ProperInvariant S B.carrier := by
  induction h with
  | identity A hA => exact hA
  | regularize A hA hVF => exact regularization_properInvariant h00 hc hκ hs hv A hA hVF
  | centripetal A D => exact D.image_properInvariant h00 hc hκ hs hv
  | zeroCentered A D => exact D.image_properInvariant h00 hc hκ hs hv
  | comp hf hg ihf ihg => exact ihg

theorem SpecialCovariantChain.target_vfDoublyBounded
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    (h : SpecialCovariantChain (G := G) A B f) (hA : VFDoublyBounded A.carrier) :
    VFDoublyBounded B.carrier := by
  induction h with
  | identity => exact hA
  | regularize A hA hVF => exact regularized_vfDoublyBounded hVF
  | centripetal A D => exact D.image_vfDoublyBounded
  | zeroCentered A D => exact D.image_vfDoublyBounded
  | comp hf hg ihf ihg => exact ihg (ihf hA)

structure CentripetalProgramRealization
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) where
  map : Map (A.fibre a) ((T.target A).fibre a)
  chain : SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) ((T.target A).fibre a) map
    (fun i => (P i).fibre a)
  graph : {z | Sum.elim a z ∈ (T.transition A).graph}=
    (rawMixedSpace n r).relation (rawMixedSpace n s) map.graph
  pieces : ∀ i (hPA : ((P i).fibre a).carrier ⊆ (A.fibre a).carrier),
    (T.pieceTarget A (P i)).fibre a=(map.restrict hPA).image

namespace CentripetalProgramRealization

theorem ofMap (h00 : M ⊨ Axioms.ACVF00)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} (f : Map (A.fibre a) B)
    (hChain : SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a))
    (hGraph : {z | Sum.elim a z ∈ (T.transition A).graph}=
      (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph) :
    Nonempty (CentripetalProgramRealization (G := G) T A P a) := by
  have hTarget : (T.target A).fibre a=B :=
    (mixedRelationImageTemplate_at_image A (T.transition A).graph (T.transition A).definable a f hGraph).trans
      (map_image_eq_target_of_surjective f (hChain.toChain.toSpecial.bijective h00).surjective)
  let g := changeMapTarget f hTarget.symm
  have hGChain := hChain.changeTarget hTarget.symm (fun x => (changeMapTarget_value f hTarget.symm x).symm)
  have hGGraph : {z | Sum.elim a z ∈ (T.transition A).graph}=
      (rawMixedSpace n r).relation (rawMixedSpace n s) g.graph := by
    cases hTarget
    exact hGraph
  refine ⟨⟨g,hGChain,hGGraph,?_⟩⟩
  intro i hPA
  exact mixedRelationImageTemplate_at_restriction (P i) (T.transition A).graph
    (T.transition A).definable a g hPA hGGraph

end CentripetalProgramRealization
end DiamondIntegral.Section6
