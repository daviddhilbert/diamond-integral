import «section 6».FormCompatibleTagComponents
import «section 6».SynchronizedTagBranchExtensions
import «section 6».RetainedRVTags

/-! Assemble a branch extension from an actual ambient synchronized
chain. Exact selected and protected images follow from retained labels
and agreement of the actual maps on the selected source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}

namespace SynchronizedTagBranchExtension

theorem ofMap_form_compatible
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : SynchronizedTagBranchFrame C Q)
    {B A : DefSet (rawMixedSpace (M := M) n s) S} (f : Map C B)
    (hf : Function.Surjective f) (hQC : ∀ i,(Q i).carrier ⊆ C.carrier)
    (g : Map X.ambient A)
    (ω : Map X.ambient (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hChain : FormCompatibleSynchronizedChain (G := G) (Fin k) X.ambient A g X.pieces ω)
    (hBranch : ∀ x : C,(g ⟨x.val,X.subset x.property⟩).val=(f x).val)
    (hOutside : ∀ x : X.ambient,x.val.2 ∉ X.tags.carrier → (g x).val.1=x.val.1) :
    ∃ F : SynchronizedTagBranchExtension (G := G) X f hQC,
      FormCompatibleSynchronizedChain (G := G) (Fin k) X.ambient F.output.ambient F.map X.pieces ω := by
  obtain ⟨hrs,hRetain⟩ := hChain.toSynchronized.toChain.toSpecial.retainsRV
  let σ := rvTailIndex hrs
  let V := selectedRVTagSet X.tags σ
  have hRV (x : X.ambient) : (g x).val.2 ∘ σ=x.val.2 := funext (hRetain x)
  have hSelected (x : X.ambient) : (g x).val.2 ∈ V.carrier ↔ x.val.2 ∈ X.tags.carrier := by
    change (g x).val.2 ∘ σ ∈ X.tags.carrier ↔ _
    rw [hRV]
  have hSource : B.carrier=(focusActive A V).carrier := by
    have he := image_eq_of_surjective_liesOver g f hf X.subset (fun x => (hBranch x).symm)
    have hi := map_branch_image g (hChain.toSynchronized.toChain.toSpecial.bijective h00).surjective
      X.tags σ hRV X.subset X.source_eq
    exact congrArg DefSet.carrier (he.trans hi)
  have hPieces (i) : (f.restrict (hQC i)).image.carrier=
      (focusActive (g.restrict (X.pieces_subset i)).image V).carrier := by
    have hImage := map_image_carrier_eq_of_source_eq (f.restrict (hQC i))
      (g.restrict ((hQC i).trans X.subset)) rfl
      (fun x => (hBranch ⟨x.val,hQC i x.property⟩).symm)
    exact hImage.trans (congrArg DefSet.carrier (map_tag_slice_image g X.tags σ hRV
      (X.pieces_subset i) ((hQC i).trans X.subset) (X.pieces_eq i)))
  have hPartial : ∀ x ∈ A.carrier,∀ y ∈ A.carrier,x.2=y.2 →
      x.2 ∉ V.carrier → tupleRV M x.1=tupleRV M y.1 := by
    intro x hx y hy hxy hu
    obtain ⟨a,ha⟩ := (hChain.toSynchronized.toChain.toSpecial.bijective h00).surjective ⟨x,hx⟩
    obtain ⟨b,hb⟩ := (hChain.toSynchronized.toChain.toSpecial.bijective h00).surjective ⟨y,hy⟩
    have haV : (g a).val=x := congrArg Subtype.val ha
    have hbV : (g b).val=y := congrArg Subtype.val hb
    have hOld : a.val.2=b.val.2 := by rw [← hRV a,← hRV b,haV,hbV,hxy]
    have hau : a.val.2 ∉ X.tags.carrier := by
      intro h
      apply hu
      rw [← haV]
      exact (hSelected a).mpr h
    have hbu : b.val.2 ∉ X.tags.carrier := hOld ▸ hau
    rw [← haV,← hbV,hOutside a hau,hOutside b hbu]
    exact X.outside_tagged a.val a.property b.val b.property hOld hau
  let Y : SynchronizedTagBranchFrame B (fun i => (f.restrict (hQC i)).image) := {
    ambient := A
    pieces := fun i => (g.restrict (X.pieces_subset i)).image
    tags := V
    proper := hChain.toSynchronized.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
    doublyBounded := hChain.toSynchronized.toChain.toSpecial.target_vfDoublyBounded X.doublyBounded
    pieces_subset := fun i y hy => by
      obtain ⟨x,hx⟩ := hy
      exact hx ▸ (g.restrict (X.pieces_subset i) x).property
    pieces_proper := fun i => ((hChain.toSynchronized.atPiece i).literal_restriction h00 (X.pieces_subset i)).target_properInvariant
      h00 hc hκ hs hv
    source_eq := hSource
    pieces_eq := hPieces
    outside_tagged := hPartial }
  exact ⟨⟨Y,g,hChain.toSynchronized,(fun _ => rfl),hBranch,hSelected,hOutside⟩,hChain⟩

end SynchronizedTagBranchExtension
end DiamondIntegral.Section6
