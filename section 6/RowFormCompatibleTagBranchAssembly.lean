import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowFormCompatibleTagComponents
import «section 6».SynchronizedTagBranchExtensions
import «section 6».RetainedRVTags

/-! (Row-form version for Remark 6.20, translated from `FormCompatibleTagBranchAssembly`.)
 Assemble a branch extension from an actual ambient synchronized
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
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}

namespace SynchronizedTagBranchExtension

theorem ofMap_form_compatible_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : SynchronizedTagBranchFrame C Q)
    {B A : DefSet (rawMixedSpace (M := M) n s) S} (f : Map C B)
    (hf : Function.Surjective f) (hQC : ∀ i,(Q i).carrier ⊆ C.carrier)
    (g : Map X.ambient A)
    (ω : RowFormOn X.ambient qR)
    (hChain : FormCompatibleSynchronizedChainRow (G := G) (Fin k) X.ambient A g X.pieces ω)
    (hBranch : ∀ x : C,(g ⟨x.val,X.subset x.property⟩).val=(f x).val)
    (hOutside : ∀ x : X.ambient,x.val.2 ∉ X.tags.carrier → (g x).val.1=x.val.1) :
    ∃ F : SynchronizedTagBranchExtension (G := G) X f hQC,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) X.ambient F.output.ambient F.map X.pieces ω := by
  obtain ⟨hrs,hRetain⟩ := hChain.toSynchronizedRow.toChain.toSpecial.retainsRV
  let σ := rvTailIndex hrs
  let V := selectedRVTagSet X.tags σ
  have hRV (x : X.ambient) : (g x).val.2 ∘ σ=x.val.2 := funext (hRetain x)
  have hSelected (x : X.ambient) : (g x).val.2 ∈ V.carrier ↔ x.val.2 ∈ X.tags.carrier := by
    change (g x).val.2 ∘ σ ∈ X.tags.carrier ↔ _
    rw [hRV]
  have hSource : B.carrier=(focusActive A V).carrier := by
    have he := image_eq_of_surjective_liesOver g f hf X.subset (fun x => (hBranch x).symm)
    have hi := map_branch_image g (hChain.toSynchronizedRow.toChain.toSpecial.bijective h00).surjective
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
    obtain ⟨a,ha⟩ := (hChain.toSynchronizedRow.toChain.toSpecial.bijective h00).surjective ⟨x,hx⟩
    obtain ⟨b,hb⟩ := (hChain.toSynchronizedRow.toChain.toSpecial.bijective h00).surjective ⟨y,hy⟩
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
    proper := hChain.toSynchronizedRow.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
    doublyBounded := hChain.toSynchronizedRow.toChain.toSpecial.target_vfDoublyBounded X.doublyBounded
    pieces_subset := fun i y hy => by
      obtain ⟨x,hx⟩ := hy
      exact hx ▸ (g.restrict (X.pieces_subset i) x).property
    pieces_proper := fun i => ((hChain.toSynchronizedRow.atPiece i).literal_restriction h00 (X.pieces_subset i)).target_properInvariant
      h00 hc hκ hs hv
    source_eq := hSource
    pieces_eq := hPieces
    outside_tagged := hPartial }
  exact ⟨⟨Y,g,hChain.toSynchronizedRow,(fun _ => rfl),hBranch,hSelected,hOutside⟩,hChain⟩

end SynchronizedTagBranchExtension
end DiamondIntegral.Section6
