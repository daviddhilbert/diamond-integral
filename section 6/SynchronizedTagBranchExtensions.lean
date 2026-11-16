import «section 6».TagBranchImageGeometry

/-! Runtime extensions from a selected whole-label branch. Both the
local and ambient maps retain their actual protected images; the next
branch frame therefore supports extension of a further component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}

structure SynchronizedTagBranchExtension (X : SynchronizedTagBranchFrame C Q)
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map C B)
    (hQC : ∀ i,(Q i).carrier ⊆ C.carrier) where
  output : SynchronizedTagBranchFrame B (fun i => (f.restrict (hQC i)).image)
  map : Map X.ambient output.ambient
  chain : SynchronizedCentripetalChain (G := G) (Fin k) X.ambient output.ambient map X.pieces
  piece_images : ∀ i,output.pieces i=(map.restrict (X.pieces_subset i)).image
  branch : ∀ x : C,(map ⟨x.val,X.subset x.property⟩).val=(f x).val
  selected : ∀ x : X.ambient,(map x).val.2 ∈ output.tags.carrier ↔ x.val.2 ∈ X.tags.carrier
  outside : ∀ x : X.ambient,x.val.2 ∉ X.tags.carrier → (map x).val.1=x.val.1

namespace SynchronizedTagBranchFrame

theorem extends_centripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : SynchronizedTagBranchFrame C Q) (D : CentripetalData (G := G) C)
    (E : ∀ i,CentripetalData (G := G) (Q i)) (hData : ∀ i,ApertureRestrictionData D (E i))
    (hQC : ∀ i,(Q i).carrier ⊆ C.carrier) :
    Nonempty (SynchronizedTagBranchExtension (G := G) X D.bijection hQC) := by
  obtain ⟨F,H,hj,hCoeff,hRestr,hPoint,hOutside,hChain⟩ := exists_synchronized_tag_component_extension
    D X.tags X.source_eq X.proper X.doublyBounded (X.tagged_of_local D.tagged)
    X.pieces Q X.pieces_subset X.pieces_proper X.pieces_eq E hData
  let V := selectedRVTagSet X.tags (Fin.natAdd 1)
  have hRV (x : X.ambient) : (F.bijection x).val.2 ∘ Fin.natAdd 1=x.val.2 := by
    funext i
    change Fin.append (fun _ : Fin 1 => branchTag (F.core x.val)) x.val.2 (Fin.natAdd 1 i)=x.val.2 i
    rw [Fin.append_right]
  have hSelected (x : X.ambient) : (F.bijection x).val.2 ∈ V.carrier ↔ x.val.2 ∈ X.tags.carrier := by
    change (F.bijection x).val.2 ∘ Fin.natAdd 1 ∈ X.tags.carrier ↔ _
    rw [hRV]
  have hSource : D.map.image.carrier=(focusActive F.map.image V).carrier := by
    have he := image_eq_of_surjective_liesOver F.bijection D.bijection (D.bijective h00).surjective
      X.subset (fun x => (hPoint x.val x.property).symm)
    have hi := map_branch_image F.bijection (F.bijective h00).surjective X.tags (Fin.natAdd 1)
      hRV X.subset X.source_eq
    exact congrArg DefSet.carrier (he.trans hi)
  have hPieces (i) : (D.bijection.restrict (hQC i)).image.carrier=
      (focusActive (F.bijection.restrict (X.pieces_subset i)).image V).carrier := by
    have hImage := map_image_carrier_eq_of_source_eq (D.bijection.restrict (hQC i))
      (F.bijection.restrict ((hQC i).trans X.subset)) rfl
      (fun x => (hPoint x.val (hQC i x.property)).symm)
    exact hImage.trans (congrArg DefSet.carrier (map_tag_slice_image F.bijection X.tags (Fin.natAdd 1)
      hRV (X.pieces_subset i) ((hQC i).trans X.subset) (X.pieces_eq i)))
  have hPartial : ∀ x ∈ F.map.image.carrier,∀ y ∈ F.map.image.carrier,x.2=y.2 →
      x.2 ∉ V.carrier → tupleRV M x.1=tupleRV M y.1 := by
    intro x hx y hy hxy hu
    obtain ⟨a,ha⟩ := (F.bijective h00).surjective ⟨x,hx⟩
    obtain ⟨b,hb⟩ := (F.bijective h00).surjective ⟨y,hy⟩
    have haV : (F.bijection a).val=x := congrArg Subtype.val ha
    have hbV : (F.bijection b).val=y := congrArg Subtype.val hb
    have hOld : a.val.2=b.val.2 := by rw [← hRV a,← hRV b,haV,hbV,hxy]
    have hau : a.val.2 ∉ X.tags.carrier := by
      intro h
      apply hu
      rw [← haV]
      exact (hSelected a).mpr h
    have hbu : b.val.2 ∉ X.tags.carrier := hOld ▸ hau
    rw [← haV,← hbV]
    change tupleRV M (F.point a.val).1=tupleRV M (F.point b.val).1
    rw [hOutside a.val a.property hau,hOutside b.val b.property hbu]
    exact X.outside_tagged a.val a.property b.val b.property hOld hau
  let Y : SynchronizedTagBranchFrame D.map.image (fun i => (D.bijection.restrict (hQC i)).image) := {
    ambient := F.map.image
    pieces := fun i => (F.bijection.restrict (X.pieces_subset i)).image
    tags := V
    proper := F.image_properInvariant h00 hc hκ hs hv
    doublyBounded := F.image_vfDoublyBounded
    pieces_subset := fun i y hy => by
      obtain ⟨x,hx⟩ := hy
      exact hx ▸ (F.bijection.restrict (X.pieces_subset i) x).property
    pieces_proper := fun i => ((hChain.atPiece i).literal_restriction h00 (X.pieces_subset i)).target_properInvariant
      h00 hc hκ hs hv
    source_eq := hSource
    pieces_eq := hPieces
    outside_tagged := hPartial }
  refine ⟨⟨Y,F.bijection,hChain,(fun _ => rfl),?_,hSelected,?_⟩⟩
  · exact fun x => hPoint x.val x.property
  · exact fun x hx => hOutside x.val x.property hx

end SynchronizedTagBranchFrame
end DiamondIntegral.Section6
