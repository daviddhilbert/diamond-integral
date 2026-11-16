import «section 6».RefinedPartitionPieces

/-! Exact full-set images of partition pieces under a carried lift.
Bijectivity and the commuting square recover source membership; an
RV-pullback old image therefore gives an RV-pullback carried image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def CarriedRefinementFrame.oldMap (X : CarriedRefinementFrame A) : Map X.bundle A :=
  ((selectRVLabelsMap X.base X.labels).comp (bundleProjection X.base X.freeLabel)).corestrict
    (fun p => X.source_subset (Fin.init p.val.1,p.val.2) p.property.1)

theorem CarriedRefinementFrame.selectedPiece_bundle_subset (X : CarriedRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) :
    (rvCoordinateBundle (X.selectedPiece P) X.freeLabel).carrier ⊆ X.bundle.carrier :=
  fun p hp => ((X.selectedPiece_bundle_mem P p).mp hp).1

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
variable {X : CarriedRefinementFrame A}

theorem CarriedChainLift.partition_image
    (h00 : M ⊨ Axioms.ACVF00) (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier) :
    (F.map.restrict (X.selectedPiece_bundle_subset P)).image.carrier =
      (rvCoordinateBundle (F.target.selectedPiece (f.restrict hPA).image) F.target.freeLabel).carrier := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    let p' : X.bundle := ⟨p.val,X.selectedPiece_bundle_subset P p.property⟩
    apply (F.target.selectedPiece_bundle_mem (f.restrict hPA).image (F.map p').val).mpr
    refine ⟨(F.map p').property,?_⟩
    have hOld : (X.oldPoint p').val ∈ P.carrier := ((X.selectedPiece_bundle_mem P p.val).mp p.property).2
    refine ⟨⟨(X.oldPoint p').val,hOld⟩,?_⟩
    exact (F.commutes p').symm
  · intro hq
    obtain ⟨hTarget,hOldImage⟩ := (F.target.selectedPiece_bundle_mem (f.restrict hPA).image q).mp hq
    obtain ⟨p,hp⟩ := (F.special.bijective h00).surjective ⟨q,hTarget⟩
    have hpoint : (F.map p).val = q := congrArg Subtype.val hp
    have hComm := F.commutes p
    rw [hpoint] at hComm
    obtain ⟨a,ha⟩ := hOldImage
    have hEq : f ⟨a.val,hPA a.property⟩ = f (X.oldPoint p) := Subtype.ext (ha.trans hComm)
    have hOld : (X.oldPoint p).val ∈ P.carrier := (congrArg Subtype.val (hinj hEq)) ▸ a.property
    have hSource : p.val ∈ (rvCoordinateBundle (X.selectedPiece P) X.freeLabel).carrier :=
      (X.selectedPiece_bundle_mem P p.val).mpr ⟨p.property,hOld⟩
    exact ⟨⟨p.val,hSource⟩,hpoint⟩

theorem CarriedChainLift.partition_image_pullback
    (h00 : M ⊨ Axioms.ACVF00) (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier)
    (hP : IsRVPullback (f.restrict hPA).image.carrier) :
    IsRVPullback (F.map.restrict (X.selectedPiece_bundle_subset P)).image.carrier := by
  rw [F.partition_image h00 hinj P hPA]
  apply F.target.selectedPiece_bundle_pullback (f.restrict hPA).image _ hP
  rintro q ⟨p,hp⟩
  exact hp ▸ (f.restrict hPA p).property

end DiamondIntegral.Section6
