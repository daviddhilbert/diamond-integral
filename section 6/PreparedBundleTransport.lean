import «section 6».ReleasedPullbacks

/-! Transport a constructed common carried preparation to actual
source sets with equal full carriers. All protected maps remain literal
restrictions of the same map, and every prepared image is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}

theorem map_image_carrier_eq_of_source_eq
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    {B D : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (g : Map C D)
    (hAC : A.carrier = C.carrier)
    (hPoint : ∀ p : A, (f p).val = (g ⟨p.val,hAC ▸ p.property⟩).val) :
    f.image.carrier = g.image.carrier := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨⟨p.val,hAC ▸ p.property⟩,(hPoint p).symm.trans hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨⟨p.val,hAC.symm ▸ p.property⟩,(hPoint ⟨p.val,hAC.symm ▸ p.property⟩).trans hp⟩

theorem map_image_carrier_eq_of_surjective
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (hf : Function.Surjective f) :
    f.image.carrier = B.carrier := by
  ext q
  exact ⟨fun ⟨p,hp⟩ => hp ▸ (f p).property,fun hq => by
    obtain ⟨p,hp⟩ := hf ⟨q,hq⟩
    exact ⟨p,congrArg Subtype.val hp⟩⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {I : Type*}

theorem SimultaneousCarriedLift.rebase_prepared
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {X : CarriedRefinementFrame A} {f : Map A B}
    {C : I → DefSet (rawMixedSpace (M := M) n r) S}
    (F : SimultaneousCarriedLift (G := G) X f C)
    (hTarget : IsRVPullback F.lift.target.bundle.carrier)
    (hPrepared : ∀ i, IsRVPullback
      (F.lift.map.restrict (X.selectedPiece_bundle_subset (C i))).image.carrier)
    (W : DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (hPA : ∀ i, (P i).carrier ⊆ W.carrier)
    (hW : W.carrier = X.bundle.carrier)
    (hP : ∀ i, (P i).carrier = (rvCoordinateBundle (X.selectedPiece (C i)) X.freeLabel).carrier) :
    ∃ t : ℕ, ∃ Z : DefSet (rawMixedSpace (M := M) (n+1) t) S, ∃ g : Map W Z,
      SpecialCovariantChain (G := G) W Z g ∧ ProperInvariant S Z.carrier ∧
      VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
      (∀ p : W, (g p).val.1 (Fin.last n) = p.val.1 (Fin.last n)) ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image
        (g.restrict (hPA i)).toImage ∧ IsRVPullback (g.restrict (hPA i)).image.carrier := by
  let g := F.lift.map.comp (Map.inclusion (fun _ hp => hW ▸ hp))
  have hg : SpecialCovariantChain (G := G) W g.image g.toImage :=
    F.lift.special.rebaseSource h00 hW.symm (fun _ => rfl)
  have hImage : g.image.carrier = F.lift.target.bundle.carrier :=
    (map_image_carrier_eq_of_source_eq F.lift.map g hW.symm (fun _ => rfl)).symm.trans
      (map_image_carrier_eq_of_surjective F.lift.map (F.lift.special.bijective h00).surjective)
  have hProper : ProperInvariant S g.image.carrier := hImage.symm ▸
    rvCoordinateBundle_properInvariant h00 hc hκ hs hv F.lift.target.base
      F.lift.target.freeLabel F.lift.target.proper
  have hDouble : VFDoublyBounded g.image.carrier := hImage.symm ▸
    rvCoordinateBundle_doublyBounded F.lift.target.base F.lift.target.freeLabel
      F.lift.target.doublyBounded F.lift.target.proper.rvBounded
  refine ⟨F.lift.target.arity,g.image,g.toImage,hg,hProper,hDouble,hImage.symm ▸ hTarget,
    fun p => F.lift.carried ⟨p.val,hW ▸ p.property⟩,fun i => ?_⟩
  have hPiece : SpecialCovariantChain (G := G) (P i) (g.toImage.restrict (hPA i)).image
      (g.toImage.restrict (hPA i)).toImage :=
    (F.restrictions i).rebaseSource h00 (hP i).symm (fun _ => rfl)
  have hPieceImage := map_image_carrier_eq_of_source_eq
    (F.lift.map.restrict (X.selectedPiece_bundle_subset (C i)))
    (g.toImage.restrict (hPA i)) (hP i).symm (fun _ => rfl)
  exact ⟨hPiece,hPieceImage ▸ hPrepared i⟩

end DiamondIntegral.Section6
