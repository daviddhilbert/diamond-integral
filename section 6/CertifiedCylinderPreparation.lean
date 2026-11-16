import «section 6».IteratedCarriedPreparation
import «section 6».PreparedBundleTransport

/-! Full cylinder preparation retaining a simultaneous permitted
component certificate. Exact source and protected carrier equalities
are transported, so the conclusion is reusable in dimension induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem certified_cylinder_preparation_of_simultaneous_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (C : I → DefSet (rawMixedSpace (M := M) n r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (f : Map A B) (hChain : SimultaneousCentripetalChain (G := G) I A B f C)
    (hBRV : IsRVPullback B.carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hCA i)).image.carrier)
    (j : Fin r) (W : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hPA : ∀ i,(P i).carrier ⊆ W.carrier)
    (hW : W.carrier=(rvCoordinateBundle A j).carrier)
    (hP : ∀ i,(P i).carrier=(rvCoordinateBundle (C i) j).carrier) :
    ∃ t : ℕ,∃ Z : DefSet (rawMixedSpace (M := M) (n+1) t) S,∃ g : Map W Z,
      SimultaneousCentripetalChain (G := G) I W Z g P ∧ ProperInvariant S Z.carrier ∧
        VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
        (∀ p : W,(g p).val.1 (Fin.last n)=p.val.1 (Fin.last n)) ∧
        ∀ i,IsRVPullback (g.restrict (hPA i)).image.carrier := by
  let X := CarriedRefinementFrame.identity A j hA hD
  obtain ⟨F,hF⟩ := hChain.carried_certified_lift_exists h00 hc hκ hs hv X
  have hSelected (i) : X.selectedPiece (C i)=C i := by
    apply defSet_eq_of_carrier_eq
    ext p
    rw [X.mem_selectedPiece]
    change (p ∈ A.carrier ∧ (p.1,p.2 ∘ id) ∈ (C i).carrier) ↔ p ∈ (C i).carrier
    simpa only [Function.comp_id,Prod.mk.eta] using
      (show (p ∈ A.carrier ∧ p ∈ (C i).carrier) ↔ p ∈ (C i).carrier from
        ⟨fun h => h.2,fun hp => ⟨hCA i hp,hp⟩⟩)
  let g := F.lift.map.comp (Map.inclusion (fun _ hp => hW ▸ hp))
  have hSource : X.bundle=W := defSet_eq_of_carrier_eq hW.symm
  have hCert : SimultaneousCentripetalChain (G := G) I W F.lift.target.bundle g P :=
    (hF.changeSource hSource (fun _ => rfl)).changePieces (fun i =>
      defSet_eq_of_carrier_eq (by rw [hSelected i]; exact (hP i).symm))
  refine ⟨F.lift.target.arity,F.lift.target.bundle,g,hCert,
    rvCoordinateBundle_properInvariant h00 hc hκ hs hv F.lift.target.base F.lift.target.freeLabel F.lift.target.proper,
    rvCoordinateBundle_doublyBounded F.lift.target.base F.lift.target.freeLabel
      F.lift.target.doublyBounded F.lift.target.proper.rvBounded,
    F.lift.target_pullback hBRV,fun p => F.lift.carried ⟨p.val,hW ▸ p.property⟩,fun i => ?_⟩
  have hPieceSource : (rvCoordinateBundle (X.selectedPiece (C i)) X.freeLabel).carrier=(P i).carrier := by
    rw [hSelected i]
    exact (hP i).symm
  have hImage := map_image_carrier_eq_of_source_eq
    (F.lift.map.restrict (X.selectedPiece_bundle_subset (C i))) (g.restrict (hPA i)) hPieceSource (fun _ => rfl)
  rw [← hImage]
  exact F.lift.partition_image_pullback h00 (hChain.toChain.toSpecial.bijective h00).injective
    (C i) (hCA i) (hPrepared i)

end DiamondIntegral.Section6
