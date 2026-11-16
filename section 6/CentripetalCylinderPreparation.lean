import «section 6».SimultaneousCarriedChains
import «section 6».PreparedBundleTransport

/-! In every dimension, an actual simultaneous projected preparation
lifts to full-set cylinders while carrying the released VF coordinate
unchanged. Each protected map is a literal special restriction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem cylinder_preparation_of_simultaneous_chain
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
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ W.carrier)
    (hW : W.carrier=(rvCoordinateBundle A j).carrier)
    (hP : ∀ i,(P i).carrier=(rvCoordinateBundle (C i) j).carrier) :
    ∃ t : ℕ,∃ Z : DefSet (rawMixedSpace (M := M) (n+1) t) S,∃ g : Map W Z,
      SpecialCovariantChain (G := G) W Z g ∧ ProperInvariant S Z.carrier ∧
        VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
        (∀ p : W,(g p).val.1 (Fin.last n)=p.val.1 (Fin.last n)) ∧
        ∀ i,SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image (g.restrict (hPA i)).toImage ∧
          IsRVPullback (g.restrict (hPA i)).image.carrier := by
  let X := CarriedRefinementFrame.identity A j hA hD
  obtain ⟨F,hFPrepared⟩ := hChain.carried_preparation_exists h00 hc hκ hs hv hCA hPrepared X
  have hSelected (i) : X.selectedPiece (C i)=C i := by
    apply defSet_eq_of_carrier_eq
    ext p
    rw [X.mem_selectedPiece]
    change (p ∈ A.carrier ∧ (p.1,p.2 ∘ id) ∈ (C i).carrier) ↔ p ∈ (C i).carrier
    simpa only [Function.comp_id,Prod.mk.eta] using
      (show (p ∈ A.carrier ∧ p ∈ (C i).carrier) ↔ p ∈ (C i).carrier from
        ⟨fun h => h.2,fun hp => ⟨hCA i hp,hp⟩⟩)
  exact F.rebase_prepared h00 hc hκ hs hv (F.lift.target_pullback hBRV) hFPrepared W P hPA hW
    (fun i => by rw [hSelected i]; exact hP i)

end DiamondIntegral.Section6
