import «section 6».PreparedBundleTransport

/-! Simultaneous preparation on actual full-set cylinders over a unary
base. Every map is constructed from the unary root algorithm; equal
carriers only transport its source metadata. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unary_cylinder_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (hARV : IsRVPullback A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier)
    (j : Fin r) (W : DefSet (rawMixedSpace (M := M) 2 r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ W.carrier)
    (hW : W.carrier = (rvCoordinateBundle A j).carrier)
    (hP : ∀ i, (P i).carrier = (rvCoordinateBundle (C i) j).carrier) :
    ∃ t : ℕ, ∃ Z : DefSet (rawMixedSpace (M := M) 2 t) S, ∃ g : Map W Z,
      SpecialCovariantChain (G := G) W Z g ∧ ProperInvariant S Z.carrier ∧
      VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
      (∀ p : W, (g p).val.1 (Fin.last 1) = p.val.1 (Fin.last 1)) ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image
        (g.restrict (hPA i)).toImage ∧ IsRVPullback (g.restrict (hPA i)).image.carrier := by
  let X := CarriedRefinementFrame.identity A j hA hD
  obtain ⟨s,B,f,F,hTarget,hPrepared⟩ := unary_preparation_carrying_coordinate
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hD hARV htag C hCA hC X
  have hSelected (i) : X.selectedPiece (C i) = C i := by
    apply defSet_eq_of_carrier_eq
    ext p
    rw [X.mem_selectedPiece]
    change (p ∈ A.carrier ∧ (p.1,p.2 ∘ id) ∈ (C i).carrier) ↔ p ∈ (C i).carrier
    simpa only [Function.comp_id,Prod.mk.eta] using
      (show (p ∈ A.carrier ∧ p ∈ (C i).carrier) ↔ p ∈ (C i).carrier from
        ⟨fun h => h.2,fun hp => ⟨hCA i hp,hp⟩⟩)
  exact F.rebase_prepared h00 hc hκ hs hv hTarget hPrepared W P hPA hW (fun i => by
    rw [hSelected i]
    exact hP i)

end DiamondIntegral.Section6
