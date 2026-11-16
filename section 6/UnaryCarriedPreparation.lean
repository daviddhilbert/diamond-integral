import «section 6».UnaryCompatiblePreparation

/-! A complete preparation construction on a retained-RV cylinder over
a unary source. One common actual special chain carries the extra VF
coordinate unchanged and prepares every protected cylinder, including
all regularization and branch labels. -/

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

theorem unary_preparation_carrying_coordinate
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
    (X : CarriedRefinementFrame A) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      ∃ F : SimultaneousCarriedLift (G := G) X f C,
        IsRVPullback F.lift.target.bundle.carrier ∧
        ∀ i, IsRVPullback (F.lift.map.restrict (X.selectedPiece_bundle_subset (C i))).image.carrier := by
  obtain ⟨s,B,f,hchain,hB,hBD,hBRV,hPieces⟩ := unary_compatible_preparation_of_doublyBounded_tagged
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hD hARV htag C hCA hC
  obtain ⟨F,hPrepared⟩ := hchain.carried_preparation_exists h00 hc hκ hs hv hCA
    (fun i => (hPieces i).2) X
  exact ⟨s,B,f,F,F.lift.target_pullback hBRV,hPrepared⟩

end DiamondIntegral.Section6
