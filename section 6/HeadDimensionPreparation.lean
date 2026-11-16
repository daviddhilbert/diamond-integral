import «section 6».HeadPreparationContexts

/-! The tagged successor-dimension preparation theorem is assembled
from the actual head-fibre induction witnesses, frozen coordinate data,
unary lift, formula choices and complete finite-program fusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem synchronized_preparation_of_tagged_head_inputs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hIH : SynchronizedPreparationInDimension (G := G) S n k)
    (H : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hH : ProperInvariant S H.carrier)
    (hD : VFDoublyBounded H.carrier) (hRP : IsRVPullback H.carrier)
    (hTag : ∀ p ∈ H.carrier,∀ z ∈ H.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ H.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (hLocal : ∀ a : VF M,Nonempty (PreparedSynchronizedFamily (G := G)
      ((headFibreTemplate H).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a))) :
    Nonempty (PreparedSynchronizedFamily (G := G) H P hPA) := by
  let B := (vfHeadProjection H).image
  have hBRP := vfHeadProjection_rvPullback H hRP
  have hBD := vfHeadProjection_doublyBounded H hD
  have hB : ProperInvariant S B.carrier := doublyBounded_rvPullback_properInvariant h00 hc hκ hs hv B hBD
    (vfHeadProjection_rvBounded H hH.rvBounded) hBRP
  let X := headPreparationContext H hH hD hRP hTag
  let C : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S := Fin.elim0
  have hCB : ∀ i,(C i).carrier ⊆ B.carrier := fun i => i.elim0
  have hC : ∀ i,ProperInvariant S (C i).carrier := fun i => i.elim0
  obtain ⟨F⟩ := exists_frozen_coordinate_program_data h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    B hB hBD hBRP (vfHeadProjection_tagged H hTag) C hCB hC X P hPA hP hLocal
  obtain ⟨U⟩ := F.unary.lift
  exact F.prepared_of_frozen_coordinate_program_data h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hIH U hPA

end DiamondIntegral.Section6
