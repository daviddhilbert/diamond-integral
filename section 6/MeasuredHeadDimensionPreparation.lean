import «section 6».FrozenMeasuredChoiceFusion
import «section 6».HeadPreparationContexts

/-! Tagged successor-dimension measured preparation uses actual head
fibre witnesses, complete frozen measured data, whole finite program
fusion and measured formula-choice assembly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_preparation_of_tagged_head_inputs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hIH : MeasuredFormCompatiblePreparationInDimension (G := G) S n k)
    (H : DefSet (rawMixedSpace (M := M) (n+2) r) S) (hH : ProperInvariant S H.carrier)
    (hD : VFDoublyBounded H.carrier) (hRP : IsRVPullback H.carrier)
    (hTag : ∀ p ∈ H.carrier,∀ z ∈ H.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ H.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : Map H (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ H.carrier ∧ gammaFormExtension ω (x,u)=γ})
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparation (G := G)
      ((headFibreTemplate H).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a) (headGammaFormMap ω a),
        FormCompatibleSynchronizedChain (G := G) (Fin k)
          ((headFibreTemplate H).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val)) (headGammaFormMap ω a)) :
    ∃ F : MeasuredCoordinatePreparation (G := G) H P hPA ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) H F.target F.map P ω := by
  let B := (vfHeadProjection H).image
  have hBRP := vfHeadProjection_rvPullback H hRP
  have hBD := vfHeadProjection_doublyBounded H hD
  have hB : ProperInvariant S B.carrier := doublyBounded_rvPullback_properInvariant h00 hc hκ hs hv B hBD
    (vfHeadProjection_rvBounded H hH.rvBounded) hBRP
  let X := headPreparationContext H hH hD hRP hTag
  let C : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S := Fin.elim0
  have hCB : ∀ i,(C i).carrier ⊆ B.carrier := fun i => i.elim0
  have hC : ∀ i,ProperInvariant S (C i).carrier := fun i => i.elim0
  obtain ⟨F⟩ := exists_frozen_measured_coordinate_program_data h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    B hB hBD hBRP (vfHeadProjection_tagged H hTag) C hCB hC X P hPA hP ω hLevels hLocal
  exact F.measured_preparation_of_frozen_coordinate_program_data h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    hIH hPA hLevels

end DiamondIntegral.Section6
