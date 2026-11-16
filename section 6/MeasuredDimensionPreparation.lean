import «section 6».MeasuredHeadDimensionPreparation
import «section 6».UnaryMeasuredFormCompatibleExistence
import «section 6».BinaryMeasuredFibrePrograms

/-! Measured preparation in every positive VF dimension, with the full
form-compatible synchronized chain. The induction is uniform in the
original VF-generated base and adjoins only the actual head on fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_preparation_all_dimensions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (n : ℕ) :
    ∀ (S V : Set M), Cardinal.mk S < κ →
      NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M) →
      (∀ x ∈ V,iVF x) → V ⊆ S → S ⊆ algebraicClosureSet V →
      (∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) →
      ∀ k,MeasuredFormCompatiblePreparationInDimension (G := G) S n k := by
  induction n with
  | zero =>
    intro S V hsmall hΓ hV hVS hSV hnt k r H hH hD hRP P hPA hP ω hLevels
    let H' := (regularizeMap H).image
    let f := regularization H
    let P' (i : Fin k) := (f.restrict (hPA i)).image
    have hP'H' (i : Fin k) : (P' i).carrier ⊆ H'.carrier := by
      rintro p ⟨a,ha⟩
      exact ha ▸ (f ⟨a.val,hPA i a.property⟩).property
    have hPre : SynchronizedCentripetalChain (G := G) (Fin k) H H' f P :=
      .regularize H hH hD P hPA hP (fun i => hD.mono (hPA i))
    have hPhi : FormCompatibleSynchronizedChain (G := G) (Fin k) H H' f P ω :=
      .regularize H hH hD P hPA hP (fun i => hD.mono (hPA i)) ω
    have hH' : ProperInvariant S H'.carrier := regularization_properInvariant h00 hc hκ hs hv H hH hD
    have hD' : VFDoublyBounded H'.carrier := regularized_vfDoublyBounded hD
    have hRP' : IsRVPullback H'.carrier := regularization_rvPullback H hRP
    have hP' (i : Fin k) : ProperInvariant S (P' i).carrier :=
      ((hPre.atPiece i).literal_restriction h00 (hPA i)).target_properInvariant h00 hc hκ hs hv
    have hTag : ∀ p ∈ H'.carrier,∀ z ∈ H'.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
      rw [show H'.carrier=regularize '' H.carrier from regularization_carrier H]
      exact regularized_tagged H.carrier
    let Ω := SelectedProgramContext.regularizationGammaForm ω
    have hTransport : ∀ p : H,(Ω (f p)).val=(ω p).val :=
      SelectedProgramContext.regularizationGammaForm_transport ω
    have hΩLevels := hPre.toChain.toSpecial.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels Ω hTransport
    obtain ⟨T,hT⟩ := unary_measured_form_compatible_preparation_of_doublyBounded_tagged h00 hc linear hκ hs hv V
      hsmall hΓ hV hVS hSV hnt H' hH' hD' hRP' hTag P' hP'H' hP' Ω hΩLevels
    let F := T.coordinate
    have hF : FormCompatibleSynchronizedChain (G := G) (Fin k) H' F.target F.map P' Ω := hT
    let J := MeasuredCoordinatePreparation.precompose h00 P hPA f hPre.toChain.toSpecial
      (fun i => (hPre.atPiece i).literal_restriction h00 (hPA i)) hP'H' ω Ω hTransport F
    exact ⟨J,.comp P hPA hPhi Ω hTransport hF⟩
  | succ n ih =>
    intro S V hsmall hΓ hV hVS hSV hnt k r H hH hD hRP P hPA hP ω hLevels
    let H' := (regularizeMap H).image
    let f := regularization H
    let P' (i : Fin k) := (f.restrict (hPA i)).image
    have hP'H' (i : Fin k) : (P' i).carrier ⊆ H'.carrier := by
      rintro p ⟨a,ha⟩
      exact ha ▸ (f ⟨a.val,hPA i a.property⟩).property
    have hPre : SynchronizedCentripetalChain (G := G) (Fin k) H H' f P :=
      .regularize H hH hD P hPA hP (fun i => hD.mono (hPA i))
    have hPhi : FormCompatibleSynchronizedChain (G := G) (Fin k) H H' f P ω :=
      .regularize H hH hD P hPA hP (fun i => hD.mono (hPA i)) ω
    have hH' : ProperInvariant S H'.carrier := regularization_properInvariant h00 hc hκ hs hv H hH hD
    have hD' : VFDoublyBounded H'.carrier := regularized_vfDoublyBounded hD
    have hRP' : IsRVPullback H'.carrier := regularization_rvPullback H hRP
    have hP' (i : Fin k) : ProperInvariant S (P' i).carrier :=
      ((hPre.atPiece i).literal_restriction h00 (hPA i)).target_properInvariant h00 hc hκ hs hv
    have hTag : ∀ p ∈ H'.carrier,∀ z ∈ H'.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
      rw [show H'.carrier=regularize '' H.carrier from regularization_carrier H]
      exact regularized_tagged H.carrier
    let Ω := SelectedProgramContext.regularizationGammaForm ω
    have hTransport : ∀ p : H,(Ω (f p)).val=(ω p).val :=
      SelectedProgramContext.regularizationGammaForm_transport ω
    have hΩLevels := hPre.toChain.toSpecial.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels Ω hTransport
    have hLocal (a : VF M) :
        ∃ F : MeasuredCoordinatePreparation (G := G) ((headFibreTemplate H').fibre (fun _ => a.val))
          (fun i => (headFibreTemplate (P' i)).fibre (fun _ => a.val))
          (fun i => headFibreTemplate_subset (hP'H' i) a) (headGammaFormMap Ω a),
          FormCompatibleSynchronizedChain (G := G) (Fin k)
            ((headFibreTemplate H').fibre (fun _ => a.val)) F.target F.map
            (fun i => (headFibreTemplate (P' i)).fibre (fun _ => a.val)) (headGammaFormMap Ω a) := by
      let z : Fin 1 → M := fun _ => a.val
      obtain ⟨hV',hVS',hSV',hnt',hsmall',hΓ'⟩ := vf_preparation_support_adjoin_tuple
        hV hVS hSV hnt (le_of_lt hκ) hsmall hΓ z (fun _ => a.property)
      exact ih (S ∪ Set.range z) (V ∪ Set.range z) hsmall' hΓ' hV' hVS' hSV' hnt' k
        _ ((headFibreTemplate H').fibre z)
        (headFibreTemplate_properInvariant H' hH' a)
        (headFibreTemplate_doublyBounded H' hD' a)
        (headFibreTemplate_rvPullback H' hRP' a)
        (fun i => (headFibreTemplate (P' i)).fibre z)
        (fun i => headFibreTemplate_subset (hP'H' i) a)
        (fun i => headFibreTemplate_properInvariant (P' i) (hP' i) a)
        (headGammaFormMap Ω a) (headGammaFormMap_levels_open Ω a hΩLevels)
    obtain ⟨F,hF⟩ := measured_form_compatible_preparation_of_tagged_head_inputs h00 hc linear hκ hs hv V hsmall hΓ
      hV hVS hSV hnt (ih S V hsmall hΓ hV hVS hSV hnt k)
      H' hH' hD' hRP' hTag P' hP'H' hP' Ω hΩLevels hLocal
    let J := MeasuredCoordinatePreparation.precompose h00 P hPA f hPre.toChain.toSpecial
      (fun i => (hPre.atPiece i).literal_restriction h00 (hPA i)) hP'H' ω Ω hTransport F
    exact ⟨J,.comp P hPA hPhi Ω hTransport hF⟩

end DiamondIntegral.Section6
