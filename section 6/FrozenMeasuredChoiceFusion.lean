import «section 6».FrozenMeasuredSourceForms
import «section 6».MeasuredFiniteTagPartitionPreparation

/-! Assemble every actual frozen program choice by measured finite
fusion, then retain the form-compatible preliminary unary lift as a
literal prefix on the original ambient and every protected piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FrozenMeasuredCoordinateProgramData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S)}

theorem measured_preparation_of_frozen_coordinate_program_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hIH : MeasuredFormCompatiblePreparationInDimension (G := G) S n l)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ X.source.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ J : MeasuredCoordinatePreparation (G := G) X.source P hPX ω,
      FormCompatibleSynchronizedChain (G := G) (Fin l) X.source J.target J.map P ω := by
  let E := F.forget h00
  let U := F.unary.lift
  let Ω := F.liftedGammaForm h00
  let Q (j) := (U.map.restrict (hPX j)).image
  have hQA (j) : (Q j).carrier ⊆ U.target.source.carrier := U.image_subset hPX j
  have hQProper (j) : ProperInvariant S (Q j).carrier :=
    ((U.chain.atPiece j).literal_restriction h00 (hPX j)).target_properInvariant h00 hc hκ hs hv
  have hGeometry := U.chain.toChain.toSpecial.gamma_levels_proper_geometry h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  have hChoicePrep (i : Fin F.programs.count) :
      ∃ J : MeasuredCoordinatePreparation (G := G) (focusActive U.target.source (E.choiceTags h00 U i))
        (fun j => focusActive (Q j) (E.choiceTags h00 U i)) (fun j _ hp => ⟨hQA j hp.1,hp.2⟩)
        (Ω.comp (Map.inclusion (fun _ hp => hp.1))),
        FormCompatibleSynchronizedChain (G := G) (Fin l) (focusActive U.target.source (E.choiceTags h00 U i))
          J.target J.map (fun j => focusActive (Q j) (E.choiceTags h00 U i))
          (Ω.comp (Map.inclusion (fun _ hp => hp.1))) := by
    obtain ⟨D,hDForms⟩ := F.exists_choice_uniform_measured_family h00 hc linear hκ hs hv hsmall hΓ hLevels i
    let Y := E.choiceProgramContext h00 hc hκ hs hv U hPX i
    let Ωi := Ω.comp (Map.inclusion (fun p
      (hp : p ∈ (focusActive U.target.source (E.choiceTags h00 U i)).carrier) => hp.1))
    have hSource (q : focusActive U.target.source (E.choiceTags h00 U i)) :
        gammaFormExtension (D.forms (Y.baseMap q)) (Fin.tail q.val.1,q.val.2 ∘ U.retainedLabels)=(Ωi q).val := by
      rw [hDForms]
      exact F.choice_source_form h00 hc hκ hs hv hPX i q
    have hLevelsI : ∀ u γ,IsOpen {x : Fin (n+2) → VF M |
        (x,u) ∈ (focusActive U.target.source (E.choiceTags h00 U i)).carrier ∧ gammaFormExtension Ωi (x,u)=γ} := by
      intro u γ
      have h := gammaFormRestriction_level_geometry (A := U.target.source)
        (C := focusActive U.target.source (E.choiceTags h00 U i)) (fun _ hp => hp.1) Y.proper.geometry Ω γ (hGeometry γ)
      exact (h.clopen_fibres hv u).isOpen
    obtain ⟨J,hJ⟩ := measured_form_compatible_preparation_of_uniform_program h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hIH
      (E.choiceDomain_properInvariant h00 i) (E.choiceDomain_rvPullback h00 i)
      (fun p hp z hz => F.unary.tagged p (E.choiceDomain_subset h00 i hp) z (E.choiceDomain_subset h00 i hz))
      (F.programs.programs i).2 (headFibreTemplate X.source) (fun j => headFibreTemplate (P j))
      (headGammaFormTemplate ω) _ _ _ D Y Ωi hSource hLevelsI
    exact ⟨J.changePieces (fun j => E.choiceProgramContext_piece_eq h00 hc hκ hs hv U hPX i j),
      hJ.changePieces (fun j => E.choiceProgramContext_piece_eq h00 hc hκ hs hv U hPX i j)⟩
  obtain ⟨T,hT⟩ := measured_form_compatible_preparation_of_finite_tag_partition h00 hc hκ hs hv F.programs.count
    U.target.source U.target.proper U.target.doublyBounded U.target.pullback U.target.tagged Q hQA hQProper (E.choiceTags h00 U)
    (fun p hp => E.choiceTags_cover h00 U ⟨p,hp⟩) (E.choiceTags_disjoint h00 U) Ω hChoicePrep
  let J := MeasuredCoordinatePreparation.precompose h00 P hPX U.map U.chain.toChain.toSpecial
    (fun j => (U.chain.atPiece j).literal_restriction h00 (hPX j)) hQA ω Ω (F.liftedGammaForm_transport h00) T
  exact ⟨J,.comp P hPX F.unary.formCompatible Ω (F.liftedGammaForm_transport h00) hT⟩

end DiamondIntegral.Section6.FrozenMeasuredCoordinateProgramData
