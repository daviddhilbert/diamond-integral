import «section 6».PreparedLabelMeasuredPrograms
import «section 6».AllDimensionalOrderedContractions
import «section 6».MeasuredProperPreparation
import «section 6».MeasuredOrderedContractions

/-! Measured ordered existence in every positive VF dimension, for
arbitrary Gamma images with open fixed-label levels. The actual measured
preparation labels are retained through an original-source program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_ordered_program_all_dimensions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    Nonempty (MeasuredOrderedProgram (G := G) A ω) := by
  let C : Fin 0 → DefSet (rawMixedSpace (M := M) (n+1) r) S := Fin.elim0
  have hCA : ∀ i,(C i).carrier ⊆ A.carrier := fun i => i.elim0
  have hC : ∀ i,ProperInvariant S (C i).carrier := fun i => i.elim0
  obtain ⟨D⟩ := measured_proper_preparation h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hCA hC ω hLevels
  let τ := rvProjection D.map
  have hτ : ProperCovariant τ := ProperCovariant.rvProjection D.map
    (D.special.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ).covariant
  let B := (graftMap hc τ).image
  have hB : ProperInvariant S B.carrier := graft_properInvariant h00 hc hκ hs hv τ hA hτ
  have hBD : VFDoublyBounded B.carrier := by
    obtain ⟨δ,hδ⟩ := hAD
    refine ⟨δ,?_⟩
    rintro q ⟨p,rfl⟩ i
    exact hδ p.val p.property i
  obtain ⟨q,U,⟨T⟩⟩ := ordered_standard_program_all_dimensions h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    (n+1) _ B hB hBD
  exact ⟨measuredOrderedProgramOfPreparedLabels h00 hc linear hκ hs hv hsmall hΓ hA D T⟩

theorem measured_ordered_contraction_all_dimensions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    Nonempty (MeasuredOrderedContraction (G := G) A ω) := by
  obtain ⟨F⟩ := measured_ordered_program_all_dimensions h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD ω hLevels
  obtain ⟨L⟩ := exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ F.program hA
  exact ⟨⟨F,L⟩⟩

end DiamondIntegral.Section6
