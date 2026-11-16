import «section 6».MeasuredFiniteProgramFusion

/-! Arbitrary finite measured program trees normalize with all form
guards and complete Gamma traces, then use the actual sequential fusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_preparation_of_uniform_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hIH : MeasuredFormCompatiblePreparationInDimension (G := G) S n k)
    {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (hB : ProperInvariant S B.carrier) (hBRP : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (T : CentripetalProgramTemplate (M := M) S 1 (n+1) s t) :
    ∀ {q : ℕ} {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
      (A : MixedSetParameterTemplate (M := M) S 1 (n+1) s)
      (P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s)
      (W : GammaFormParameterTemplate (M := M) S 1 (n+1) s)
      (C : DefSet (rawMixedSpace (M := M) (n+2) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q),
      (U : UniformMeasuredProgramFamily (G := G) η T A P W) →
      (X : SelectedProgramContext η A P C π σ) →
      (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)) →
      (∀ p : C,gammaFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) →
      (∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ C.carrier ∧ gammaFormExtension ω (x,u)=γ}) →
      ∃ F : MeasuredCoordinatePreparation (G := G) C
          (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
          (fun i => rvLabelPullback_subset C _ _) ω,
        FormCompatibleSynchronizedChain (G := G) (Fin k) C F.target F.map
          (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  intro q η A P W C π σ U X ω hSource hLevels
  exact measured_form_compatible_preparation_of_uniform_sequence h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hIH
    hB hBRP hBTag T.toSequence A P W C π σ U.sequential X ω hSource hLevels

end DiamondIntegral.Section6
