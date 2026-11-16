import «section 6».MeasuredSelectedRegularizationAssembly
import «section 6».MeasuredFusionTerminalResidual

/-! Full finite measured program fusion. The induction constructs actual
source forms and their open levels at every remaining program, derives
both aperture form conditions from guarded local components, and retains
the actual form-compatible global chain and all protected images. -/

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

theorem measured_form_compatible_preparation_of_uniform_sequence
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
    (L : CentripetalProgramSequence (M := M) S 1 (n+1) s t) :
    ∀ {q : ℕ} {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
      (A : MixedSetParameterTemplate (M := M) S 1 (n+1) s)
      (P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s)
      (W : GammaFormParameterTemplate (M := M) S 1 (n+1) s)
      (C : DefSet (rawMixedSpace (M := M) (n+2) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q),
      (U : UniformMeasuredProgramFamily (G := G) η L.toProgram A P W) →
      (X : SelectedProgramContext η A P C π σ) →
      (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)) →
      (∀ p : C,gammaFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) →
      (∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ C.carrier ∧ gammaFormExtension ω (x,u)=γ}) →
      ∃ F : MeasuredCoordinatePreparation (G := G) C
          (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
          (fun i => rvLabelPullback_subset C _ _) ω,
        FormCompatibleSynchronizedChain (G := G) (Fin k) C F.target F.map
          (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  induction L with
  | single F =>
    intro q η A P W C π σ U X ω hSource hLevels
    cases F with
    | identity => exact X.measured_identity_terminal h00 hc hκ hs hv hBRP U ω hSource
    | regularize => exact X.measured_regularization_terminal h00 hc hκ hs hv hBRP U ω hSource
    | centripetal K =>
      have hGood := fun b => (U.prepared b).1
      have hCoeffMem := K.coefficient_data_mem A P
      obtain ⟨R⟩ := exists_measured_centripetal_fusion_repair h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
        hB hBRP hBTag U X hGood (K.active_data_mem A P) hCoeffMem ω hSource hLevels (fun b => (U.admissible b).2)
      obtain ⟨FRes,hFRes⟩ := R.terminal_residual_preparation h00 hc hκ hs hv hBRP hCoeffMem
      exact R.geometric.assemble_measured_residual h00 hc linear hκ hs hv hsmall hΓ hIH hCoeffMem ω
        (R.core_form_constant h00 hCoeffMem) (R.variable_core_form_constant h00 hCoeffMem) hLevels FRes hFRes
  | cons F H ih =>
    intro q η A P W C π σ U X ω hSource hLevels
    cases F with
    | identity =>
      have hPA := fun b => (U.geometry b).subset
      let U' := U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ
      let X' := X.afterIdentity hPA
      obtain ⟨J,hJ⟩ := ih _ _ _ C π σ U' X' ω
        (X.afterIdentity_source_form h00 hc linear hκ hs hv hsmall hΓ U ω hSource) hLevels
      exact ⟨J.changePieces (fun i => identity_selected_piece_eq hPA i),
        hJ.changePieces (fun i => identity_selected_piece_eq hPA i)⟩
    | regularize =>
      have hPA := fun b => (U.geometry b).subset
      let U' := U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ
      let X' := X.afterRegularization h00 hc hκ hs hv hPA
      let Ω := SelectedProgramContext.regularizationGammaForm ω
      have hReg : SpecialCovariantChain (G := G) C (regularizeMap C).image (regularization C) :=
        .regularize C X.proper X.doublyBounded
      have hΩLevels := hReg.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels Ω
        (SelectedProgramContext.regularizationGammaForm_transport ω)
      obtain ⟨J,hJ⟩ := ih _ _ _ (regularizeMap C).image (regularizedBaseLabels π) (regularizedTailLabels σ)
        U' X' Ω (X.afterRegularization_source_form h00 hc linear hκ hs hv hsmall hΓ U ω hSource) hΩLevels
      exact X.precompose_measured_regularization h00 hPA ω J hJ
    | centripetal K =>
      have hGood := fun b => (U.prepared b).1.1
      have hActiveMem : (⟨(n+1)+_,leadingRVImageTemplate (focusActiveParameterTemplate A K.active)⟩ : RVDataTemplate S 1) ∈
          ((CentripetalProgramTemplate.centripetal K).comp H.toProgram).rvTrace A P :=
        List.mem_append.mpr (Or.inl (K.active_data_mem A P))
      have hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈
          ((CentripetalProgramTemplate.centripetal K).comp H.toProgram).rvTrace A P :=
        List.mem_append.mpr (Or.inl (K.coefficient_data_mem A P))
      have hCore (b : B) := ((Set.ext_iff.mp
        ((CentripetalProgramTemplate.centripetal K).measuredFormGood_comp H.toProgram A P W) _).mp (U.admissible b)).1.2
      obtain ⟨R⟩ := exists_measured_centripetal_fusion_repair h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
        hB hBRP hBTag U X hGood hActiveMem hCoeffMem ω hSource hLevels hCore
      let U' := R.family.afterPrefix h00 hc linear hκ hs hv hsmall hΓ
      let Y := R.geometric.residualContext h00 hc hκ hs hv hCoeffMem
      let Ω := R.geometric.fusionResidualGammaMap h00 hCoeffMem ω
      obtain ⟨J,hJ⟩ := ih _ _ _ (R.geometric.residualTarget hCoeffMem)
        (centripetalBaseLabels R.geometric.component π) (centripetalLocalLabels R.geometric.component σ) U' Y Ω
        (R.residual_source_form h00 hc linear hκ hs hv hsmall hΓ hCoeffMem)
        (R.geometric.fusionResidualGammaMap_levels_open h00 hc linear hκ hs hv hsmall hΓ hCoeffMem ω hLevels)
      let FRes : MeasuredCoordinatePreparation (G := G) (R.geometric.residualTarget hCoeffMem)
          (R.geometric.residualPiece hCoeffMem) (R.geometric.residualPiece_subset hCoeffMem) Ω :=
        J.changePieces (fun i => R.geometric.residual_piece_eq h00 hCoeffMem i)
      have hFRes : FormCompatibleSynchronizedChain (G := G) (Fin k) (R.geometric.residualTarget hCoeffMem)
          FRes.target FRes.map (R.geometric.residualPiece hCoeffMem) Ω :=
        hJ.changePieces (fun i => R.geometric.residual_piece_eq h00 hCoeffMem i)
      exact R.geometric.assemble_measured_residual h00 hc linear hκ hs hv hsmall hΓ hIH hCoeffMem ω
        (R.core_form_constant h00 hCoeffMem) (R.variable_core_form_constant h00 hCoeffMem) hLevels FRes hFRes

end DiamondIntegral.Section6
