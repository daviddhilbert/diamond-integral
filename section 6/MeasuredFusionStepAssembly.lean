import «section 6».MeasuredVariableReleaseInduction
import «section 6».FormCompatibleFocusSteps
import «section 6».MeasuredComplementaryBranchPreparation
import «section 6».MeasuredPreparationSetTransport
import «section 6».FusionStepAssembly

/-! One full measured fusion step on the actual global source. The
retained core and variable old-aperture annulus use lower-dimensional
measured induction; the actual residual uses the remaining program.
Whole-label gluing retains the complete form-compatible permitted chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalFusionRepair
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 (n+1) s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 (n+1) s}
variable {A : MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {C : DefSet (rawMixedSpace (M := M) (n+2) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

def fusionGammaMap (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    Map R.stageTarget (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  ω.comp ((centripetalStepMap R.component).inverse (centripetalStepMap_bijective R.component h00))

def fusionResidualGammaMap (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    Map (R.residualTarget hCoeffMem) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (R.fusionGammaMap h00 ω).comp (Map.inclusion (fun _ hp => hp.1))

theorem fusionGammaMap_transport (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : C) :
    (R.fusionGammaMap h00 ω (R.stageMap p)).val=(ω p).val := by
  change (ω ((centripetalStepMap R.component).inverse _ (centripetalStepMap R.component p))).val=(ω p).val
  rw [Map.inverse_apply]

theorem assemble_measured_residual
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hIH : MeasuredFormCompatiblePreparationInDimension (G := G) S n k)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSafe : R.component.CoreFormConstant ω) (hOldSafe : R.component.VariableCoreFormConstant R.oldRadius ω)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ C.carrier ∧ gammaFormExtension ω (x,u)=γ})
    (FRes : MeasuredCoordinatePreparation (G := G) (R.residualTarget hCoeffMem)
      (R.residualPiece hCoeffMem) (R.residualPiece_subset hCoeffMem) (R.fusionResidualGammaMap h00 hCoeffMem ω))
    (hFRes : FormCompatibleSynchronizedChain (G := G) (Fin k) (R.residualTarget hCoeffMem) FRes.target FRes.map
      (R.residualPiece hCoeffMem) (R.fusionResidualGammaMap h00 hCoeffMem ω)) :
    ∃ F : MeasuredCoordinatePreparation (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _) ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) C F.target F.map
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  let W := R.stageTarget
  let Q := R.stagePiece
  let Ω := R.fusionGammaMap h00 ω
  have hW := R.stageTarget_properInvariant h00 hc hκ hs hv
  have hWD := R.stageTarget_doublyBounded
  have hWRP := R.stageTarget_rvPullback h00
  have hWTag := R.stageTarget_tagged
  have hQP (i) : ProperInvariant S (Q i).carrier :=
    (((R.stage_chain h00 hc hκ hs hv).atPiece i).literal_restriction h00
      (R.sourcePiece_subset i)).target_properInvariant h00 hc hκ hs hv
  obtain ⟨FCore,hFCore⟩ := measured_form_compatible_core_of_dimension_induction h00 hc linear hκ hs hv hsmall hΓ hIH
    R.component R.context.pullback R.sourcePiece R.protectedComponent R.protectedComponent_compatible ω hSafe hLevels
  have hQCore (i) : (focusActive (Q i) R.coreTags).carrier ⊆ (focusActive W R.coreTags).carrier :=
    fun _ hp => ⟨R.stagePiece_subset i hp.1,hp.2⟩
  obtain ⟨FC,hFC⟩ := FCore.transport_sets_form_compatible (hQC := hQCore) hFCore R.core_slice R.protected_core_slice
    (Ω.comp (Map.inclusion (fun _ hp => hp.1))) (fun _ => rfl)
  obtain ⟨FRelease,hFRelease⟩ := measured_form_compatible_variable_release_of_dimension_induction
    h00 hc linear hκ hs hv hsmall hΓ hIH R.component R.context.pullback (R.releaseTags hCoeffMem) R.oldRadius
    (R.old_aperture_release_data h00 hCoeffMem) R.sourcePiece R.protectedComponent R.protectedComponent_compatible
    (R.old_aperture_protected_stable hCoeffMem) ω hOldSafe hLevels
  let W₀ := focusActive W R.noncoreTags
  let Q₀ (i) := focusActive (Q i) R.noncoreTags
  have hQ₀ (i) : (Q₀ i).carrier ⊆ W₀.carrier := fun _ hp => ⟨R.stagePiece_subset i hp.1,hp.2⟩
  let Ω₀ := Ω.comp (Map.inclusion (fun p (hp : p ∈ W₀.carrier) => hp.1))
  have hQR (i) : (focusActive (Q₀ i) (R.releaseTags hCoeffMem)).carrier ⊆
      (focusActive W₀ (R.releaseTags hCoeffMem)).carrier := fun _ hp => ⟨hQ₀ i hp.1,hp.2⟩
  obtain ⟨FR,hFR⟩ := FRelease.transport_sets_form_compatible (hQC := hQR) hFRelease
    (R.release_nested_slice hCoeffMem W).symm
    (fun i => (R.protected_release_slice hCoeffMem i).trans (R.release_nested_slice hCoeffMem (Q i)).symm)
    (Ω₀.comp (Map.inclusion (fun _ hp => hp.1))) (fun _ => rfl)
  have hQS (i) : (focusActive (Q₀ i) (rvTagComplement (R.releaseTags hCoeffMem))).carrier ⊆
      (focusActive W₀ (rvTagComplement (R.releaseTags hCoeffMem))).carrier := fun _ hp => ⟨hQ₀ i hp.1,hp.2⟩
  obtain ⟨FS,hFS⟩ := FRes.transport_sets_form_compatible (hQC := hQS) hFRes
    (R.residual_nested_slice hCoeffMem W).symm
    (fun i => (R.residual_nested_slice hCoeffMem (Q i)).symm)
    (Ω₀.comp (Map.inclusion (fun _ hp => hp.1))) (fun _ => rfl)
  obtain ⟨FN,hFN⟩ := measured_form_compatible_preparation_glue_complementary_tags h00 hc hκ hs hv W₀
    (focusActive_properInvariant W hW R.noncoreTags) (hWD.mono (fun _ hp => hp.1))
    (focusActive_rvPullback W R.noncoreTags hWRP)
    (fun p hp z hz => hWTag p hp.1 z hz.1) Q₀ hQ₀
    (fun i => focusActive_properInvariant (Q i) (hQP i) R.noncoreTags) (R.releaseTags hCoeffMem) Ω₀ FR hFR FS hFS
  have hQN (i) : (focusActive (Q i) (rvTagComplement R.coreTags)).carrier ⊆
      (focusActive W (rvTagComplement R.coreTags)).carrier := fun _ hp => ⟨R.stagePiece_subset i hp.1,hp.2⟩
  obtain ⟨FN',hFN'⟩ := FN.transport_sets_form_compatible (hQC := hQN) hFN
    (R.noncore_complement_slice h00 W (Set.Subset.refl _)).symm
    (fun i => (R.noncore_complement_slice h00 (Q i) (R.stagePiece_subset i)).symm)
    (Ω.comp (Map.inclusion (fun _ hp => hp.1))) (fun _ => rfl)
  obtain ⟨FW,hFW⟩ := measured_form_compatible_preparation_glue_complementary_tags h00 hc hκ hs hv W hW hWD hWRP hWTag
    Q R.stagePiece_subset hQP R.coreTags Ω FC hFC FN' hFN'
  have hStage : FormCompatibleSynchronizedChain (G := G) (Fin k) C R.stageTarget R.stageMap R.sourcePiece ω :=
    form_compatible_centripetal_step h00 hc hκ hs hv R.component R.sourcePiece
      R.protectedComponent R.protectedComponent_compatible ω hSafe
  have hImages (i) : (R.stagePiece i).carrier ⊆ W.carrier := R.stagePiece_subset i
  let F := MeasuredCoordinatePreparation.precompose h00 R.sourcePiece R.sourcePiece_subset R.stageMap
    (R.stage_chain h00 hc hκ hs hv).toChain.toSpecial
    (fun i => ((R.stage_chain h00 hc hκ hs hv).atPiece i).literal_restriction h00 (R.sourcePiece_subset i))
    hImages ω Ω (R.fusionGammaMap_transport h00 ω) FW
  have hF : FormCompatibleSynchronizedChain (G := G) (Fin k) C F.target F.map R.sourcePiece ω :=
    .comp R.sourcePiece R.sourcePiece_subset hStage Ω (R.fusionGammaMap_transport h00 ω) hFW
  let F' : MeasuredCoordinatePreparation (G := G) C
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
      (fun i => rvLabelPullback_subset C _ _) ω := F.changePieces (fun i => (R.protectedEq i).symm)
  exact ⟨F',hF.changePieces (fun i => (R.protectedEq i).symm)⟩

end DiamondIntegral.Section6.CentripetalFusionRepair
