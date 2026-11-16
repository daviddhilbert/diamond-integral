import «section 6».FusionBranchSlices
import «section 6».FusionProjectedBranches

/-! One complete global fusion step: lower-dimensional preparation
handles the core and released annulus, remaining-program preparation
handles the residual, and literal branch chains prepare the whole source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalFusionRepair
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

theorem residualPiece_subset
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) (i : Fin k) :
    (R.residualPiece hCoeffMem i).carrier ⊆ (R.residualTarget hCoeffMem).carrier :=
  fun _ hp => ⟨R.stagePiece_subset i hp.1,hp.2⟩

theorem assemble_prepared_residual
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hIH : SynchronizedPreparationInDimension (G := G) S n k)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (FRes : PreparedSynchronizedFamily (G := G) (R.residualTarget hCoeffMem)
      (R.residualPiece hCoeffMem) (R.residualPiece_subset hCoeffMem)) :
    Nonempty (PreparedSynchronizedFamily (G := G) C
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
      (fun i => rvLabelPullback_subset C _ _)) := by
  let W := R.stageTarget
  let Q := R.stagePiece
  have hW := R.stageTarget_properInvariant h00 hc hκ hs hv
  have hWD := R.stageTarget_doublyBounded
  have hWRP := R.stageTarget_rvPullback h00
  have hWTag := R.stageTarget_tagged
  have hQP (i) : ProperInvariant S (Q i).carrier :=
    (((R.stage_chain h00 hc hκ hs hv).atPiece i).literal_restriction h00
      (R.sourcePiece_subset i)).target_properInvariant h00 hc hκ hs hv
  obtain ⟨FCore⟩ := R.prepared_core_of_dimension_induction h00 hc hκ hs hv hIH
  let FC : PreparedSynchronizedFamily (G := G) (focusActive W R.coreTags)
      (fun i => focusActive (Q i) R.coreTags) (fun i _ hp => ⟨R.stagePiece_subset i hp.1,hp.2⟩) :=
    FCore.transportSets R.core_slice R.protected_core_slice
  obtain ⟨FRelease⟩ := R.prepared_release_of_dimension_induction h00 hc hκ hs hv hIH hCoeffMem
  let W₀ := focusActive W R.noncoreTags
  let Q₀ (i) := focusActive (Q i) R.noncoreTags
  have hQ₀ (i) : (Q₀ i).carrier ⊆ W₀.carrier := fun _ hp => ⟨R.stagePiece_subset i hp.1,hp.2⟩
  let FR : PreparedSynchronizedFamily (G := G) (focusActive W₀ (R.releaseTags hCoeffMem))
      (fun i => focusActive (Q₀ i) (R.releaseTags hCoeffMem)) (fun i _ hp => ⟨hQ₀ i hp.1,hp.2⟩) :=
    FRelease.transportSets (R.release_nested_slice hCoeffMem W).symm
      (fun i => (R.protected_release_slice hCoeffMem i).trans (R.release_nested_slice hCoeffMem (Q i)).symm)
  let FS : PreparedSynchronizedFamily (G := G) (focusActive W₀ (rvTagComplement (R.releaseTags hCoeffMem)))
      (fun i => focusActive (Q₀ i) (rvTagComplement (R.releaseTags hCoeffMem)))
      (fun i _ hp => ⟨hQ₀ i hp.1,hp.2⟩) :=
    FRes.transportSets (R.residual_nested_slice hCoeffMem W).symm
      (fun i => (R.residual_nested_slice hCoeffMem (Q i)).symm)
  obtain ⟨FN⟩ := synchronized_preparation_glue_complementary_tags h00 hc hκ hs hv W₀
    (focusActive_properInvariant W hW R.noncoreTags) (hWD.mono (fun _ hp => hp.1))
    (focusActive_rvPullback W R.noncoreTags hWRP)
    (fun p hp z hz => hWTag p hp.1 z hz.1) Q₀ hQ₀
    (fun i => focusActive_properInvariant (Q i) (hQP i) R.noncoreTags) (R.releaseTags hCoeffMem) FR FS
  let FN' : PreparedSynchronizedFamily (G := G) (focusActive W (rvTagComplement R.coreTags))
      (fun i => focusActive (Q i) (rvTagComplement R.coreTags))
      (fun i _ hp => ⟨R.stagePiece_subset i hp.1,hp.2⟩) :=
    FN.transportSets (R.noncore_complement_slice h00 W (Set.Subset.refl _)).symm
      (fun i => (R.noncore_complement_slice h00 (Q i) (R.stagePiece_subset i)).symm)
  obtain ⟨FW⟩ := synchronized_preparation_glue_complementary_tags h00 hc hκ hs hv W hW hWD hWRP hWTag
    Q R.stagePiece_subset hQP R.coreTags FC FN'
  let F := FW.precompose R.sourcePiece_subset (R.stage_chain h00 hc hκ hs hv)
  exact ⟨F.changePieces (fun i => (R.protectedEq i).symm)⟩

end DiamondIntegral.Section6.CentripetalFusionRepair
