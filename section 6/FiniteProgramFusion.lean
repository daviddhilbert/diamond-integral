import «section 6».SelectedProgramPrefixes
import «section 6».FusionStepAssembly

/-! Finite fusion of an actual uniform program family. Structural
induction removes one local primitive at a time; the only dimensional
induction input is preparation of the actual projected replacement sets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem synchronized_preparation_of_uniform_sequence
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hIH : SynchronizedPreparationInDimension (G := G) S n k)
    {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (hB : ProperInvariant S B.carrier) (hBRP : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (L : CentripetalProgramSequence (M := M) S 1 n s t) :
    ∀ {q : ℕ} {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
      (A : MixedSetParameterTemplate (M := M) S 1 n s)
      (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
      (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q),
      UniformProgramFamily η L.toProgram A P → SelectedProgramContext η A P C π σ →
      Nonempty (PreparedSynchronizedFamily (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _)) := by
  induction L with
  | single F =>
    intro q η A P C π σ U X
    cases F with
    | identity => exact ⟨X.terminal hBRP U⟩
    | regularize =>
      have hPA := fun b => (U.geometry b).subset
      let X' := X.afterRegularization h00 hc hκ hs hv hPA
      let F := X'.finish (G := G) hBRP U.prepared_target_fibres
        (fun i => U.rows _ ((CentripetalProgramTemplate.regularize _).terminal_piece_data_mem A P i))
      exact ⟨X.precomposeRegularization h00 hc hκ hs hv hPA F⟩
    | centripetal K =>
      have hGood := fun b => (U.prepared b).1
      have hCoeffMem := K.coefficient_data_mem A P
      obtain ⟨R⟩ := exists_centripetal_fusion_repair h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
        hB hBRP hBTag U X hGood (K.active_data_mem A P) hCoeffMem
      let Y := R.residualContext h00 hc hκ hs hv hCoeffMem
      let F := Y.finish (G := G) hBRP R.family.prepared_target_fibres
        (fun i => R.family.rows _ ((CentripetalProgramTemplate.centripetal K).terminal_piece_data_mem A P i))
      let FRes : PreparedSynchronizedFamily (G := G) (R.residualTarget hCoeffMem)
          (R.residualPiece hCoeffMem) (R.residualPiece_subset hCoeffMem) :=
        F.changePieces (fun i => R.residual_piece_eq h00 hCoeffMem i)
      exact R.assemble_prepared_residual h00 hc hκ hs hv hIH hCoeffMem FRes
  | cons F H ih =>
    intro q η A P C π σ U X
    cases F with
    | identity =>
      have hPA := fun b => (U.geometry b).subset
      let U' := U.afterPrefix (G := G) h00 hc hκ hs hv
      let X' := X.afterIdentity hPA
      obtain ⟨F⟩ := ih _ _ C π σ U' X'
      exact ⟨F.changePieces (fun i => identity_selected_piece_eq hPA i)⟩
    | regularize =>
      have hPA := fun b => (U.geometry b).subset
      let U' := U.afterPrefix (G := G) h00 hc hκ hs hv
      let X' := X.afterRegularization h00 hc hκ hs hv hPA
      obtain ⟨F⟩ := ih _ _ (regularizeMap C).image (regularizedBaseLabels π) (regularizedTailLabels σ) U' X'
      exact ⟨X.precomposeRegularization h00 hc hκ hs hv hPA F⟩
    | centripetal K =>
      have hGood := fun b => (U.prepared b).1.1
      have hActiveMem : (⟨n+_,leadingRVImageTemplate (focusActiveParameterTemplate A K.active)⟩ : RVDataTemplate S 1) ∈
          ((CentripetalProgramTemplate.centripetal K).comp H.toProgram).rvTrace A P := by
        exact List.mem_append.mpr (Or.inl (K.active_data_mem A P))
      have hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈
          ((CentripetalProgramTemplate.centripetal K).comp H.toProgram).rvTrace A P :=
        List.mem_append.mpr (Or.inl (K.coefficient_data_mem A P))
      obtain ⟨R⟩ := exists_centripetal_fusion_repair h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
        hB hBRP hBTag U X hGood hActiveMem hCoeffMem
      let U' := R.family.afterPrefix (G := G) h00 hc hκ hs hv
      let Y := R.residualContext h00 hc hκ hs hv hCoeffMem
      obtain ⟨F⟩ := ih _ _ (R.residualTarget hCoeffMem)
        (centripetalBaseLabels R.component π) (centripetalLocalLabels R.component σ) U' Y
      let FRes : PreparedSynchronizedFamily (G := G) (R.residualTarget hCoeffMem)
          (R.residualPiece hCoeffMem) (R.residualPiece_subset hCoeffMem) :=
        F.changePieces (fun i => R.residual_piece_eq h00 hCoeffMem i)
      exact R.assemble_prepared_residual h00 hc hκ hs hv hIH hCoeffMem FRes

end DiamondIntegral.Section6
