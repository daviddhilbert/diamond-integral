import «section 6».FusionActualStages

/-! On the exact residual branch, the global step realizes the
first local program component, with unchanged unary base and literal
membership in every next protected fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
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

theorem residual_point_data (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (p : C) (hRes : (R.stageMap p).val.2 ∈ (R.residualTags hCoeffMem).carrier) :
    selectedJointPoint (centripetalBaseLabels R.component π) (centripetalLocalLabels R.component σ)
      (R.stageMap p).val ∈
        (unaryIndexedMixedFamily R.parameter ((CentripetalProgramTemplate.centripetal K).target A)).carrier ∧
    ∀ i,selectedJointPoint (centripetalBaseLabels R.component π) (centripetalLocalLabels R.component σ)
      (R.stageMap p).val ∈
        (unaryIndexedMixedFamily R.parameter ((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i))).carrier ↔
          p.val ∈ (R.sourcePiece i).carrier := by
  let b := R.context.baseMap p
  have hbOld : unaryFamilyBasePoint (selectedJointPoint π σ p.val)=b.val :=
    (selectedJointPoint_base π σ p.val).trans (R.context.baseMap_value p).symm
  have hpA := (mem_unaryIndexedMixedFamily_at R.parameter A _ b hbOld).mp (R.context.source p.val p.property)
  rw [selectedJointPoint_local] at hpA
  change (Fin.tail p.val.1,p.val.2 ∘ σ) ∈ (A.fibre (unaryFamilyParameter R.parameter b)).carrier at hpA
  have hOld := (R.residualTags_at h00 hCoeffMem p).mp hRes
  have hPoint := centripetal_selected_local_point R.component (R.fibreComponents.component b) σ p.val
    (R.coordinate.trans (congrArg Fin.succ (R.fibreComponents.coordinate b)).symm)
    (R.focus p) (R.coefficient b) hOld
  let z := selectedJointPoint (centripetalBaseLabels R.component π) (centripetalLocalLabels R.component σ)
    (R.stageMap p).val
  have hb : unaryFamilyBasePoint z=b.val :=
    (selectedJointPoint_base _ _ _).trans
      ((centripetal_selected_base R.component K.coordinate R.coordinate π p.val).trans
        (R.context.baseMap_value p).symm)
  have hLocal : (Fin.tail z.1,z.2 ∘ Fin.natAdd r)=
      (R.fibreComponents.component b).point (Fin.tail p.val.1,p.val.2 ∘ σ) := by
    change (Fin.tail (selectedJointPoint _ _ (R.stageMap p).val).1,
      (selectedJointPoint _ _ (R.stageMap p).val).2 ∘ Fin.natAdd r)=_
    rw [selectedJointPoint_local]
    exact hPoint
  constructor
  · change z ∈ (unaryIndexedMixedFamily R.parameter ((CentripetalProgramTemplate.centripetal K).target A)).carrier
    rw [mem_unaryIndexedMixedFamily_at R.parameter _ z b hb,hLocal,R.fibreComponents.target_fibre b]
    exact ⟨⟨(Fin.tail p.val.1,p.val.2 ∘ σ),hpA⟩,rfl⟩
  · intro i
    change (z ∈ (unaryIndexedMixedFamily R.parameter
      ((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i))).carrier) ↔ _
    rw [mem_unaryIndexedMixedFamily_at R.parameter _ z b hb,hLocal,
      R.fibreComponents.pieceTarget_mem_iff h00 b i ((R.family.geometry b).subset i)
        (Fin.tail p.val.1,p.val.2 ∘ σ) hpA]
    change (Fin.tail p.val.1,p.val.2 ∘ σ) ∈ ((P i).fibre (unaryFamilyParameter R.parameter b)).carrier ↔
      p.val ∈ (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily R.parameter (P i))).carrier
    rw [mem_rvLabelPullback]
    change (Fin.tail p.val.1,p.val.2 ∘ σ) ∈ ((P i).fibre (unaryFamilyParameter R.parameter b)).carrier ↔
      (p.val ∈ C.carrier ∧ selectedJointPoint π σ p.val ∈ (unaryIndexedMixedFamily R.parameter (P i)).carrier)
    rw [mem_unaryIndexedMixedFamily_at R.parameter (P i)
      (selectedJointPoint π σ p.val) b hbOld,selectedJointPoint_local]
    exact (and_iff_right p.property).symm

end DiamondIntegral.Section6.CentripetalFusionRepair
