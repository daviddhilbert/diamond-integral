import «section 6».FusionResidualPoints

/-! The exact residual next-program source and protected families.
Actual full images, rather than only their RV images, define the context
on which the remaining-component induction applies. -/

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

theorem stage_preimage (z : R.stageTarget) : ∃ p : C,(R.stageMap p).val=z.val := by
  obtain ⟨a,ha⟩ := z.property
  obtain ⟨p,hp⟩ := a.property
  exact ⟨p,(congrArg DiamondIntegral.Section6.regularize hp).trans ha⟩

def residualTarget
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :=
  focusActive R.stageTarget (R.residualTags hCoeffMem)

def residualPiece
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) (i : Fin k) :=
  focusActive (R.stagePiece i) (R.residualTags hCoeffMem)

theorem residual_source (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    ∀ z ∈ (R.residualTarget hCoeffMem).carrier,
      selectedJointPoint (centripetalBaseLabels R.component π) (centripetalLocalLabels R.component σ) z ∈
        (unaryIndexedMixedFamily R.parameter ((CentripetalProgramTemplate.centripetal K).target A)).carrier := by
  intro z hz
  obtain ⟨p,hp⟩ := R.stage_preimage ⟨z,hz.1⟩
  change (R.stageMap p).val=z at hp
  have hRes : (R.stageMap p).val.2 ∈ (R.residualTags hCoeffMem).carrier := hp.symm ▸ hz.2
  exact hp ▸ (R.residual_point_data h00 hCoeffMem p hRes).1

theorem residual_piece_eq (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) (i : Fin k) :
    rvLabelPullback (R.residualTarget hCoeffMem)
      (Fin.addCases (centripetalBaseLabels R.component π) (centripetalLocalLabels R.component σ))
      (unaryIndexedMixedFamily R.parameter ((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i)))=
        R.residualPiece hCoeffMem i := by
  apply defSet_eq_of_carrier_eq
  ext z
  constructor
  · intro hz
    obtain ⟨hzR,hzPi⟩ := (mem_rvLabelPullback _ _ _ z).mp hz
    obtain ⟨p,hp⟩ := R.stage_preimage ⟨z,hzR.1⟩
    change (R.stageMap p).val=z at hp
    have hRes : (R.stageMap p).val.2 ∈ (R.residualTags hCoeffMem).carrier := hp.symm ▸ hzR.2
    have hNew : selectedJointPoint (centripetalBaseLabels R.component π)
        (centripetalLocalLabels R.component σ) (R.stageMap p).val ∈
          (unaryIndexedMixedFamily R.parameter ((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i))).carrier :=
      hp.symm ▸ hzPi
    have hpPi := ((R.residual_point_data h00 hCoeffMem p hRes).2 i).mp hNew
    exact ⟨⟨⟨p.val,hpPi⟩,hp⟩,hzR.2⟩
  · rintro ⟨⟨p,hp⟩,hTags⟩
    let a : C := ⟨p.val,R.sourcePiece_subset i p.property⟩
    change (R.stageMap a).val=z at hp
    have hRes : (R.stageMap a).val.2 ∈ (R.residualTags hCoeffMem).carrier := hp.symm ▸ hTags
    have hNew := ((R.residual_point_data h00 hCoeffMem a hRes).2 i).mpr p.property
    apply (mem_rvLabelPullback _ _ _ z).mpr
    exact ⟨⟨hp ▸ (R.stageMap a).property,hTags⟩,hp ▸ hNew⟩

def residualContext
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    SelectedProgramContext R.parameter ((CentripetalProgramTemplate.centripetal K).target A)
      (fun i => (CentripetalProgramTemplate.centripetal K).pieceTarget A (P i)) (R.residualTarget hCoeffMem)
      (centripetalBaseLabels R.component π) (centripetalLocalLabels R.component σ) := by
  refine ⟨focusActive_properInvariant _ (R.stageTarget_properInvariant h00 hc hκ hs hv) _,
    R.stageTarget_doublyBounded.mono (fun _ hp => hp.1),
    focusActive_rvPullback _ _ (R.stageTarget_rvPullback h00),R.residual_source h00 hCoeffMem,?_⟩
  intro i
  rw [R.residual_piece_eq h00 hCoeffMem i]
  apply focusActive_properInvariant
  exact (((R.stage_chain h00 hc hκ hs hv).atPiece i).literal_restriction h00
    (R.sourcePiece_subset i)).target_properInvariant h00 hc hκ hs hv

end DiamondIntegral.Section6.CentripetalFusionRepair
