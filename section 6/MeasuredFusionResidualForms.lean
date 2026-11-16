import «section 6».MeasuredFusionRepairForms
import «section 6».UniformMeasuredPrefixValues
import «section 6».SelectedMeasuredTerminalPreparation

/-! The actual residual source retains the unary base and realizes the
old local component on its full selected point. Its actual inverse
transported form therefore agrees with the remaining measured family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}

namespace CentripetalFusionRepair
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

theorem residual_baseMap_at_preimage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (z : R.residualTarget hCoeffMem) (p : C) (hp : (R.stageMap p).val=z.val) :
    (R.residualContext h00 hc hκ hs hv hCoeffMem).baseMap z=R.context.baseMap p := by
  apply Subtype.ext
  rw [SelectedProgramContext.baseMap_value,SelectedProgramContext.baseMap_value,← hp,R.stageMap_value]
  exact centripetal_selected_base R.component K.coordinate R.coordinate π p.val

theorem residual_local_at_preimage
    (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (z : R.residualTarget hCoeffMem) (p : C) (hp : (R.stageMap p).val=z.val) :
    (Fin.tail z.val.1,z.val.2 ∘ centripetalLocalLabels R.component σ)=
      (R.fibreComponents.component (R.context.baseMap p)).point (Fin.tail p.val.1,p.val.2 ∘ σ) := by
  have hRes : (R.stageMap p).val.2 ∈ (R.residualTags hCoeffMem).carrier := hp.symm ▸ z.property.2
  have hOld := (R.residualTags_at h00 hCoeffMem p).mp hRes
  rw [← hp,R.stageMap_value]
  exact centripetal_selected_local_point R.component (R.fibreComponents.component (R.context.baseMap p)) σ p.val
    (R.coordinate.trans (congrArg Fin.succ (R.fibreComponents.coordinate _)).symm)
    (R.focus p) (R.coefficient _) hOld

end CentripetalFusionRepair

namespace MeasuredCentripetalFusionRepair
variable {H : CentripetalProgramTemplate (M := M) S 1 (n+1) (1+s) t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 (n+1) s}
variable {A : MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {W : GammaFormParameterTemplate (M := M) S 1 (n+1) s}
variable {C : DefSet (rawMixedSpace (M := M) (n+2) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable {ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable (R : MeasuredCentripetalFusionRepair (G := G) η ((CentripetalProgramTemplate.centripetal K).comp H) K A P W C π σ ω)

theorem residual_source_form
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈
      ((CentripetalProgramTemplate.centripetal K).comp H).rvTrace A P) :
    ∀ z : R.geometric.residualTarget hCoeffMem,
      gammaFormExtension ((R.family.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
        ((R.geometric.residualContext h00 hc hκ hs hv hCoeffMem).baseMap z))
        (Fin.tail z.val.1,z.val.2 ∘ centripetalLocalLabels R.geometric.component σ)=
          (R.geometric.fusionResidualGammaMap h00 hCoeffMem ω z).val := by
  intro z
  obtain ⟨p,hp⟩ := R.geometric.stage_preimage ⟨z.val,z.property.1⟩
  let b := R.geometric.context.baseMap p
  let x := R.geometric.localSourcePoint p
  let y : ((CentripetalProgramTemplate.centripetal K).target A).fibre
      (unaryFamilyParameter R.geometric.parameter b) :=
    ⟨(R.geometric.fibreComponents.component b).bijection x,by
      rw [R.geometric.fibreComponents.target_fibre]
      exact ((R.geometric.fibreComponents.component b).bijection x).property⟩
  have hValue := R.family.afterPrefix_value h00 hc linear hκ hs hv hsmall hΓ b
    (R.geometric.fibreComponents.component b).bijection
    ((R.geometric.fibreComponents.component b).bijective h00)
    (R.geometric.fibreComponents.component_transition_graph b) x y rfl
  have hLocal := R.geometric.residual_local_at_preimage h00 hCoeffMem z p hp
  have hLeft : gammaFormExtension ((R.family.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
        ((R.geometric.residualContext h00 hc hκ hs hv hCoeffMem).baseMap z))
      (Fin.tail z.val.1,z.val.2 ∘ centripetalLocalLabels R.geometric.component σ)=(ω p).val := by
    rw [R.geometric.residual_baseMap_at_preimage h00 hc hκ hs hv hCoeffMem z p hp,hLocal]
    exact (gammaFormExtension_at _ y).trans (hValue.trans
      ((gammaFormExtension_at (R.family.forms b) x).symm.trans (R.sourceForm p)))
  have hAt : (R.geometric.fusionResidualGammaMap h00 hCoeffMem ω z).val=(ω p).val := by
    change (R.geometric.fusionGammaMap h00 ω ⟨z.val,z.property.1⟩).val=(ω p).val
    have he : (⟨z.val,z.property.1⟩ : R.geometric.stageTarget)=R.geometric.stageMap p := Subtype.ext hp.symm
    rw [he]
    exact R.geometric.fusionGammaMap_transport h00 ω p
  exact hLeft.trans hAt.symm

end MeasuredCentripetalFusionRepair
end DiamondIntegral.Section6
