import «section 6».FusionOldApertureMaps

/-! Actual old-aperture invariance on the repaired source and every
protected set constructs the whole-label released annulus. No single
globally named old coefficient is assumed. -/

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

theorem old_aperture_protected_stable
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (i : Fin k) :
    ∀ p ∈ (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily R.parameter (P i))).carrier,
      p.2 ∈ R.component.activeTags.carrier → ∀ x : VF M,
        (R.oldRadius p.2).val < vfValue (p.1 R.component.coordinate-x) →
          (Function.update p.1 R.component.coordinate x,p.2) ∈
            (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily R.parameter (P i))).carrier := by
  rw [R.coordinate]
  apply selected_coordinate_stable_of_fibre_components R.parameter A (P i) C π σ R.context.pullback
    K.coordinate R.component.activeTags.carrier R.oldRadius
  intro p hp hu
  obtain ⟨hpC,hpPi⟩ := (mem_rvLabelPullback C _ _ p).mp hp
  let a : C := ⟨p,hpC⟩
  let b := R.context.baseMap a
  have hb : selectedUnaryBasePoint π p=b.val := (R.context.baseMap_value a).symm
  have hpLocal := (mem_unaryIndexedMixedFamily_at R.parameter (P i) (selectedJointPoint π σ p)
    b ((selectedJointPoint_base π σ p).trans hb)).mp hpPi
  rw [selectedJointPoint_local] at hpLocal
  change (Fin.tail p.1,p.2 ∘ σ) ∈ ((P i).fibre (unaryFamilyParameter R.parameter b)).carrier at hpLocal
  obtain ⟨E,hE⟩ := R.fibreComponents.restrictions b i
  refine ⟨b,hb,R.fibreComponents.component b,E,R.fibreComponents.coordinate b,hE,(R.active a).mp hu,?_⟩
  have h := R.oldRadius_value hCoeffMem ⟨p,hpC,hu⟩
  have hEq := congrArg₂ (fun x y : VF M => x*y) hE.coefficient
    (hE.focus (Fin.tail p.1,p.2 ∘ σ) hpLocal)
  exact h.trans (congrArg vfValue hEq).symm

theorem old_aperture_source_stable
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    ∀ p ∈ C.carrier,p.2 ∈ R.component.activeTags.carrier → ∀ x : VF M,
      (R.oldRadius p.2).val < vfValue (p.1 R.component.coordinate-x) →
        (Function.update p.1 R.component.coordinate x,p.2) ∈ C.carrier := by
  have hSelf : rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily R.parameter A)=C := by
    apply defSet_eq_of_carrier_eq
    ext p
    rw [mem_rvLabelPullback]
    exact ⟨And.left,fun hp => ⟨hp,R.context.source p hp⟩⟩
  have hStable := selected_coordinate_stable_of_fibre_components R.parameter A A C π σ R.context.pullback
    K.coordinate R.component.activeTags.carrier R.oldRadius (by
      intro p hp hu
      have hpC := ((mem_rvLabelPullback C _ _ p).mp hp).1
      let a : C := ⟨p,hpC⟩
      let b := R.context.baseMap a
      refine ⟨b,(R.context.baseMap_value a).symm,R.fibreComponents.component b,R.fibreComponents.component b,
        R.fibreComponents.coordinate b,⟨Set.Subset.refl _,rfl,rfl,fun _ _ => rfl⟩,(R.active a).mp hu,?_⟩
      exact R.oldRadius_value hCoeffMem ⟨p,hpC,hu⟩)
  rw [hSelf] at hStable
  simpa only [R.coordinate] using hStable

def old_aperture_release_data (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    VariableApertureReleaseData R.component
      (R.component.variableReleaseTags R.oldApertureMap (R.oldApertureMap_constant hCoeffMem)) R.oldRadius :=
  R.component.variableReleaseData_of_gamma_graph h00 R.oldApertureMap
    (R.oldApertureMap_constant hCoeffMem) (R.old_aperture_source_stable hCoeffMem)

end DiamondIntegral.Section6.CentripetalFusionRepair
