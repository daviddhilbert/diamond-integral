import «section 6».CentripetalFusionRepairs
import «section 6».SelectedCoordinateStability
import «section 6».VariableReleaseTags

/-! The old aperture of an actual fusion repair is a complete
original-base Gamma graph, constant on each retained-label fibre.
Its value is the aperture of the actual old local component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
namespace CentripetalFusionRepair
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

def oldCoefficientMap : Map (focusActive C R.component.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (unaryCoefficientMap K.coefficient R.parameter (fun b => (R.admissible b).1.1.2)).comp
    (R.context.baseMap.comp (Map.inclusion (fun _ hp => hp.1)))

theorem oldCoefficientMap_value (p : focusActive C R.component.activeTags) :
    (R.oldCoefficientMap p).val 0=
      (R.fibreComponents.component (R.context.baseMap ⟨p.val,p.property.1⟩)).coefficient :=
  R.fibreComponents.coefficient_map _

theorem oldCoefficientMap_nonzero (p : focusActive C R.component.activeTags) :
    (R.oldCoefficientMap p).val 0 ≠ 0 := by
  rw [R.oldCoefficientMap_value]
  exact (R.fibreComponents.component _).coefficient_nonzero

variable (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)

include hCoeffMem in
theorem oldCoefficientMap_rv_constant (p z : focusActive C R.component.activeTags)
    (hTags : p.val.2=z.val.2) : rv M ((R.oldCoefficientMap p).val 0)=rv M ((R.oldCoefficientMap z).val 0) := by
  apply unaryCoefficientMap_rv_constant K.coefficient R.parameter (fun b => (R.admissible b).1.1.2)
    (R.family.rows _ hCoeffMem)
  exact R.context.baseMap_labels ⟨p.val,p.property.1⟩ ⟨z.val,z.property.1⟩ hTags

def oldApertureMap := R.component.fullFocusGraph.variableCutoffMap R.oldCoefficientMap

include hCoeffMem in
theorem oldApertureMap_constant (p z : focusActive C R.component.activeTags) (hTags : p.val.2=z.val.2) :
    (R.oldApertureMap p).val=(R.oldApertureMap z).val :=
  R.component.fullFocusGraph.variableCutoffMap_constant R.oldCoefficientMap R.oldCoefficientMap_nonzero
    (R.oldCoefficientMap_rv_constant hCoeffMem) p z hTags

def oldRadius := gammaFibreValue R.oldApertureMap

include hCoeffMem in
theorem oldRadius_named (hc : CanonicalStructure.IsCanonical (M := M)) (u : Fin q → RVInfinity M) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {R.oldRadius u}} :=
  gammaFibreValue_named hc R.oldApertureMap (R.oldApertureMap_constant hCoeffMem) u

include hCoeffMem in
theorem oldRadius_value (p : focusActive C R.component.activeTags) :
    (R.oldRadius p.val.2).val=vfValue
      ((R.fibreComponents.component (R.context.baseMap ⟨p.val,p.property.1⟩)).coefficient*
        (R.fibreComponents.component (R.context.baseMap ⟨p.val,p.property.1⟩)).extendedFocus
          (Fin.tail p.val.1,p.val.2 ∘ σ)) := by
  have h := R.component.fullFocusGraph.variableActiveRadius_value R.oldCoefficientMap
    R.oldCoefficientMap_nonzero (R.oldCoefficientMap_rv_constant hCoeffMem) p
  have hf : (R.component.focusMap p).val 0=R.component.extendedFocus p.val :=
    (R.component.focusMap_eq p).trans (R.component.extendedFocus_active p.property.1 p.property.2).symm
  change (R.oldRadius p.val.2).val=vfValue ((R.oldCoefficientMap p).val 0*(R.component.focusMap p).val 0) at h
  rw [R.oldCoefficientMap_value,hf,R.focus ⟨p.val,p.property.1⟩] at h
  exact h

include hCoeffMem in
theorem old_noncore_iff (p : C) (hu : p.val.2 ∈ R.component.activeTags.carrier) :
    (R.fibreComponents.component (R.context.baseMap p)).core (Fin.tail p.val.1,p.val.2 ∘ σ)=false ↔
      vfValue (p.val.1 R.component.coordinate-R.component.extendedFocus p.val) ≤ (R.oldRadius p.val.2).val := by
  rw [R.oldRadius_value hCoeffMem ⟨p.val,p.property,hu⟩,R.focus p,R.coordinate,
    ← R.fibreComponents.coordinate (R.context.baseMap p)]
  exact decide_eq_false_iff_not.trans not_lt

end CentripetalFusionRepair
end DiamondIntegral.Section6
