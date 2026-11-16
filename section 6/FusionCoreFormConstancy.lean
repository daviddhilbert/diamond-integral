import «section 6».MeasuredFusionStepAssembly

/-! Actual local component forms control both the variable old core and
the contracted global core. Equal complementary VF coordinates recover
the identical base point, rather than just an RV-equivalent parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalFusionRepair
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

def localSourcePoint (p : C) : A.fibre (unaryFamilyParameter R.parameter (R.context.baseMap p)) :=
  ⟨(Fin.tail p.val.1,p.val.2 ∘ σ),by
    obtain ⟨b,hb,hA⟩ := (mem_unaryIndexedMixedFamily R.parameter A _).mp (R.context.source p.val p.property)
    have hBase : b=R.context.baseMap p := Subtype.ext
      (hb.symm.trans ((selectedJointPoint_base π σ p.val).trans (R.context.baseMap_value p).symm))
    rw [hBase] at hA
    rwa [selectedJointPoint_local] at hA⟩

theorem baseMap_eq_of_complement
    (p z : C) (hOther : ∀ i,i ≠ R.component.coordinate → p.val.1 i=z.val.1 i) (hTags : p.val.2=z.val.2) :
    R.context.baseMap p=R.context.baseMap z := by
  apply Subtype.ext
  rw [R.context.baseMap_value,R.context.baseMap_value]
  apply Prod.ext
  · funext i
    exact hOther 0 (by rw [R.coordinate]; exact (Fin.succ_ne_zero _).symm)
  · exact congrArg (fun u => u ∘ π) hTags

theorem oldRadius_le_global_cutoff
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (p : C) (hu : p.val.2 ∈ R.component.activeTags.carrier) :
    (R.oldRadius p.val.2).val ≤ vfValue (R.component.coefficient*R.component.extendedFocus p.val) := by
  rw [R.oldRadius_value hCoeffMem ⟨p.val,p.property,hu⟩,R.focus p]
  change vfValue ((R.fibreComponents.component (R.context.baseMap p)).coefficient*
      (R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ)) ≤
    vfValue (R.component.coefficient*
      (R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ))
  calc
    _ = vfValue (R.fibreComponents.component (R.context.baseMap p)).coefficient*
        vfValue ((R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ)) :=
      Values.vfValueHom.map_mul _ _
    _ ≤ vfValue R.component.coefficient*
        vfValue ((R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ)) :=
      mul_le_mul_left (R.coefficient (R.context.baseMap p)) _
    _ = _ := (Values.vfValueHom.map_mul _ _).symm

theorem variable_core_form_constant_of_local_forms
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (ζ : ∀ b : B,Map (A.fibre (unaryFamilyParameter R.parameter b))
      (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range (unaryFamilyParameter R.parameter b))))
    (hζ : ∀ b,(R.fibreComponents.component b).CoreFormConstant (ζ b))
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hForm : ∀ p : C,gammaFormExtension (ζ (R.context.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    R.component.VariableCoreFormConstant R.oldRadius ω := by
  intro p z hpAct hzAct hpOld hzOld hOther hTags
  have hBase : R.context.baseMap z=R.context.baseMap p := (R.baseMap_eq_of_complement p z hOther hTags).symm
  let b := R.context.baseMap p
  let x := R.localSourcePoint p
  let y : A.fibre (unaryFamilyParameter R.parameter b) :=
    ⟨(Fin.tail z.val.1,z.val.2 ∘ σ),by
      have hz := (R.localSourcePoint z).property
      change (Fin.tail z.val.1,z.val.2 ∘ σ) ∈ (A.fibre (unaryFamilyParameter R.parameter (R.context.baseMap z))).carrier at hz
      rw [hBase] at hz
      exact hz⟩
  have hpCore : (R.fibreComponents.component (R.context.baseMap p)).core (Fin.tail p.val.1,p.val.2 ∘ σ)=true := by
    rw [R.oldRadius_value hCoeffMem ⟨p.val,p.property,hpAct⟩,R.focus p,R.coordinate,
      ← R.fibreComponents.coordinate (R.context.baseMap p)] at hpOld
    exact decide_eq_true hpOld
  have hzCore : (R.fibreComponents.component (R.context.baseMap z)).core (Fin.tail z.val.1,z.val.2 ∘ σ)=true := by
    rw [R.oldRadius_value hCoeffMem ⟨z.val,z.property,hzAct⟩,R.focus z,R.coordinate,
      ← R.fibreComponents.coordinate (R.context.baseMap z)] at hzOld
    exact decide_eq_true hzOld
  rw [hBase] at hzCore
  have hLocalOther (i) (hi : i ≠ (R.fibreComponents.component b).coordinate) : x.val.1 i=y.val.1 i := by
    have hiK : i ≠ K.coordinate := fun h => hi (h.trans (R.fibreComponents.coordinate b).symm)
    apply hOther i.succ
    rw [R.coordinate]
    simpa only [ne_eq,Fin.succ_inj] using hiK
  have hLocal := hζ b x y hpCore hzCore hLocalOther (congrArg (fun u => u ∘ σ) hTags)
  have hzForm := hForm z
  rw [hBase] at hzForm
  have hLocalExt := (gammaFormExtension_at (ζ b) x).trans (hLocal.trans (gammaFormExtension_at (ζ b) y).symm)
  exact (hForm p).symm.trans (hLocalExt.trans hzForm)

end CentripetalFusionRepair

namespace CentripetalData
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem VariableCoreFormConstant.core_of_cutoff {D : CentripetalData (G := G) A}
    {ρ : (Fin r → RVInfinity M) → Gamma M}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} (h : D.VariableCoreFormConstant ρ ω)
    (hDom : ∀ p : A,p.val.2 ∈ D.activeTags.carrier → (ρ p.val.2).val ≤ vfValue (D.coefficient*D.extendedFocus p.val)) :
    D.CoreFormConstant ω := by
  intro p q hp hq hOther hTags
  have hpA := D.core_true_active p.val hp
  have hqA := D.core_true_active q.val hq
  exact h p q hpA hqA ((hDom p hpA).trans_lt (of_decide_eq_true hp))
    ((hDom q hqA).trans_lt (of_decide_eq_true hq)) hOther hTags

end CentripetalData
end DiamondIntegral.Section6
