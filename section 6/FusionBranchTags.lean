import «section 6».FusionOldApertureStability
import «section 6».SelectedCentripetalPoints

/-! Canonical retained-RV branch tags separate the new core,
released old core, and old noncore. The residual branch is exactly
where the old and new actual component maps agree. -/

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

theorem regularized_boolean_tag_iff (h00 : M ⊨ Axioms.ACVF00)
    {C : DefSet (rawMixedSpace (M := M) n q) S} (D : CentripetalData (G := G) C)
    (a : Mixed M n q) (b : Bool) :
    (regularize (D.point a)).2 ∈
      (rvBooleanTagSet S (Fin.natAdd n (Fin.castAdd q (0 : Fin 1))) b).carrier ↔ D.core a=b := by
  change (regularize (D.point a)).2 (Fin.natAdd n (Fin.castAdd q (0 : Fin 1)))=branchTag b ↔ _
  rw [D.regularized_core_flag]
  exact ⟨fun h => branchTag_injective h00 h,congrArg (branchTag (M := M))⟩

variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
namespace CentripetalFusionRepair
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

def coreTags (_R : CentripetalFusionRepair (G := G) η T K A P C π σ) :=
  rvBooleanTagSet S (Fin.natAdd (n+1) (Fin.castAdd q (0 : Fin 1))) true

def releaseTags
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :=
  R.component.variableReleaseTags R.oldApertureMap (R.oldApertureMap_constant hCoeffMem)

def residualTags
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    DefSet (rawRVSpace (M := M) ((n+1)+(1+q))) S := by
  let U := rvBooleanTagSet S (Fin.natAdd (n+1) (Fin.castAdd q (0 : Fin 1))) false
  exact ⟨U.carrier \ (R.releaseTags hCoeffMem).carrier,U.definable.sdiff _ (R.releaseTags hCoeffMem).definable⟩

theorem local_noncore_implies_global (a : C)
    (hOld : (R.fibreComponents.component (R.context.baseMap a)).core (Fin.tail a.val.1,a.val.2 ∘ σ)=false) :
    R.component.core a.val=false :=
  enlarged_aperture_noncore R.component (R.fibreComponents.component (R.context.baseMap a)) σ a.val
    (R.coordinate.trans (congrArg Fin.succ (R.fibreComponents.coordinate (R.context.baseMap a))).symm)
    (R.focus a) (R.coefficient (R.context.baseMap a)) hOld

theorem residualTags_at (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (a : C) : (regularize (R.component.point a.val)).2 ∈ (R.residualTags hCoeffMem).carrier ↔
      (R.fibreComponents.component (R.context.baseMap a)).core (Fin.tail a.val.1,a.val.2 ∘ σ)=false := by
  change ((regularize (R.component.point a.val)).2 ∈ (rvBooleanTagSet S _ false).carrier ∧
    (regularize (R.component.point a.val)).2 ∉ (R.releaseTags hCoeffMem).carrier) ↔ _
  rw [regularized_boolean_tag_iff h00 R.component a.val false]
  change (R.component.core a.val=false ∧
    (regularize (R.component.point a.val)).2 ∉
      (R.component.variableReleaseTags R.oldApertureMap (R.oldApertureMap_constant hCoeffMem)).carrier) ↔ _
  rw [R.component.variableReleaseTags_at h00 R.oldApertureMap (R.oldApertureMap_constant hCoeffMem) a.val a.property]
  constructor
  · rintro ⟨hNew,hNot⟩
    by_cases hu : a.val.2 ∈ R.component.activeTags.carrier
    · apply (R.old_noncore_iff hCoeffMem a hu).mpr
      apply le_of_not_gt
      intro hStrict
      exact hNot ⟨hu,hStrict,hNew⟩
    · apply (R.fibreComponents.component (R.context.baseMap a)).core_inactive
      exact fun h => hu ((R.active a).mpr h)
  · intro hOld
    refine ⟨R.local_noncore_implies_global a hOld,?_⟩
    rintro ⟨hu,hStrict,hNew⟩
    exact (not_lt_of_ge ((R.old_noncore_iff hCoeffMem a hu).mp hOld)) hStrict

end CentripetalFusionRepair
end DiamondIntegral.Section6
