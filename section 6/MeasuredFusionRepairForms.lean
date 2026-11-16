import «section 6».MeasuredCentripetalFusionRepairs

/-! An actual measured fusion repair supplies both aperture form
conditions to the full measured step assembly. These conditions follow
from its guarded local components, rather than being accepted inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.MeasuredCentripetalFusionRepair
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable {ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable (R : MeasuredCentripetalFusionRepair (G := G) η T K A P W C π σ ω)

theorem variable_core_form_constant (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    R.geometric.component.VariableCoreFormConstant R.geometric.oldRadius ω :=
  R.geometric.variable_core_form_constant_of_local_forms hCoeffMem R.family.forms
    (R.geometric.fibreComponents.component_core_form_constant h00 W R.family.forms R.family.graphs R.firstCore)
    ω R.sourceForm

theorem core_form_constant (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    R.geometric.component.CoreFormConstant ω :=
  (R.variable_core_form_constant h00 hCoeffMem).core_of_cutoff (R.geometric.oldRadius_le_global_cutoff hCoeffMem)

end DiamondIntegral.Section6.MeasuredCentripetalFusionRepair
