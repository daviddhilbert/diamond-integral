import «section 6».MeasuredCentripetalProgramTemplates
import «section 6».CentripetalProgramSubstitution

/-! Definable freezing or reparametrization transports the whole
Gamma graph and the measured terminal test together with the complete
finite program. No level value is added to the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p q n r s k : ℕ}

def GammaFormParameterTemplate.substitute (W : GammaFormParameterTemplate (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) : GammaFormParameterTemplate (M := M) S q n r :=
  ⟨parameterSubstitution h W.graph,parameterSubstitution_definable h _ W.definable⟩

theorem GammaFormParameterTemplate.substitute_section (W : GammaFormParameterTemplate (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) (a : Fin q → M) :
    {z | Sum.elim a z ∈ (W.substitute h).graph}={z | Sum.elim (h.value a) z ∈ W.graph} := rfl

theorem gammaTransitionConstantParameterLocus_substitute
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (h : DefinableParameterSubstitution (M := M) S p q) :
    gammaTransitionConstantParameterLocus (parameterSubstitution h R) (parameterSubstitution h W)=
      h.value ⁻¹' gammaTransitionConstantParameterLocus R W := by
  ext a
  rfl

theorem CentripetalProgramTemplate.substitute_measuredGood
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) :
    (T.substitute h).measuredGood (A.substitute h) (fun i => (P i).substitute h) (W.substitute h)=
      h.value ⁻¹' T.measuredGood A P W := by
  unfold CentripetalProgramTemplate.measuredGood
  rw [T.substitute_preparedGood h A P,T.substitute_transition h A]
  rw [show (W.substitute h).graph=parameterSubstitution h W.graph from rfl]
  rw [gammaTransitionConstantParameterLocus_substitute]
  rfl

end DiamondIntegral.Section6
