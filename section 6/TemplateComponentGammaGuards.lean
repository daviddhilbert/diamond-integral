import «section 6».TemplateComponentFamilies
import «section 6».FormCompatibleProgramLoci

/-! The actual local components of a template family satisfy its full
Gamma-core guard. Their coordinate, coefficient, active tags and complete
focus graph identify the literal transition used by the first-order test. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.TemplateComponentFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good A P}

theorem component_transition_graph (L : TemplateComponentFamily (G := G) η T A P hGood) (b : B) :
    {z | Sum.elim (unaryFamilyParameter η b) z ∈ focusComponentTransition T A}=
      (rawMixedSpace n s).relation (rawMixedSpace n (1+s)) (L.component b).bijection.graph :=
  focusComponentTransition_at T A _ (hGood b).1.1.1 (hGood b).1.1.2 (L.component b)
    (L.coordinate b) (L.active b) (L.coefficient b) (L.focus b)

theorem component_core_form_constant
    (L : TemplateComponentFamily (G := G) η T A P hGood) (h00 : M ⊨ Axioms.ACVF00)
    (W : GammaFormParameterTemplate (M := M) S 1 n s)
    (ζ : ∀ b : B,Map (A.fibre (unaryFamilyParameter η b))
      (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range (unaryFamilyParameter η b))))
    (hGraph : ∀ b,{z | Sum.elim (unaryFamilyParameter η b) z ∈ W.graph}=
      (rawMixedSpace n s).relation rawGammaPresentation (ζ b).graph)
    (hGuard : ∀ b,unaryFamilyParameter η b ∈ (CentripetalProgramTemplate.centripetal T).coreFormGood A W) (b : B) :
    (L.component b).CoreFormConstant (ζ b) := by
  have h := hGuard b
  change unaryFamilyParameter η b ∈ gammaCoreConstantParameterLocus (focusComponentTransition T A) W.graph T.coordinate _ at h
  rw [← L.coordinate b] at h
  exact (gammaCoreConstantParameterLocus_at_component _ _ _ (L.component b) h00 (ζ b)
    (L.component_transition_graph b) (hGraph b)).mp h

end DiamondIntegral.Section6.TemplateComponentFamily
