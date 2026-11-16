import «section 6».UniformProgramFamilies
import «section 6».IndexedCoefficientCutoffs

/-! Actual local permitted components for a complete admissible
template family. Their precise coordinate, active locus, coefficient,
full focus graph and every protected restriction are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

structure TemplateComponentFamily
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : FocusComponentParameterTemplate (M := M) S 1 n s)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good A P) where
  component : ∀ b : B,CentripetalData (G := G) (A.fibre (unaryFamilyParameter η b))
  coordinate : ∀ b,(component b).coordinate=T.coordinate
  active : ∀ b,(component b).activeTags=T.active.fibre (unaryFamilyParameter η b)
  coefficient : ∀ b,(component b).coefficient=
    vfScalarTemplateValue T.coefficient (unaryFamilyParameter η b) (hGood b).1.1.2
  focus : ∀ b,∀ p : focusActive (A.fibre (unaryFamilyParameter η b))
    (T.active.fibre (unaryFamilyParameter η b)),(component b).extendedFocus p.val=
      T.focus.value _ (hGood b).1.1.1 p.val.2 p.val.1 0
  restrictions : ∀ b i,∃ E : CentripetalData (G := G) ((P i).fibre (unaryFamilyParameter η b)),
    ApertureRestrictionData (component b) E

def templateComponentFamily
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : FocusComponentParameterTemplate (M := M) S 1 n s)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good A P)
    (hGeo : ∀ b : B,TemplateFibreGeometry A P (unaryFamilyParameter η b)) :
    TemplateComponentFamily (G := G) η T A P hGood := by
  have h (b : B) := T.exists_component hc hv A P _ (hGood b) (hGeo b).proper
    (hGeo b).doublyBounded (hGeo b).subset (hGeo b).piecesProper
  exact {
    component := fun b => (h b).choose
    coordinate := fun b => (h b).choose_spec.1
    active := fun b => (h b).choose_spec.2.1
    coefficient := fun b => (h b).choose_spec.2.2.1
    focus := fun b => (h b).choose_spec.2.2.2.1
    restrictions := fun b => (h b).choose_spec.2.2.2.2 }

theorem TemplateComponentFamily.coefficient_map
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {T : FocusComponentParameterTemplate (M := M) S 1 n s}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good A P}
    (L : TemplateComponentFamily (G := G) η T A P hGood) (b : B) :
    (unaryCoefficientMap T.coefficient η (fun b => (hGood b).1.1.2) b).val 0=(L.component b).coefficient :=
  (unaryCoefficientMap_value T.coefficient η _ b).trans (L.coefficient b).symm

end DiamondIntegral.Section6
