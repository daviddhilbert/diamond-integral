import «section 6».ConstrainedContinuousVFTemplates

/-! Current proper partial focus domains give genuine total continuous
VF graph rows by zero extension. Their complete graphs stay over the
original base together with the existing RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem totalFocusFibre_continuous
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S}
    (f : Map A B) (u : Fin r → RVInfinity M) (hA : IsClopen (vfFibre A.carrier u))
    (hf : Continuous (FMT.focusFibre f u)) : Continuous (totalFocusFibre f u) := by
  apply continuous_of_clopen_zero_complement (vfFibre A.carrier u) hA
    (totalFocusFibre f u) (totalFocusFibre_continuousOn f u hf)
  exact fun x hx => totalFocusFibre_off f u x hx

theorem proper_partial_focus_total_graph
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S}
    (f : Map A B) (hA : ProperInvariant S A.carrier)
    (u : Fin r → RVInfinity M) (hf : Continuous (FMT.focusFibre f u)) :
    Continuous (totalFocusFibre f u) ∧
      (S ∪ Set.range (rvValues u)).Definable LRV (vfGraph (totalFocusFibre f u)) := by
  refine ⟨totalFocusFibre_continuous f u (hA.clopen_fibres hv u) hf,?_⟩
  exact rvFunctionFamily_section_definable (totalFocusFamilyCode f) (totalFocusFamilyCode_definable f)
    (totalFocusFibre f) (totalFocusFamilyCode_at f) u

end DiamondIntegral.Section6
