import «section 6».PromotedContinuousRVTemplates
import «section 6».PartialFocusGraphTemplates

/-! Actual proper partial focus maps supply complete continuous
RV-family graphs over their original base. The whole graph, with all
old labels, enters parameter promotion without a separate choice per row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem rvVFGraph_eq_functionFamilyGraph
    (F : (Fin r ⊕ Fin n → M) → M)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin 1 → VF M)
    (hAt : ∀ u x,F (Sum.elim (rvValues u) (vfValues x))=(f u x 0).val) :
    rvVFGraph f=rvFunctionFamilyGraph F := by
  ext z
  constructor
  · rintro ⟨u,x,rfl⟩
    exact ⟨⟨fun i => (u i).property,fun i => (x i).property⟩,hAt u x⟩
  · rintro ⟨⟨hRV,hVF⟩,hValue⟩
    let u : Fin r → RVInfinity M := fun i => ⟨z (.inl i),hRV i⟩
    let x : Fin n → VF M := fun i => ⟨z (.inr (.inl i)),hVF i⟩
    have hArgs : rvFunctionFamilyArgs z=Sum.elim (rvValues u) (vfValues x) := by
      funext i; cases i <;> rfl
    rw [hArgs,hAt] at hValue
    refine ⟨u,x,?_⟩
    funext i
    rcases i with i | (i | i)
    · rfl
    · rfl
    · fin_cases i
      exact hValue

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem proper_partial_focus_total_rv_family_graph
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S}
    (f : Map A B) (hA : ProperInvariant S A.carrier) (hCont : ∀ u,Continuous (FMT.focusFibre f u)) :
    (∀ u,Continuous (totalFocusFibre f u)) ∧ S.Definable LRV (rvVFGraph (totalFocusFibre f)) := by
  refine ⟨fun u => totalFocusFibre_continuous f u (hA.clopen_fibres hv u) (hCont u),?_⟩
  rw [rvVFGraph_eq_functionFamilyGraph (totalFocusFamilyCode f) (totalFocusFibre f) (totalFocusFamilyCode_at f)]
  exact rvFunctionFamilyGraph_definable _ (totalFocusFamilyCode_definable f)

end DiamondIntegral.Section6
