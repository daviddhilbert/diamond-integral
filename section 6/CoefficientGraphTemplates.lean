import «section 6».TemplateValueIdentities

/-! Complete scalar coefficient graphs, with the empty VF input
block removed from the uniform transition's finite real coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p : ℕ}

def coefficientParameterGraph (C : ContinuousVFGraphTemplate (M := M) S p 0 1) : Set (Fin p ⊕ Fin 1 → M) :=
  {z | Sum.elim (z ∘ Sum.inl) (Sum.elim (Fin.elim0 : Fin 0 → M) (z ∘ Sum.inr)) ∈ C.graph}

theorem coefficientParameterGraph_definable (C : ContinuousVFGraphTemplate (M := M) S p 0 1) :
    S.Definable LRV (coefficientParameterGraph C) := by
  have hCode : S.DefinableMap LRV (fun z : Fin p ⊕ Fin 1 → M =>
      Sum.elim (z ∘ Sum.inl) (Sum.elim (Fin.elim0 : Fin 0 → M) (z ∘ Sum.inr))) := by
    rintro (i | (i | i))
    · exact Set.DefinableFun.proj LRV
    · exact i.elim0
    · exact Set.DefinableFun.proj LRV
  exact C.definable.preimage_map hCode

theorem coefficientParameterGraph_at (C : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (a : Fin p → M) (ha : a ∈ C.good) (c : Fin 1 → M) :
    Sum.elim a c ∈ coefficientParameterGraph C ↔ c 0=(vfScalarTemplateValue C a ha).val := by
  constructor
  · intro hc
    exact vfScalarTemplateValue_of_entry C a ha c hc
  · intro hc
    have hEmpty : vfValues (Fin.elim0 : Fin 0 → VF M)=(Fin.elim0 : Fin 0 → M) := funext (fun i => i.elim0)
    have hValue : vfValues (C.value a ha Fin.elim0)=c := by
      funext i
      fin_cases i
      exact hc.symm
    have h := C.value_mem a ha Fin.elim0
    rw [hEmpty,hValue] at h
    exact h

end DiamondIntegral.Section6
