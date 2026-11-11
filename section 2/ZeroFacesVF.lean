import «section 2».ZeroFaces
import Section3.ParameterBridge
import Section3.GammaBaseTools

/-! The zero-face charts preserve ground-definability in actual VF sorts.
The fixed zero is named by the language, not added as a parameter. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfZero_singleton_definable (S : Set M) : S.Definable₁ LRV {(0 : VF M).val} :=
  SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.vfZero Fin.elim0
    (fun i => i.elim0)

theorem ZeroFaceChart.vf_slice_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) (D : Set (Fin n → M))
    (hD : DefinableOver S (fun _ => .vf) D) :
    DefinableOver S (fun _ => .vf) (C.slice (0 : VF M).val D) := by
  have hsort : D ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
    obtain ⟨p,φ,hφ,rfl⟩ := hD
    exact fun _ hz => hz.1
  apply raw_definableOver_sorted hc
  · exact C.slice_definable S _ (vfZero_singleton_definable S) D hD.raw_definable
  · intro x hx j
    have h := hsort hx.1 (C.freeIndex j)
    change iVF (C.insert (0 : VF M).val x (C.freeIndex j)) at h
    rwa [C.insert_free] at h

theorem ZeroFaceChart.vf_lift_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z)
    (V : Set (Fin C.freeArity → M)) (hV : DefinableOver S (fun _ => .vf) V) :
    DefinableOver S (fun _ => .vf) (C.lift (0 : VF M).val V) := by
  have hsort : V ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
    obtain ⟨p,φ,hφ,rfl⟩ := hV
    exact fun _ hz => hz.1
  apply raw_definableOver_sorted hc
  · exact C.lift_definable S _ (vfZero_singleton_definable S) V hV.raw_definable
  · intro y hy j
    rcases C.coordinate_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact (hy.1 i).symm ▸ (0 : VF M).property
    · exact hsort hy.2 i

end DiamondIntegral.Section2
