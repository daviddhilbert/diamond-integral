import «section 4».FieldPointCharts
import «section 4».FieldScissorClasses

/-! The affine line is the disjoint sum of its punctured line and a
point in the actual pure-field definable presentation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.FieldAffineDecomposition
open FieldDefinableRing
variable (K : Type) [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def puncturedLine : Chart K :=
  ⟨1, {x | x 0 ≠ 0}, ((pure_proj (0 : Fin 1)).eq_const (0 : K)).compl⟩

def zeroPoint : Chart K :=
  ⟨1, {x | x 0 = 0}, (pure_proj (0 : Fin 1)).eq_const (0 : K)⟩

theorem zeroPoint_class : objectClass K (zeroPoint K) = 1 := by
  apply FieldPointCharts.objectClass_unique
  refine ⟨fun _ => 0, rfl, ?_⟩
  intro x hx
  funext i
  fin_cases i
  exact hx

theorem punctured_plus_one : objectClass K (puncturedLine K) + 1 = affineClass K := by
  have hU : (Set.univ : Set (Fin 1 → K)) = (puncturedLine K).domain ∪ (zeroPoint K).domain := by
    ext x
    change True ↔ x 0 ≠ 0 ∨ x 0 = 0
    tauto
  have hI : (∅ : Set (Fin 1 → K)) = (puncturedLine K).domain ∩ (zeroPoint K).domain := by
    ext x
    change False ↔ x 0 ≠ 0 ∧ x 0 = 0
    tauto
  have h := FieldScissorClasses.objectClass_scissor (puncturedLine K).domain (zeroPoint K).domain
    Set.univ ∅ (puncturedLine K).definable (zeroPoint K).definable
    Set.definable_univ Set.definable_empty hU hI
  have hempty : objectClass K (⟨1, ∅, Set.definable_empty⟩ : Chart K) = 0 :=
    FieldPointCharts.objectClass_empty _ rfl
  change affineClass K + objectClass K (⟨1, ∅, Set.definable_empty⟩ : Chart K) =
    objectClass K (puncturedLine K) + objectClass K (zeroPoint K) at h
  rw [hempty, add_zero, zeroPoint_class] at h
  exact h.symm

end DiamondIntegral.Section4.FieldAffineDecomposition
