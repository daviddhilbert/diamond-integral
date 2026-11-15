import «section 5».PuiseuxResiduePresentation
import Section3.GammaValueLaws

/-! The native Gamma quotient of the concrete original structure is the
actual rational value set with its top element. This connects native finite
value support with the finite Kummer coordinate construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
local instance valuePresentationStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

theorem rv_order_value (r s : CanonicalRV.RVSort Carrier) :
    iLe r.val s.val ↔ value (taggedRVEquiv r) ≤ value (taggedRVEquiv s) := by
  have hr := rvSort_tag r
  have hs := rvSort_tag s
  rw [← hr, ← hs]
  change ((∀ i : Fin 2, ¬ inVF
      ((![Sum.inr (taggedRVEquiv r), Sum.inr (taggedRVEquiv s)] : Fin 2 → Carrier) i)) ∧
    ¬ inVF (Sum.inr (taggedRVEquiv r)) ∧ ¬ inVF (Sum.inr (taggedRVEquiv s)) ∧
    value (taggedRVEquiv r) ≤ value (taggedRVEquiv s)) ↔ _
  simp [inVF]

theorem vrv_eq_iff_value_eq (r s : CanonicalRV.RVSort Carrier) :
    Values.vrv r = Values.vrv s ↔ value (taggedRVEquiv r) = value (taggedRVEquiv s) := by
  rw [le_antisymm_iff, le_antisymm_iff, Values.vrv_le_iff, Values.vrv_le_iff,
    rv_order_value, rv_order_value]

theorem normal_value_surjective : Function.Surjective
    (fun r : CanonicalRV.RVSort Carrier => value (taggedRVEquiv r)) := by
  intro q
  cases q with
  | top => exact ⟨rvTag none, rfl⟩
  | coe q => exact ⟨rvTag (some (Multiplicative.ofAdd q, 1)), rfl⟩

def gammaNormalEquiv : Values.GammaTop (M := Carrier) ≃ WithTop ℚ :=
  CanonicalRV.equivOfSameFibers Values.vrv
    (fun r : CanonicalRV.RVSort Carrier => value (taggedRVEquiv r))
    Values.vrv_surjective normal_value_surjective vrv_eq_iff_value_eq

theorem gammaNormalEquiv_vrv (r : CanonicalRV.RVSort Carrier) :
    gammaNormalEquiv (Values.vrv r) = value (taggedRVEquiv r) :=
  CanonicalRV.equivOfSameFibers_apply Values.vrv
    (fun r : CanonicalRV.RVSort Carrier => value (taggedRVEquiv r))
    Values.vrv_surjective normal_value_surjective vrv_eq_iff_value_eq r

end DiamondIntegral.Section5.PuiseuxOriginal
