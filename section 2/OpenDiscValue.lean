import «section 2».GammaBallRelations
import «section 2».DiscGeometry

/-! The actual open-disc code and its strict valuative inequality. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem openDiscCode_mem_iff_value (a x : VF M) (γ : Gamma M) :
    x.val ∈ BallImaginaries.underlying (openDiscCode a γ) ↔ γ.val < vfValue (x-a) := by
  obtain ⟨G,hG,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  let r := radiusRepresentative γ.val
  have hr : r ≠ 0 := fun h => γ.property ((radiusRepresentative_zero_iff _).mp h)
  have hf : finiteValue r hr = γ := Subtype.ext (radiusRepresentative_value _)
  change x ∈ discPoints (openDiscCode a γ) ↔ _
  rw [← hf,openDiscCode_points v hv a r hr]
  change v (x-a) < v r ↔ Values.vrv (rv M r) < Values.vrv (rv M (x-a))
  conv_rhs => rw [lt_iff_not_ge,Values.vrv_le_iff]
  change v (x-a) < v r ↔ ¬ VFValued.predV r (x-a)
  rw [hv,not_le]

end DiamondIntegral.Section2
