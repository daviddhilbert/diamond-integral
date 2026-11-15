import «section 5».PuiseuxCanonicalPresentation
import Section4.ResidueNormalization

/-! The residue field of the concrete canonical model is the original
complex coefficient field, with its actual residue operations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity

local instance residueModelStructure : LRV.Structure Carrier := canonicalInterpret
variable [hM : Carrier ⊨ Axioms.ACVF]

def rvTag (r : RV) : CanonicalRV.RVSort Carrier := ⟨Sum.inr r, by exact not_false⟩

theorem rvSort_tag (r : CanonicalRV.RVSort Carrier) : Sum.inr (rvPart r.val) = r.val := by
  rcases r with ⟨r, hr⟩
  cases r with
  | inl f => exact False.elim (hr trivial)
  | inr r => rfl

def taggedRVEquiv : CanonicalRV.RVSort Carrier ≃ RV where
  toFun r := rvPart r.val
  invFun := rvTag
  left_inv r := Subtype.ext (rvSort_tag r)
  right_inv _ := rfl

theorem rvTag_zero : rvTag none = (0 : CanonicalRV.RVSort Carrier) := by
  apply Subtype.ext
  rw [RVOperations.zero_val]
  rfl

theorem rvTag_mul (r s : RV) : rvTag (rvMul r s) = rvTag r * rvTag s := by
  apply Subtype.ext
  rw [RVOperations.mul_val]
  change _ = if ∀ i : Fin 2, @sortEval Carrier interpret .rv
    ((![Sum.inr r, Sum.inr s] : Fin 2 → Carrier) i) then Sum.inr (rvMul r s) else _
  rw [if_pos (by intro i; fin_cases i <;> exact not_false)]
  rfl

theorem rvTag_add (r s : RV) :
    rvTag (kAdd r s) = ValuedModelMap.addK (rvTag r) (rvTag s) := by
  apply Subtype.ext
  change _ = if ∀ i : Fin 2, @sortEval Carrier interpret .rv
    ((![Sum.inr r, Sum.inr s] : Fin 2 → Carrier) i) then Sum.inr (kAdd r s) else _
  rw [if_pos (by intro i; fin_cases i <;> exact not_false)]
  rfl

theorem rvTag_inK (r : RV) : ValuedModelMap.inK (rvTag r) ↔ inResidue r := by
  change ((¬ inVF (Sum.inr r)) ∧ value r = 0) ∨ rvTag r = ValuedModelMap.zeroRV ↔ _
  have hz : rvTag r = ValuedModelMap.zeroRV ↔ r = none := by
    change rvTag r = rvTag none ↔ _
    exact taggedRVEquiv.symm.injective.eq_iff
  rw [hz]
  cases r with
  | none => simp [value, inResidue]
  | some u =>
    simp only [inVF, not_false_eq_true, value, Option.some_ne_none, inResidue,
      true_and, or_false]
    constructor
    · intro h
      exact congrArg Multiplicative.ofAdd (WithTop.coe_injective h)
    · intro h
      rw [h]
      rfl

theorem residueLift_coefficient (c : ℂ) : residue (residueLift c) = c := by
  by_cases hc : c = 0 <;> simp [residueLift, residue, hc]

theorem residueLift_residue (r : RV) (hr : inResidue r) : residueLift (residue r) = r := by
  cases r with
  | none => simp [residueLift, residue]
  | some u =>
    change u.1 = 1 at hr
    simp only [residue, hr, ↓reduceIte, residueLift, Units.ne_zero, ↓reduceDIte]
    congr 2
    · exact hr.symm
    · exact Units.ext rfl

theorem residueLift_mul (c d : ℂ) : residueLift (c * d) = rvMul (residueLift c) (residueLift d) := by
  by_cases hc : c = 0
  · simp [residueLift, hc, rvMul]
  by_cases hd : d = 0
  · simp [residueLift, hc, hd, rvMul]
  simp only [residueLift, hc, hd, mul_ne_zero hc hd, ↓reduceDIte, rvMul]
  congr 2
  · simp
  · exact Units.ext rfl

theorem residueLift_inResidue (c : ℂ) : inResidue (residueLift c) := by
  by_cases hc : c = 0 <;> simp [residueLift, hc, inResidue]

theorem residueLift_add (c d : ℂ) : residueLift (c + d) = kAdd (residueLift c) (residueLift d) := by
  rw [kAdd, if_pos ⟨residueLift_inResidue c, residueLift_inResidue d⟩,
    residueLift_coefficient, residueLift_coefficient]

def complexResidue (c : ℂ) : ModelResidue Carrier := residuePart (rvTag (residueLift c))

theorem residueRV_complexResidue (c : ℂ) :
    residueRV (complexResidue c) = rvTag (residueLift c) :=
  residueRV_part ((rvTag_inK _).mpr (residueLift_inResidue c))

def complexResidueEquiv : ℂ ≃+* ModelResidue Carrier where
  toFun := complexResidue
  invFun x := residue (taggedRVEquiv (residueRV x))
  left_inv c := by
    change residue (taggedRVEquiv (residueRV (complexResidue c))) = c
    rw [residueRV_complexResidue]
    exact residueLift_coefficient c
  right_inv x := by
    apply residueRV_injective
    rw [residueRV_complexResidue]
    have hr : inResidue (taggedRVEquiv (residueRV x)) :=
      (rvTag_inK _).mp ((taggedRVEquiv.symm_apply_apply (residueRV x)) ▸ residueRV_inK x)
    rw [residueLift_residue _ hr]
    exact taggedRVEquiv.symm_apply_apply _
  map_mul' c d := by
    apply residueRV_injective
    rw [residueRV_mul, residueRV_complexResidue, residueRV_complexResidue,
      residueRV_complexResidue, residueLift_mul, rvTag_mul]
  map_add' c d := by
    apply residueRV_injective
    rw [residueRV_add, residueRV_complexResidue, residueRV_complexResidue,
      residueRV_complexResidue, residueLift_add, rvTag_add]

end DiamondIntegral.Section5.PuiseuxOriginal
