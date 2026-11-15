import «section 5».PuiseuxOriginalModelActions
import «section 5».PuiseuxRVLanguage

/-! The presentation is constructed for the concrete canonical structure,
in the paper's standing ACVF-model context. The model hypothesis is kept
explicit; canonical totalization alone does not assert ACVF satisfaction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

local instance canonicalModelStructure : LRV.Structure Carrier := canonicalInterpret
variable [hM : Carrier ⊨ Axioms.ACVF]

theorem vfType_tag (a : VFType (M := Carrier)) : Sum.inl (vfPart a.val) = a.val := by
  rcases a with ⟨a, ha⟩
  cases a with
  | inl f => rfl
  | inr r => exact False.elim ha

def taggedFieldEquiv : VFType (M := Carrier) ≃+* PuiseuxSeries ℂ where
  toFun a := vfPart a.val
  invFun f := ⟨Sum.inl f, trivial⟩
  left_inv a := Subtype.ext (vfType_tag a)
  right_inv _ := rfl
  map_mul' a b := by
    have ha := vfType_tag a
    have hb := vfType_tag b
    change vfPart (iVFMul a.val b.val) = _
    rw [← ha, ← hb]
    change vfPart (if ∀ i : Fin 2, @sortEval Carrier interpret .vf
      ((![Sum.inl (vfPart a.val), Sum.inl (vfPart b.val)] : Fin 2 → Carrier) i)
      then Sum.inl (vfPart a.val * vfPart b.val) else _) = _
    rw [if_pos (by intro i; fin_cases i <;> trivial)]
    rfl
  map_add' a b := by
    have ha := vfType_tag a
    have hb := vfType_tag b
    change vfPart (iVFAdd a.val b.val) = _
    rw [← ha, ← hb]
    change vfPart (if ∀ i : Fin 2, @sortEval Carrier interpret .vf
      ((![Sum.inl (vfPart a.val), Sum.inl (vfPart b.val)] : Fin 2 → Carrier) i)
      then Sum.inl (vfPart a.val + vfPart b.val) else _) = _
    rw [if_pos (by intro i; fin_cases i <;> trivial)]
    rfl

theorem rvOfField_value (f : PuiseuxSeries ℂ) :
    value (rvOfField f) = (f : HahnSeries ℚ ℂ).orderTop := by
  by_cases hf : f = 0
  · subst f
    simp [rvOfField, RVCalc.rv, rvNormalEquiv, _root_.Equiv.optionCongr, value]
  · change value (rvNormalEquiv (RVCalc.rv (puiseuxValuation ℂ) f)) = _
    rw [RVCalc.rv, dif_neg hf]
    change ((puiseuxRVUnitEquiv
      (QuotientGroup.mk' (RVCalc.principalUnits (puiseuxValuation ℂ)) (Units.mk0 f hf))).1.toAdd : WithTop ℚ) = _
    rw [puiseuxRVUnitEquiv_mk]
    exact HahnSeries.order_eq_orderTop_of_ne_zero (fun h => hf (Subtype.ext h))

theorem taggedFieldEquiv_valuation (a b : VFType (M := Carrier)) :
    VFValued.predV a b ↔
      puiseuxValuation ℂ (taggedFieldEquiv a) ≤ puiseuxValuation ℂ (taggedFieldEquiv b) := by
  have ha := vfType_tag a
  have hb := vfType_tag b
  change iLe (iRv b.val) (iRv a.val) ↔ _
  rw [← ha, ← hb]
  have hrv (f : PuiseuxSeries ℂ) : iRv (Sum.inl f : Carrier) = Sum.inr (rvOfField f) := by
    change (if ∀ i : Fin 1, @sortEval Carrier interpret .vf
      ((![Sum.inl f] : Fin 1 → Carrier) i) then Sum.inr (rvOfField f) else _) = _
    rw [if_pos (by intro i; fin_cases i; trivial)]
  rw [hrv, hrv]
  change ((∀ i : Fin 2, ¬ inVF ((![Sum.inr (rvOfField (vfPart b.val)),
      Sum.inr (rvOfField (vfPart a.val))] : Fin 2 → Carrier) i)) ∧
      ¬ inVF (Sum.inr (rvOfField (vfPart b.val))) ∧
      ¬ inVF (Sum.inr (rvOfField (vfPart a.val))) ∧
      value (rvOfField (vfPart b.val)) ≤ value (rvOfField (vfPart a.val))) ↔ _
  simp only [inVF, not_false_eq_true, and_true, true_and]
  rw [rvOfField_value, rvOfField_value]
  change _ ↔ (vfPart b.val : HahnSeries ℚ ℂ).orderTop ≤ (vfPart a.val : HahnSeries ℚ ℂ).orderTop
  simp [inVF]

/-- The old abstract presentation is now instantiated by the actual tagged
VF sort and the actual Hahn valuation, rather than supplied as extra data. -/
def canonicalModelPresentation : PuiseuxModelPresentation Carrier where
  fieldEquiv := taggedFieldEquiv
  valuation_iff := taggedFieldEquiv_valuation

def canonicalModelAction (η : CompatibleRoots ℂ) : Carrier ≃[LRV] Carrier :=
  puiseuxOriginalModelAction canonicalModelPresentation canonicalInterpret_isCanonical η

end DiamondIntegral.Section5.PuiseuxOriginal
