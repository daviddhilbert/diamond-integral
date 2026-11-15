import «section 5».PuiseuxResiduePresentation
import Section6.ConcreteValued

/-! The residue field of the actual Hahn valuation on complex Puiseux
series is C. This is proved before assuming any ACVF-model assertion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Section6

abbrev v := puiseuxValuation ℂ

theorem constant_valuation (c : ℂ) : v (puiseuxConstant c) = if c = 0 then 0 else 1 := by
  by_cases hc : c = 0
  · simp [hc,v]
  · change Multiplicative.ofAdd ((puiseuxConstant c : HahnSeries ℚ ℂ).orderTop) = _
    rw [puiseuxConstant_coe]
    simp [HahnSeries.C,orderTop_single,hc]

def constantInteger : ℂ →+* v.valuationSubring :=
  (puiseuxConstant (k := ℂ)).codRestrict _ (by
    intro c
    rw [Valuation.mem_valuationSubring_iff,constant_valuation]
    split <;> simp)

def constantResidue : ℂ →+* ConcreteRV.Residue v :=
  (IsLocalRing.residue v.valuationSubring).comp constantInteger

theorem normal_constant (c : ℂ) : rvOfField (puiseuxConstant c) = residueLift c := by
  by_cases hc : c = 0
  · simp [hc,rvOfField,RVCalc.rv_zero,rvNormalEquiv,residueLift,_root_.Equiv.optionCongr]
  · have hf : puiseuxConstant c ≠ (0 : PuiseuxSeries ℂ) := (map_ne_zero puiseuxConstant).mpr hc
    rw [rvOfField,RVCalc.rv_of_ne hf,residueLift,dif_neg hc]
    change some (puiseuxUnitLeadingTerm (Units.mk0 (puiseuxConstant c) hf)) = _
    congr 1
    apply Prod.ext
    · change Multiplicative.ofAdd (puiseuxConstant c : HahnSeries ℚ ℂ).order = 1
      rw [puiseuxConstant_coe]
      simp [HahnSeries.C,order_single hc]
    · apply Units.ext
      change (puiseuxConstant c : HahnSeries ℚ ℂ).leadingCoeff = c
      rw [puiseuxConstant_coe]
      exact leadingCoeff_of_single

theorem normal_value (r : RVCalc.RV v) :
    RVCalc.vrv v r = Multiplicative.ofAdd (OrderDual.toDual (value (rvNormalEquiv r))) := by
  cases r with
  | none => rfl
  | some r =>
    induction r using Quotient.inductionOn' with
    | h u =>
      change v (u : PuiseuxSeries ℂ) = Multiplicative.ofAdd
        (OrderDual.toDual (((u : PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).order : WithTop ℚ))
      change Multiplicative.ofAdd (((u : PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).orderTop) = _
      rw [←order_eq_orderTop_of_ne_zero (puiseuxUnit_coe_ne_zero u)]
      rfl

theorem normal_residueCode_constant (c : ℂ) :
    rvNormalEquiv (ConcreteRV.residueCode v (constantResidue c)) = residueLift c := by
  have he := ConcreteRV.residueCode_reduction v (constantInteger c)
  change ConcreteRV.residueCode v (IsLocalRing.residue v.valuationSubring (constantInteger c)) = _ at he
  rw [constantResidue,RingHom.comp_apply,he]
  by_cases hc : c = 0
  · simp [constantInteger,hc,residueLift,rvNormalEquiv,_root_.Equiv.optionCongr]
  · rw [if_pos (by simpa [constantInteger] using (constant_valuation c).trans (if_neg hc))]
    exact normal_constant c

theorem constantResidue_surjective : Function.Surjective constantResidue := by
  intro r
  by_cases hr : r = 0
  · exact ⟨0,by simpa only [map_zero] using hr.symm⟩
  · let q := ConcreteRV.residueCode v r
    have hq : RVCalc.vrv v q = 1 := ConcreteRV.value_residueCode v hr
    have hval : value (rvNormalEquiv q) = 0 := by
      rw [normal_value] at hq
      exact congrArg (fun a : Multiplicative (WithTop ℚ)ᵒᵈ => OrderDual.ofDual a.toAdd) hq
    cases hn : rvNormalEquiv q with
    | none => simp [hn,value] at hval
    | some u =>
      have hu : u.1 = 1 := by
        apply Multiplicative.toAdd.injective
        exact WithTop.coe_injective (by simpa [hn,value] using hval)
      refine ⟨(u.2 : ℂ),?_⟩
      apply ConcreteRV.residueCode_injective v
      apply rvNormalEquiv.injective
      rw [normal_residueCode_constant]
      change residueLift (u.2 : ℂ) = rvNormalEquiv q
      rw [hn]
      simp only [residueLift,Units.ne_zero,↓reduceDIte]
      congr 1
      exact Prod.ext hu.symm (Units.ext rfl)

def constantResidueEquiv : ℂ ≃+* ConcreteRV.Residue v :=
  RingEquiv.ofBijective constantResidue ⟨constantResidue.injective,constantResidue_surjective⟩

theorem normal_residueCode (r : ConcreteRV.Residue v) :
    rvNormalEquiv (ConcreteRV.residueCode v r) = residueLift (constantResidueEquiv.symm r) := by
  obtain ⟨c,rfl⟩ := constantResidue_surjective r
  change _ = residueLift (constantResidueEquiv.symm (constantResidueEquiv c))
  rw [RingEquiv.symm_apply_apply]
  exact normal_residueCode_constant c

end DiamondIntegral.Section5.PuiseuxOriginal
