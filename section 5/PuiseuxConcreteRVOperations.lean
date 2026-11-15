import «section 5».PuiseuxConcreteResidue

/-! The actual quotient-to-leading-term equivalence preserves every RV
operation, including addition and negation in the residue field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical SpecialTransformations.Section6

theorem raw_residueLift_coefficient (c : ℂ) : residue (residueLift c) = c := by
  by_cases hc : c = 0 <;> simp [residueLift, residue, hc]

theorem raw_residueLift_residue (r : RV) (hr : inResidue r) : residueLift (residue r) = r := by
  cases r with
  | none => simp [residueLift, residue]
  | some u =>
    change u.1 = 1 at hr
    simp only [residue, hr, ↓reduceIte, residueLift, Units.ne_zero, ↓reduceDIte]
    congr 2
    · exact hr.symm
    · exact Units.ext rfl

theorem raw_residueLift_mul (c d : ℂ) : residueLift (c * d) = rvMul (residueLift c) (residueLift d) := by
  by_cases hc : c = 0
  · simp [residueLift, hc, rvMul]
  by_cases hd : d = 0
  · simp [residueLift, hc, hd, rvMul]
  simp only [residueLift, hc, hd, mul_ne_zero hc hd, ↓reduceDIte, rvMul]
  congr 2
  · simp
  · exact Units.ext rfl

theorem raw_residueLift_inResidue (c : ℂ) : inResidue (residueLift c) := by
  by_cases hc : c = 0 <;> simp [residueLift, hc, inResidue]

theorem raw_residueLift_add (c d : ℂ) : residueLift (c + d) = kAdd (residueLift c) (residueLift d) := by
  rw [kAdd, if_pos ⟨raw_residueLift_inResidue c, raw_residueLift_inResidue d⟩,
    raw_residueLift_coefficient, raw_residueLift_coefficient]


theorem normal_inResidue (q : RVCalc.RV v) :
    inResidue (rvNormalEquiv q) ↔ q ∈ Set.range (ConcreteRV.residueCode v) := by
  constructor
  · intro h
    refine ⟨constantResidue (residue (rvNormalEquiv q)),?_⟩
    apply rvNormalEquiv.injective
    rw [normal_residueCode_constant]
    exact raw_residueLift_residue _ h
  · rintro ⟨r,rfl⟩
    rw [normal_residueCode]
    exact raw_residueLift_inResidue _

theorem normal_addResidue (q r : RVCalc.RV v) :
    rvNormalEquiv (ConcreteValued.addResidue v q r) = kAdd (rvNormalEquiv q) (rvNormalEquiv r) := by
  by_cases hq : q ∈ Set.range (ConcreteRV.residueCode v)
  · by_cases hr : r ∈ Set.range (ConcreteRV.residueCode v)
    · obtain ⟨a,rfl⟩ := hq
      obtain ⟨b,rfl⟩ := hr
      rw [ConcreteValued.addResidue_code,normal_residueCode,normal_residueCode,normal_residueCode]
      rw [map_add]
      exact raw_residueLift_add _ _
    · rw [ConcreteValued.addResidue,if_neg (fun h => hr h.2),kAdd,
        if_neg (fun h => hr ((normal_inResidue r).mp h.2))]
      rfl
  · rw [ConcreteValued.addResidue,if_neg (fun h => hq h.1),kAdd,
      if_neg (fun h => hq ((normal_inResidue q).mp h.1))]
    rfl

theorem normal_negResidue (q : RVCalc.RV v) :
    rvNormalEquiv (ConcreteValued.negResidue v q) = kNeg (rvNormalEquiv q) := by
  by_cases hq : q ∈ Set.range (ConcreteRV.residueCode v)
  · obtain ⟨a,rfl⟩ := hq
    rw [ConcreteValued.negResidue_code,normal_residueCode,normal_residueCode,map_neg]
    rw [kNeg,if_pos (raw_residueLift_inResidue _),raw_residueLift_coefficient]
  · rw [ConcreteValued.negResidue,if_neg hq,kNeg,
      if_neg (fun h => hq ((normal_inResidue q).mp h))]
    rfl

theorem normal_rvMul (q r : RVCalc.RV v) :
    rvNormalEquiv (RVCalc.rvMul v q r) = rvMul (rvNormalEquiv q) (rvNormalEquiv r) := by
  cases q <;> cases r <;>
    simp [rvNormalEquiv,_root_.Equiv.optionCongr,RVCalc.rvMul,rvMul,map_mul]

theorem normal_rvInv (q : RVCalc.RV v) :
    rvNormalEquiv (q.map Inv.inv) = rvInv (rvNormalEquiv q) := by
  cases q <;> simp [rvNormalEquiv,_root_.Equiv.optionCongr,rvInv,map_inv]

theorem normal_value_one (q : RVCalc.RV v) :
    RVCalc.vrv v q = 1 ↔ value (rvNormalEquiv q) = 0 := by
  rw [normal_value]
  rfl

theorem normal_value_le (q r : RVCalc.RV v) :
    RVCalc.vrv v r ≤ RVCalc.vrv v q ↔ value (rvNormalEquiv q) ≤ value (rvNormalEquiv r) := by
  rw [normal_value,normal_value]
  rfl

end DiamondIntegral.Section5.PuiseuxOriginal
