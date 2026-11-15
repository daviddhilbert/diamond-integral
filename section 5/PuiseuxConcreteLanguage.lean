import «section 5».PuiseuxConcreteRVOperations

/-! An unconditional isomorphism between the ordinary quotient-valued
structure and the canonical original Puiseux RV-language structure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section6

local instance sourceStructure : LRV.Structure (ConcreteValued.Carrier v) := ConcreteValued.nativeStructure v
local instance targetStructure : LRV.Structure Carrier := canonicalInterpret

def concreteCarrierNormal : ConcreteValued.Carrier v ≃ Carrier :=
  _root_.Equiv.sumCongr (_root_.Equiv.refl _) rvNormalEquiv

theorem concreteCarrierNormal_inl (f : PuiseuxSeries ℂ) : concreteCarrierNormal (.inl f) = .inl f := rfl

theorem concreteCarrierNormal_inr (q : RVCalc.RV v) : concreteCarrierNormal (.inr q) = .inr (rvNormalEquiv q) := rfl

theorem concreteCarrierNormal_vf (x : ConcreteValued.Carrier v) :
    vfPart (concreteCarrierNormal x) = ConcreteValued.vfValue v x := by cases x <;> rfl

theorem concreteCarrierNormal_rv (x : ConcreteValued.Carrier v) :
    rvPart (concreteCarrierNormal x) = rvNormalEquiv (ConcreteValued.rvValue v x) := by cases x <;> rfl

theorem concreteCarrierNormal_vfSort (x : ConcreteValued.Carrier v) :
    inVF (concreteCarrierNormal x) ↔ ConcreteValued.hasSort v .vf x := by cases x <;> rfl

theorem concreteCarrierNormal_rvSort (x : ConcreteValued.Carrier v) :
    ¬ inVF (concreteCarrierNormal x) ↔ ConcreteValued.hasSort v .rv x := by cases x <;> simp [concreteCarrierNormal,inVF,ConcreteValued.hasSort]

theorem concreteCarrierNormal_sort (s : SortTag) (x : ConcreteValued.Carrier v) :
    @sortEval Carrier interpret s (concreteCarrierNormal x) ↔ ConcreteValued.hasSort v s x := by
  cases s
  · exact concreteCarrierNormal_vfSort x
  · exact concreteCarrierNormal_rvSort x

theorem concreteCarrierNormal_function {n : ℕ} (f : Fn n) (x : Fin n → ConcreteValued.Carrier v) :
    concreteCarrierNormal (ConcreteValued.functionValue v f x) = function f (concreteCarrierNormal ∘ x) := by
  cases f <;> simp only [ConcreteValued.functionValue,function,concreteCarrierNormal_inl,
    concreteCarrierNormal_inr,Function.comp_apply,concreteCarrierNormal_vf,concreteCarrierNormal_rv]
  all_goals try rfl
  · exact congrArg Sum.inr (congrArg Option.some (map_one (puiseuxRVUnitEquiv (k := ℂ))))
  · exact congrArg Sum.inr (normal_rvMul _ _)
  · exact congrArg Sum.inr (normal_rvInv _)
  · exact congrArg Sum.inr (normal_addResidue _ _)
  · exact congrArg Sum.inr (normal_negResidue _)

def concreteLanguageEquiv : ConcreteValued.Carrier v ≃[LRV] Carrier where
  toEquiv := concreteCarrierNormal
  map_fun' f x := by
    change concreteCarrierNormal (if ∀ i, ConcreteValued.hasSort v (Fn.argSort f i) (x i)
      then ConcreteValued.functionValue v f x else ConcreteValued.zeroOf v (Fn.resSort f)) =
      if ∀ i, @sortEval Carrier interpret (Fn.argSort f i) (concreteCarrierNormal (x i))
      then function f (concreteCarrierNormal ∘ x) else @CanonicalStructure.sortZero Carrier interpret (Fn.resSort f)
    have hg : (∀ i, @sortEval Carrier interpret (Fn.argSort f i) (concreteCarrierNormal (x i))) ↔
        ∀ i, ConcreteValued.hasSort v (Fn.argSort f i) (x i) :=
      forall_congr' (fun i => concreteCarrierNormal_sort _ _)
    by_cases h : ∀ i, ConcreteValued.hasSort v (Fn.argSort f i) (x i)
    · simpa only [if_pos h,if_pos (hg.mpr h)] using concreteCarrierNormal_function f x
    · simp only [if_neg h,if_neg (fun hx => h (hg.mp hx))]
      cases Fn.resSort f <;> rfl
  map_rel' r x := by
    cases r with
    | memVF => exact concreteCarrierNormal_vfSort (x 0)
    | memRV => exact concreteCarrierNormal_rvSort (x 0)
    | memUnits =>
      change (¬ inVF (concreteCarrierNormal (x 0)) ∧ value (rvPart (concreteCarrierNormal (x 0))) = 0) ↔
        (ConcreteValued.hasSort v .rv (x 0) ∧ RVCalc.vrv v (ConcreteValued.rvValue v (x 0)) = 1)
      rw [concreteCarrierNormal_rvSort,concreteCarrierNormal_rv,normal_value_one]
    | rvLe =>
      change ((∀ i, ¬ inVF (concreteCarrierNormal (x i))) ∧
        ¬ inVF (concreteCarrierNormal (x 0)) ∧ ¬ inVF (concreteCarrierNormal (x 1)) ∧
        value (rvPart (concreteCarrierNormal (x 0))) ≤ value (rvPart (concreteCarrierNormal (x 1)))) ↔
        ((∀ i, ConcreteValued.hasSort v .rv (x i)) ∧
        RVCalc.vrv v (ConcreteValued.rvValue v (x 1)) ≤ RVCalc.vrv v (ConcreteValued.rvValue v (x 0)))
      simp only [concreteCarrierNormal_rvSort,concreteCarrierNormal_rv,normal_value_le]
      exact ⟨fun h => ⟨h.1,h.2.2.2⟩,fun h => ⟨h.1,h.1 0,h.1 1,h.2⟩⟩

end DiamondIntegral.Section5.PuiseuxOriginal
