import «section 5».FiniteRootProjection
import «section 5».PuiseuxRVLanguage

/-! Finite Kummer coordinates for actual RV lines, including their common
absorbing zero. The framing is auxiliary data, never a language symbol. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

def linePoint (q : ℚ) (c : ℂ) : RV :=
  if hc : c = 0 then none else some (Multiplicative.ofAdd q, Units.mk0 c hc)

def lineCoefficient : RV → ℂ
  | none => 0
  | some u => u.2

def ValueLine (q : ℚ) := {r : RV // r = none ∨ value r = q}

theorem lineCoefficient_point (q : ℚ) (c : ℂ) : lineCoefficient (linePoint q c) = c := by
  by_cases hc : c = 0 <;> simp [linePoint, lineCoefficient, hc]

theorem linePoint_coefficient (q : ℚ) (r : ValueLine q) :
    linePoint q (lineCoefficient r.val) = r.val := by
  rcases r with ⟨r, hr⟩
  cases r with
  | none => simp [linePoint, lineCoefficient]
  | some u =>
    have hq : u.1.toAdd = q := WithTop.coe_injective (hr.resolve_left (by simp))
    simp only [lineCoefficient, linePoint, Units.ne_zero, ↓reduceDIte]
    congr 2
    · exact congrArg Multiplicative.ofAdd hq.symm
    · exact Units.ext rfl

def lineEquiv (q : ℚ) : ℂ ≃ ValueLine q where
  toFun c := ⟨linePoint q c, by by_cases hc : c = 0 <;> simp [linePoint, hc, value]⟩
  invFun r := lineCoefficient r.val
  left_inv := lineCoefficient_point q
  right_inv r := Subtype.ext (linePoint_coefficient q r)

theorem rvAction_linePoint (η : CompatibleRoots ℂ) (q : ℚ) (c : ℂ) :
    rvAction η (linePoint q c) =
      linePoint q ((compatibleRootCharacter η (Multiplicative.ofAdd q) : ℂˣ) * c) := by
  by_cases hc : c = 0
  · simp [linePoint, hc, rvAction, _root_.Equiv.optionCongr]
  · simp only [linePoint, hc, ↓reduceDIte, mul_ne_zero (Units.ne_zero _) hc]
    change some (Multiplicative.ofAdd q, _) = some (Multiplicative.ofAdd q, _)
    congr 2
    exact Units.ext rfl

def weightedAction {n : ℕ} (a : Fin n → ℤ) (ζ : ℂˣ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ((ζ ^ a i : ℂˣ) : ℂ) * x i

theorem weightedAction_one {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℂ) :
    weightedAction a 1 x = x := by ext i; simp [weightedAction]

theorem weightedAction_mul {n : ℕ} (a : Fin n → ℤ) (ζ ξ : ℂˣ) (x : Fin n → ℂ) :
    weightedAction a (ζ * ξ) x = weightedAction a ζ (weightedAction a ξ x) := by
  ext i
  simp [weightedAction, mul_zpow, mul_assoc]

def finiteFrame {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (x : Fin n → ℂ) : Fin n → RV :=
  fun i => linePoint ((a i : ℚ) / (N : ℕ)) (x i)

theorem finiteFrame_injective {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) :
    Function.Injective (finiteFrame N a) := by
  intro x y h
  funext i
  have hi := congrArg (fun r => lineCoefficient (r i)) h
  simpa only [finiteFrame, lineCoefficient_point] using hi

theorem finiteFrame_action {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (η : CompatibleRoots ℂ) (x : Fin n → ℂ) :
    (fun i => rvAction η (finiteFrame N a x i)) =
      finiteFrame N a (weightedAction a (η.val N) x) := by
  funext i
  rw [finiteFrame, rvAction_linePoint, compatibleRootCharacter_fraction]
  rfl

local instance framesStructure : LRV.Structure Carrier := canonicalInterpret

/-- Framing an actual formula over the entire Laurent base gives an invariant
set for every finite multiplier. The proof lifts each multiplier to a proved
compatible system; no inverse-limit surjectivity is assumed. -/
theorem framed_formula_invariant {m n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (φ : LRV.BoundedFormula (Fin m) n) (v : Fin m → Carrier)
    (hv : ∀ i, baseCarrier (v i)) (ζ : rootsOfUnity (N : ℕ) ℂ) (x : Fin n → ℂ) :
    φ.Realize v (fun i => Sum.inr (finiteFrame N a (weightedAction a ζ.val x) i)) ↔
      φ.Realize v (fun i => Sum.inr (finiteFrame N a x i)) := by
  obtain ⟨η, hη⟩ := finiteRootProjection_surjective N ζ
  have he : η.val N = ζ.val := congrArg Subtype.val hη
  have h := original_formula_invariant η φ v hv (finiteFrame N a x)
  have hframe := finiteFrame_action N a η x
  rw [he] at hframe
  simpa only [← hframe] using h

/-- Root changes are equivariant diagonal linear isomorphisms. -/
def frameChange {n : ℕ} (a : Fin n → ℤ) (δ : ℂˣ) : (Fin n → ℂ) ≃ (Fin n → ℂ) where
  toFun := weightedAction a δ
  invFun := weightedAction a δ⁻¹
  left_inv x := by rw [← weightedAction_mul, inv_mul_cancel, weightedAction_one]
  right_inv x := by rw [← weightedAction_mul, mul_inv_cancel, weightedAction_one]

theorem frameChange_equivariant {n : ℕ} (a : Fin n → ℤ) (δ ζ : ℂˣ) (x : Fin n → ℂ) :
    frameChange a δ (weightedAction a ζ x) = weightedAction a ζ (frameChange a δ x) := by
  change weightedAction a δ (weightedAction a ζ x) = _
  rw [← weightedAction_mul, mul_comm δ ζ, weightedAction_mul]
  rfl

end DiamondIntegral.Section5.PuiseuxOriginal
