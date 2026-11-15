import RVClassEquality
import Mathlib.Algebra.Group.Units.Equiv

/-! Actual quotient RV actions of valuation-preserving field automorphisms. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation-preserving automorphism maps principal units onto themselves. -/
theorem valuedAutomorphism_principalUnits (v : Valuation K Γ₀)
    (σ : K ≃+* K) (hσ : ∀ x, v (σ x) = v x) :
    (RVCalc.principalUnits v).map (Units.mapEquiv σ.toMulEquiv) = RVCalc.principalUnits v := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    change v (σ (w : K) - 1) < 1
    rw [← map_one σ, ← map_sub, hσ]
    exact hw
  · intro hu
    refine ⟨(Units.mapEquiv σ.toMulEquiv).symm u, ?_,
      (Units.mapEquiv σ.toMulEquiv).apply_symm_apply u⟩
    change v (σ.symm (u : K) - 1) < 1
    have hv := hσ (σ.symm (u : K) - 1)
    rw [map_sub, map_one, σ.apply_symm_apply] at hv
    rw [← hv]
    exact hu

/-- The actual multiplicative quotient action on RV units. -/
def valuedRVUnitEquiv (v : Valuation K Γ₀)
    (σ : K ≃+* K) (hσ : ∀ x, v (σ x) = v x) :
    RVCalc.RVUnit v ≃* RVCalc.RVUnit v :=
  QuotientGroup.congr _ _ (Units.mapEquiv σ.toMulEquiv)
    (valuedAutomorphism_principalUnits v σ hσ)

theorem valuedRVUnitEquiv_mk (v : Valuation K Γ₀)
    (σ : K ≃+* K) (hσ : ∀ x, v (σ x) = v x) (u : Kˣ) :
    valuedRVUnitEquiv v σ hσ (QuotientGroup.mk' (RVCalc.principalUnits v) u) =
      QuotientGroup.mk' (RVCalc.principalUnits v) (Units.mapEquiv σ.toMulEquiv u) := rfl

/-- Include the RV zero/infinity point. -/
def valuedRVEquiv (v : Valuation K Γ₀)
    (σ : K ≃+* K) (hσ : ∀ x, v (σ x) = v x) : RVCalc.RV v ≃ RVCalc.RV v :=
  Equiv.optionCongr (valuedRVUnitEquiv v σ hσ).toEquiv

theorem valuedRVEquiv_rv (v : Valuation K Γ₀)
    (σ : K ≃+* K) (hσ : ∀ x, v (σ x) = v x) (x : K) :
    valuedRVEquiv v σ hσ (RVCalc.rv v x) = RVCalc.rv v (σ x) := by
  by_cases hx : x = 0
  · subst x
    simp [valuedRVEquiv, RVCalc.rv_zero]
  · rw [RVCalc.rv_of_ne hx, RVCalc.rv_of_ne ((map_ne_zero σ).mpr hx)]
    change some (valuedRVUnitEquiv v σ hσ
      (QuotientGroup.mk' (RVCalc.principalUnits v) (Units.mk0 x hx))) = _
    rw [valuedRVUnitEquiv_mk]
    congr 2
    exact Units.ext rfl

end DiamondIntegral.Section5
