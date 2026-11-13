import «section 3».GammaGroundRVDefinableSubgroup
import «section 3».MonomialValueKernels
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {G Γ : Type} [CommGroup G] [CommGroup Γ] {n : ℕ}

/-- Equality of weight tuples modulo old values supplies actual old
coefficients, without choosing any representative of the input weights. -/
theorem monomial_coefficients_of_quotient_weights (v : G →* Γ) (S : Subgroup G)
    (a b : Fin n → Γ) (C : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i, QuotientGroup.mk' (S.map v) (b i) =
      integerMonomialMap C (fun j => QuotientGroup.mk' (S.map v) (a j)) i) :
    ∃ c : Fin n → G, (∀ i, c i ∈ S) ∧ b = (fun i => v (c i)) * integerMonomialMap C a := by
  let q := QuotientGroup.mk' (S.map v)
  have hm : ∀ i, b i * (integerMonomialMap C a i)⁻¹ ∈ S.map v := by
    intro i
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b i * (integerMonomialMap C a i)⁻¹) = 1
    rw [map_mul,map_inv]
    rw [congrFun (monomial_map_value q C a) i,h i]
    exact mul_inv_cancel _
  choose c hc hv using fun i => Subgroup.mem_map.mp (hm i)
  refine ⟨c,hc,?_⟩
  funext i
  change b i = v (c i) * integerMonomialMap C a i
  rw [hv i]
  simp [mul_assoc]

end DiamondIntegral.Section3
