import «section 3».IntegerMonomialCosets
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G Γ : Type} [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]

/-- Unimodular affine monomials preserve and reflect equality of full
value tuples. This is the exact kernel condition for Gamma descent. -/
theorem affineMonomial_value_kernel_iff (v : G →* Γ) (A : Matrix ι ι ℤ) (hA : IsUnit A.det)
    (c x y : ι → G) :
    (fun i => v ((c * integerMonomialMap A x) i)) = (fun i => v ((c * integerMonomialMap A y) i)) ↔
      (fun i => v (x i)) = fun i => v (y i) := by
  let e : (ι → Γ) ≃* (ι → Γ) := integerMonomialEquiv A A⁻¹ (Matrix.mul_nonsing_inv A hA) (Matrix.nonsing_inv_mul A hA)
  have he (z : ι → G) : (fun i => v ((c * integerMonomialMap A z) i)) =
      (fun i => v (c i)) * e (fun i => v (z i)) := by
    funext i
    exact (map_mul v _ _).trans (congrArg (fun t => v (c i)*t) (congrFun (monomial_map_value v A z) i))
  constructor
  · intro h
    apply e.injective
    apply mul_left_cancel (a := fun i => v (c i))
    exact (he x).symm.trans (h.trans (he y))
  · intro h
    exact (he x).trans ((congrArg (fun z => (fun i => v (c i))*e z) h).trans (he y).symm)
end DiamondIntegral.Section3
