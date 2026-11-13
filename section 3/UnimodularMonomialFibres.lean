import «section 3».IntegerMonomialCosets
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G Γ : Type} [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]

/-- A unimodular affine monomial map carries each full value fibre onto
the full value fibre of its image. The inverse is an integral monomial. -/
theorem affineMonomial_full_value_fibre_solve (v : G →* Γ) (A : Matrix ι ι ℤ) (hA : IsUnit A.det)
    (c x y : ι → G)
    (hvalue : (fun i => v (y i)) = fun i => v ((c * integerMonomialMap A x) i)) :
    ∃ u : ι → G, (fun i => v (u i)) = (fun i => v (x i)) ∧ c * integerMonomialMap A u = y := by
  let u := integerMonomialMap A⁻¹ (c⁻¹*y)
  have hu : c * integerMonomialMap A u = y := by
    change c * integerMonomialMap A (integerMonomialMap A⁻¹ (c⁻¹*y)) = y
    rw [integerMonomialMap_comp,Matrix.mul_nonsing_inv A hA,integerMonomialMap_one,mul_inv_cancel_left]
  have hc : (fun i => v ((c⁻¹*y) i)) = integerMonomialMap A (fun i => v (x i)) := by
    funext i
    change v ((c i)⁻¹*y i) = integerMonomialMap A (fun i => v (x i)) i
    rw [map_mul,map_inv,congrFun hvalue i]
    change (v (c i))⁻¹ * v (c i * integerMonomialMap A x i) = _
    rw [map_mul,inv_mul_cancel_left]
    exact congrFun (monomial_map_value v A x) i
  have hv : (fun i => v (u i)) = fun i => v (x i) := by
    change (fun i => v (integerMonomialMap A⁻¹ (c⁻¹*y) i)) = _
    rw [monomial_map_value,hc,integerMonomialMap_comp,Matrix.nonsing_inv_mul A hA,integerMonomialMap_one]
  exact ⟨u,hv,hu⟩
end DiamondIntegral.Section3
