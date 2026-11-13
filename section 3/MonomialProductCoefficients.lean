import «section 3».IntegerMonomialCosets
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G Γ α : Type} [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]

/-- A unimodular affine-monomial product presentation that is injective
cannot retain two residue coefficients with the same value tuple. -/
theorem monomialProduct_subsingleton_of_constant_coefficient_values
    (v : G →* Γ) (A : Matrix ι ι ℤ) (hA : IsUnit A.det)
    (c : α → ι → G) (T : Set (ι → Γ)) (x : ι → G) (hx : (fun i => v (x i)) ∈ T)
    (hc : ∀ a b, (fun i => v (c a i)) = fun i => v (c b i))
    (hinj : Function.Injective (fun p : α × {u : ι → G // (fun i => v (u i)) ∈ T} =>
      c p.1 * integerMonomialMap A p.2.val)) : Subsingleton α := by
  let V : (ι → G) →* (ι → Γ) :=
    { toFun := fun y i => v (y i)
      map_one' := funext (fun _ => map_one v)
      map_mul' := fun y z => funext (fun i => map_mul v (y i) (z i)) }
  let e : (ι → G) ≃* (ι → G) := integerMonomialEquiv A A⁻¹ (Matrix.mul_nonsing_inv A hA) (Matrix.nonsing_inv_mul A hA)
  let q : (ι → Γ) ≃* (ι → Γ) := integerMonomialEquiv A A⁻¹ (Matrix.mul_nonsing_inv A hA) (Matrix.nonsing_inv_mul A hA)
  have hnat (y : ι → G) : V (e y) = q (V y) := monomial_map_value v A y
  refine ⟨fun a b => ?_⟩
  let u := e.symm ((c b)⁻¹ * (c a * e x))
  have hu : V u = V x := by
    apply q.injective
    calc
      q (V u) = V (e u) := (hnat u).symm
      _ = (V (c b))⁻¹ * (V (c a) * V (e x)) := by
        rw [show e u = (c b)⁻¹ * (c a * e x) from e.apply_symm_apply _]
        rw [map_mul,map_inv,map_mul]
      _ = V (e x) := by
        funext i
        change (v (c b i))⁻¹ * (v (c a i) * v (e x i)) = v (e x i)
        rw [congrFun (hc b a) i,inv_mul_cancel_left]
      _ = q (V x) := hnat x
  have he : c a * integerMonomialMap A x = c b * integerMonomialMap A u := by
    change c a * e x = c b * e u
    rw [show e u = (c b)⁻¹ * (c a * e x) from e.apply_symm_apply _]
    exact (mul_inv_cancel_left _ _).symm
  have hp := hinj (a₁ := (a,⟨x,hx⟩)) (a₂ := (b,⟨u,by change V u ∈ T; rwa [hu]⟩)) he
  exact congrArg Prod.fst hp
end DiamondIntegral.Section3
