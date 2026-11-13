import «section 3».RVMonomialCharacters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem integerCharacter_value_eq {G Γ : Type} [CommGroup G] [CommGroup Γ]
    (v : G →* Γ) (e : Fin n → ℤ) (x y : Fin n → G) (hxy : ∀ i, v (x i) = v (y i)) :
    v (integerCharacter e x) = v (integerCharacter e y) := by
  simp only [integerCharacter,map_prod,map_zpow]
  simp_rw [hxy]

theorem rvMonomial_absolute_depends_on_values (T : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) :
    RVOperations.absoluteHom (T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
      RVOperations.absoluteHom (T.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))) := by
  have hc := integerCharacter_value_eq (rvUnitValueHom (M := M)) (fun i => T.powers i) x y hxy
  have ha := (rvUnitValue_eq_iff_absolute_eq _ _).mp hc
  rw [rvMonomial_rawEval_units,rvMonomial_rawEval_units,map_mul,map_mul,ha]

theorem rvMonomial_rawEval_ne_zero (T : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (hc : rvMonomialCoefficient T a r ≠ 0) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) ≠ 0 := by
  rw [rvMonomial_rawEval_units]
  exact mul_ne_zero hc (Units.ne_zero _)
end DiamondIntegral.Section3
