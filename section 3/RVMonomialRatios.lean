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

theorem integerCharacter_sub {ι G : Type} [Fintype ι] [CommGroup G]
    (e f : ι → ℤ) (x : ι → G) : integerCharacter (e - f) x = integerCharacter e x / integerCharacter f x := by
  simp only [integerCharacter,Pi.sub_apply,zpow_sub,div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_inv_distrib]

theorem rvMonomial_ratio_units (T U : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) / U.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) =
      (rvMonomialCoefficient T a r / rvMonomialCoefficient U a r) *
        ((integerCharacter (fun i => T.powers i - U.powers i) x : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M) := by
  rw [rvMonomial_rawEval_units,rvMonomial_rawEval_units,mul_div_mul_comm]
  have he : (fun i => T.powers i - U.powers i) = (fun i => T.powers i) - (fun i => U.powers i) := rfl
  rw [he,integerCharacter_sub]
  simp only [div_eq_mul_inv,Units.val_mul,Units.val_inv_eq_inv_val]

/-- A residue-scaled character with nonzero coefficient has a fixed value. -/
theorem scaled_residue_character_values_finite (c : CanonicalRV.RVSort M) (hc : c ≠ 0)
    (e : Fin n → ℤ) (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ))
    (hA : ∀ x ∈ A, ValuedModelMap.inK (c * ((integerCharacter e x : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M))) :
    (characterValueImage (rvUnitValueHom (M := M)) A e).Finite := by
  let u : (CanonicalRV.RVSort M)ˣ := Units.mk0 c hc
  apply (Set.finite_singleton ((rvUnitValueHom u)⁻¹)).subset
  rintro _ ⟨x,hx,rfl⟩
  change rvUnitValueHom (integerCharacter e x) = (rvUnitValueHom u)⁻¹
  have hv := (rvUnitValue_eq_one_iff_inK (u * integerCharacter e x)).mpr (hA x hx)
  rw [map_mul] at hv
  apply mul_left_cancel (a := rvUnitValueHom u)
  exact hv.trans (mul_inv_cancel _).symm

theorem rvMonomial_ratio_character_values_finite (T U : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (hT : rvMonomialCoefficient T a r ≠ 0) (hU : rvMonomialCoefficient U a r ≠ 0)
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ))
    (hA : ∀ x ∈ A, ValuedModelMap.inK
      (T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) / U.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)))) :
    (characterValueImage (rvUnitValueHom (M := M)) A (fun i => T.powers i - U.powers i)).Finite := by
  apply scaled_residue_character_values_finite (rvMonomialCoefficient T a r / rvMonomialCoefficient U a r) (div_ne_zero hT hU)
  intro x hx
  rw [← rvMonomial_ratio_units]
  exact hA x hx
end DiamondIntegral.Section3
