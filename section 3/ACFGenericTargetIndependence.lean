import «section 3».ACFDefinableRelationFields
import Section4.TupleIndependence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [CompatibleRing K] {n : ℕ}

/-- A two-sided functional definable relation between tuples of equal
arity carries an independent tuple to an independent tuple. -/
theorem acf_definable_bijection_target_independent (E : Subfield K)
    (R : Set (Fin n ⊕ Fin n → K)) (hR : (E : Set K).Definable Language.ring R)
    (x y : Fin n → K) (hxy : Sum.elim x y ∈ R)
    (hu : ∀ z : Fin n → K, Sum.elim x z ∈ R → z = y)
    (hv : ∀ z : Fin n → K, Sum.elim z y ∈ R → z = x)
    (hx : AlgebraicIndependent E x) : AlgebraicIndependent E y := by
  have he := acf_definable_bijection_adjoin_eq E R hR x y hxy hu hv
  have hf : tupleField E x = tupleField E y := by
    rw [tupleField_eq_adjoin,tupleField_eq_adjoin,he]
  apply (tupleField_trdeg_eq_arity_iff E y).mp
  have ht := (tupleField_trdeg_eq_arity_iff E x).mpr hx
  simpa only [hf] using ht

/-- Generic tuples lie in the residue torus, including in arity zero. -/
theorem algebraicallyIndependent_coordinate_ne_zero (E : Subfield K)
    (x : Fin n → K) (hx : AlgebraicIndependent E x) (i : Fin n) : x i ≠ 0 := by
  intro hi
  have hp : MvPolynomial.aeval x (MvPolynomial.X i : MvPolynomial (Fin n) E) = MvPolynomial.aeval x (0 : MvPolynomial (Fin n) E) := by simp [hi]
  exact MvPolynomial.X_ne_zero (R := E) i (hx hp)

end DiamondIntegral.Section3
