import «section 6».RelativeIntegerMultipliers
import Section7.ResidueCharacteristic

/-! The weighted local polynomial lift retains every inactive VF
coordinate exactly. Its row coefficients are forced to differ by the
nonzero partial Jacobian at a genuinely diagonal fibre anchor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language MvPolynomial IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n : ℕ}

theorem exists_weighted_relative_polynomial_lift
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ v x ≤ v y)
    (E : Subfield (VF M)) (t s : Fin n → RVCalc.RV v)
    (ht : ∀ j,t j ≠ none) (hs : ∀ j,s j ≠ none) (i : Fin n)
    (hFixed : ∀ j,j ≠ i → t j = s j)
    (α β : Fin n → G) (F Q : Fin n → MvPolynomial (Fin (n+n)) E)
    (hF : ∀ j,IsGammaPolynomial v (fun k => RVCalc.vrv v (productTuple t s k)) (α j) ((F j).map E.subtype))
    (hQ : ∀ j,IsGammaPolynomial v (fun k => RVCalc.vrv v (productTuple t s k)) (β j) ((Q j).map E.subtype))
    (hFR : ∀ j,IsResidueRoot v (productTuple t s) (α j) ((F j).map E.subtype))
    (hQR : ∀ j,IsResidueRoot v (productTuple t s) (β j) ((Q j).map E.subtype))
    (hFD : ∀ j,¬ IsResidueRoot v (productTuple t s)
      (α j / RVCalc.vrv v (productTuple t s (productRight n n j)))
        (pderiv (productRight n n j) ((F j).map E.subtype)))
    (hQD : ∀ j,¬ IsResidueRoot v (productTuple t s)
      (β j / RVCalc.vrv v (productTuple t s (productLeft n n j)))
        (pderiv (productLeft n n j) ((Q j).map E.subtype)))
    (hFO : ∀ j k,j ≠ k → pderiv (productRight n n k) ((F j).map E.subtype) = 0)
    (hQO : ∀ j k,j ≠ k → pderiv (productLeft n n k) ((Q j).map E.subtype) = 0)
    (hDiag : ∀ j,j ≠ i → F j = relativeDiagonalPolynomial E n j ∧ Q j = relativeDiagonalPolynomial E n j) :
    ∃ (H : Fin n → MvPolynomial (Fin (n+n)) E) (w : Fin n → G),
      let W := fun j => (H j).map E.subtype
      (∀ j,IsGammaPolynomial v (fun k => RVCalc.vrv v (productTuple t s k)) (w j) (W j)) ∧
      ¬ IsResidueRoot v (productTuple t s) (jacobianValue (fun j => RVCalc.vrv v (t j)) w)
        (partialJacobianPolynomial (productLeft n n) W) ∧
      ¬ IsResidueRoot v (productTuple t s) (jacobianValue (fun j => RVCalc.vrv v (s j)) w)
        (partialJacobianPolynomial (productRight n n) W) ∧
      FibreBijection v {p | ∀ j,(W j).eval (productTuple p.1 p.2) = 0} t s ∧
      ∀ a ∈ RVFibre v t,∀ b ∈ RVFibre v s,
        (∀ j,(W j).eval (productTuple a b) = 0) → ∀ j,j ≠ i → b j = a j := by
  letI : IsAlgClosed (VF M) := VFAlgClosed.isAlgClosed_vfType
  letI : CharZero (ResidueField v.valuationSubring) := residueField_charZero_of_model00 v hv h00
  obtain ⟨H,w,hW,hJL,hJR,hLift,hRow⟩ := exists_weighted_polynomial_system_with_row_formula
    v E t s ht hs α β F Q hF hQ hFR hQR hFD hQD hFO hQO
  let W := fun j => (H j).map E.subtype
  obtain ⟨z,hz,hzFixed⟩ := exists_relative_rv_anchor v t s i hFixed
  have hu (j : Fin (n+n)) : productTuple t s j ≠ none := by
    obtain ⟨k,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n+n)).surjective j
    cases k with
    | inl j =>
      change productTuple t s (productLeft n n j) ≠ none
      simpa only [productTuple_left] using ht j
    | inr j =>
      change productTuple t s (productRight n n j) ≠ none
      simpa only [productTuple_right] using hs j
  have hγ (j : Fin (n+n)) : RVCalc.vrv v (productTuple t s j) ≠ 0 := by
    rw [← rvFibre_value v hz j]
    exact v.ne_zero_iff.mpr (fun he => hu j ((hz j).symm.trans (he ▸ RVCalc.rv_zero)))
  have hJGamma := isGammaPolynomial_partialJacobian v hγ hW (productRight n n)
  have hJValue := (not_residueRoot_iff_eval_eq v hu hJGamma).mp hJR z hz
  have hJNonzero : (partialJacobianPolynomial (productRight n n) W).eval z ≠ 0 := by
    apply v.ne_zero_iff.mp
    rw [hJValue]
    exact hJGamma.2.1
  have hFactor (j : Fin n) (hj : j ≠ i) : ∃ p q : ℤ,p ≠ q ∧
      W j = (q • X (productRight n n j) - p • X (productLeft n n j)) *
        relativeDiagonalPolynomial (VF M) n j := by
    obtain ⟨p,q,hRow⟩ := hRow j
    rw [(hDiag j hj).1,(hDiag j hj).2] at hRow
    have hFactorE := relative_diagonal_row_factor (K := E) j p q (H j) hRow
    have hFactorVF : W j = (q • X (productRight n n j) - p • X (productLeft n n j)) *
        relativeDiagonalPolynomial (VF M) n j := by
      change (MvPolynomial.map E.subtype) (H j) = _
      rw [hFactorE]
      simp only [(MvPolynomial.map E.subtype).map_mul,(MvPolynomial.map E.subtype).map_sub,
        _root_.map_zsmul (MvPolynomial.map E.subtype),MvPolynomial.map_X E.subtype,relativeDiagonalPolynomial_map]
    refine ⟨p,q,relative_diagonal_row_coefficients_ne j p q (W j) hFactorVF z (hzFixed j hj) ?_,hFactorVF⟩
    obtain ⟨k,hk⟩ := polynomial_partial_row_regular W (productRight n n) z hJNonzero j
    exact ⟨productRight n n k,hk⟩
  have hJL' : ¬ IsResidueRoot v (productTuple t s) (jacobianValue (fun j => RVCalc.vrv v (t j)) w)
      (partialJacobianPolynomial (productLeft n n) W) := by
    simpa only [productTuple_left] using hJL
  have hJR' : ¬ IsResidueRoot v (productTuple t s) (jacobianValue (fun j => RVCalc.vrv v (s j)) w)
      (partialJacobianPolynomial (productRight n n) W) := by
    simpa only [productTuple_right] using hJR
  refine ⟨H,w,hW,hJL',hJR',hLift,fun a ha b hb hRoot j hj => ?_⟩
  obtain ⟨p,q,hpq,hFactor⟩ := hFactor j hj
  have ha₀ : a j ≠ 0 := by
    intro he
    exact ht j ((ha j).symm.trans (he ▸ RVCalc.rv_zero))
  have ha' : productTuple a b (productLeft n n j) ≠ 0 := by
    simpa only [productTuple_left] using ha₀
  have hRV' : RVCalc.rv v (productTuple a b (productRight n n j)) =
      RVCalc.rv v (productTuple a b (productLeft n n j)) := by
    simp only [productTuple_left,productTuple_right]
    exact (hb j).trans ((hFixed j hj).symm.trans (ha j).symm)
  have hEq := relative_diagonal_row_fixes_coordinate h00 v hv j p q hpq (W j) hFactor
    (productTuple a b) ha' hRV' (hRoot j)
  simpa only [productTuple_left,productTuple_right] using hEq

end DiamondIntegral.Section6
