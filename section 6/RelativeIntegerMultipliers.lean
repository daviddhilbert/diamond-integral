import «section 6».RelativeRVAnchors
import Section3.MeanInBalls

/-! The inactive weighted row multiplier cannot vanish on two equal
nonzero RV fibres when its integer coefficients differ. Residue
characteristic zero supplies the exact value of their difference. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n : ℕ}

theorem vf_intCast_valuation_one (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ v x ≤ v y) (z : ℤ) (hz : z ≠ 0) :
    v (z : VF M) = 1 := by
  cases z with
  | ofNat k =>
    have hk : k ≠ 0 := by intro h; subst k; exact hz rfl
    change v ((k : ℤ) : VF M) = 1
    rw [Int.cast_natCast]
    exact Barycentre.natCast_value_one v hv h00 k hk
  | negSucc k =>
    rw [Int.cast_negSucc,v.map_neg]
    exact Barycentre.natCast_value_one v hv h00 (k+1) (Nat.succ_ne_zero k)

theorem vf_int_smul_valuation (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ v x ≤ v y) (z : ℤ) (hz : z ≠ 0) (x : VF M) :
    v (z • x) = v x := by
  rw [zsmul_eq_mul,v.map_mul,vf_intCast_valuation_one h00 v hv z hz,one_mul]

theorem equal_rv_integer_multiplier_nonzero (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ v x ≤ v y)
    (x y : VF M) (hx : x ≠ 0) (hRV : RVCalc.rv v y = RVCalc.rv v x)
    (p q : ℤ) (hpq : p ≠ q) : q • y - p • x ≠ 0 := by
  have hlt := (rv_eq_centre_iff v hx y).mp hRV
  have hSmall := valuation_zsmul_lt v hlt q
  have hq : q-p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hValue := vf_int_smul_valuation h00 v hv (q-p) hq x
  intro h
  have heq : q • (y-x) = -((q-p) • x) := by
    have hxy := sub_eq_zero.mp h
    rw [smul_sub,sub_smul,hxy]
    abel
  have hNeg : v (-((q-p) • x)) = v ((q-p) • x) := v.map_neg _
  have hSame : v (-((q-p) • x)) = v x := hNeg.trans hValue
  exact (not_lt_of_ge hSame.ge) (heq ▸ hSmall)

theorem relative_diagonal_row_fixes_coordinate (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF M) G) (hv : ∀ x y : VF M,VFValued.predV x y ↔ v x ≤ v y)
    (j : Fin n) (p q : ℤ) (hpq : p ≠ q) (H : MvPolynomial (Fin (n+n)) (VF M))
    (hH : H = (q • X (productRight n n j) - p • X (productLeft n n j)) *
      relativeDiagonalPolynomial (VF M) n j)
    (a : Fin (n+n) → VF M) (ha : a (productLeft n n j) ≠ 0)
    (hRV : RVCalc.rv v (a (productRight n n j)) = RVCalc.rv v (a (productLeft n n j)))
    (hRoot : H.eval a = 0) : a (productRight n n j) = a (productLeft n n j) := by
  have hMul := equal_rv_integer_multiplier_nonzero h00 v hv _ _ ha hRV p q hpq
  rw [hH,(MvPolynomial.eval a).map_mul,(MvPolynomial.eval a).map_sub,
    _root_.map_zsmul (MvPolynomial.eval a),_root_.map_zsmul (MvPolynomial.eval a),
    MvPolynomial.eval_X,MvPolynomial.eval_X] at hRoot
  have hD := (mul_eq_zero.mp hRoot).resolve_left hMul
  change (MvPolynomial.eval a) (X (productRight n n j) - X (productLeft n n j)) = 0 at hD
  rw [(MvPolynomial.eval a).map_sub,MvPolynomial.eval_X,MvPolynomial.eval_X] at hD
  exact sub_eq_zero.mp hD

end DiamondIntegral.Section6
