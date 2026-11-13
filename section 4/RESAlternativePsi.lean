import «section 4».RESAlternativeReduction
import «section 4».GammaAlternativeSpecialization
import «section 4».RESPsiGradings

/-! The alternative geometric psi in Remark 4.8 is an actual graded ring
homomorphism on the restricted polynomial source. Its line and open-ray
monomials have the same degree-one-point assignment in the enlarged
quotient. No global RV descent is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAlternativePsi
open RESAlternativeReduction GammaNamesSubgroup GammaFunctionPolynomial GammaDefinableConvolution
open GammaUnboundedSpecialization GammaEulerEvaluation GammaPolynomialGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def psi (B : Base (M := M)) : sourceRing B EulerKind.geometric →+* Ring B :=
  GammaAlternativeSpecialization.specialize B EulerKind.geometric (weightCharacter B) (torusClass B)
    (weighted_torus B)

theorem psi_positive (B : Base (M := M)) (p : sourceRing B EulerKind.geometric)
    (n : ℕ) (hn : n ≠ 0) (f : baseSubring B EulerKind.geometric) (hp : p.val = Polynomial.monomial n f) :
    psi B p = (coefficientEuler B EulerKind.geometric f : Ring B) * torusClass B ^ n :=
  GammaAlternativeSpecialization.specialize_positive B EulerKind.geometric (weightCharacter B) (torusClass B)
    (weighted_torus B) p n hn f hp

theorem psi_point_zero (B : Base (M := M)) (a : additiveNames B) :
    psi B (pointMonomial B EulerKind.geometric 0 a) = weightCharacter B (Multiplicative.ofAdd a) :=
  GammaAlternativeSpecialization.specialize_point_zero B EulerKind.geometric (weightCharacter B) (torusClass B)
    (weighted_torus B) a

theorem psi_point_positive (B : Base (M := M)) (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) :
    psi B (pointMonomial B EulerKind.geometric n a) = torusClass B ^ n := by
  rw [psi_positive B _ n hn _ rfl]
  have he : coefficientEuler B EulerKind.geometric
      (GammaPointAlgebra.pointMonoidHom B EulerKind.geometric (Multiplicative.ofAdd a)) = 1 :=
    EulerFunction.totalEuler_point EulerKind.geometric a.val
  rw [he, Int.cast_one, one_mul]

theorem psi_ray_positive (B : Base (M := M)) (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) :
    psi B (rayMonomial B EulerKind.geometric n hn a) = torusClass B ^ (n - 1) * pointClass B := by
  rw [psi_positive B _ n hn _ rfl]
  have he : coefficientEuler B EulerKind.geometric
      (⟨EulerFunction.ray EulerKind.geometric a.val,
        GammaDefinableConvolution.ray_mem_base B EulerKind.geometric a.val a.property⟩ :
          baseSubring B EulerKind.geometric) = -1 :=
    EulerFunction.totalEuler_ray EulerKind.geometric a.val
  rw [he, Int.cast_neg, Int.cast_one, neg_one_mul]
  have hQ : pointClass B = -torusClass B :=
    eq_neg_of_add_eq_zero_right (torus_plus_point_zero B)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hQ]
  simp only [Nat.succ_sub_one, pow_succ]
  ring

theorem psi_line_positive (B : Base (M := M)) (n : ℕ) (hn : n ≠ 0) :
    psi B (lineMonomial B EulerKind.geometric n hn) = torusClass B ^ (n - 1) * pointClass B := by
  rw [psi_positive B _ n hn _ rfl]
  have he : coefficientEuler B EulerKind.geometric
      (⟨EulerFunction.line EulerKind.geometric,
        GammaDefinableConvolution.line_mem_base B EulerKind.geometric⟩ :
          baseSubring B EulerKind.geometric) = -1 :=
    EulerFunction.totalEuler_line EulerKind.geometric
  rw [he, Int.cast_neg, Int.cast_one, neg_one_mul]
  have hQ : pointClass B = -torusClass B :=
    eq_neg_of_add_eq_zero_right (torus_plus_point_zero B)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hQ]
  simp only [Nat.succ_sub_one, pow_succ]
  ring

theorem groupRingCharacter_mem (B : Base (M := M)) (a : DefinableGammaGroupRing B) :
    GammaUnboundedSpecialization.weightCharacter B (weightCharacter B) a ∈ piece B 0 := by
  rw [show GammaUnboundedSpecialization.weightCharacter B (weightCharacter B) a =
      a.coeff.sum (fun b n => n • weightCharacter B (Multiplicative.ofAdd b)) from
    AddMonoidAlgebra.lift_apply (weightCharacter B) a]
  unfold Finsupp.sum
  apply (piece B 0).sum_mem
  intro b _
  exact (piece B 0).zsmul_mem (weight_mem B b) _

theorem intCast_mem (B : Base (M := M)) (z : ℤ) : (z : Ring B) ∈ piece B 0 := by
  change (coaction B).map (z : Ring B) = Polynomial.monomial 0 (z : Ring B)
  simp

theorem torus_pow_mem (B : Base (M := M)) (n : ℕ) : torusClass B ^ n ∈ piece B n := by
  simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded n (torus_mem B)

theorem psi_mem (B : Base (M := M)) {n : ℕ} {p : sourceRing B EulerKind.geometric}
    (hp : p ∈ unboundedPiece B EulerKind.geometric n) : psi B p ∈ piece B n := by
  have he := (mem_unboundedPiece B EulerKind.geometric p n).mp hp
  by_cases hn : n = 0
  · subst n
    have hg : polynomial B EulerKind.geometric (torusClass B) p =
        (coefficientEuler B EulerKind.geometric (p.val.coeff 0) : Ring B) := by
      change Polynomial.eval₂ _ _ p.val = _
      rw [he, Polynomial.eval₂_monomial, pow_zero, mul_one, Polynomial.coeff_monomial_same]
      rfl
    rw [psi, GammaAlternativeSpecialization.specialize_apply, hg]
    change GammaUnboundedSpecialization.weightCharacter B (weightCharacter B)
      (GammaEndpointProjection.namedEndpoint B EulerKind.geometric (p.val.coeff 0)) +
        (coefficientEuler B EulerKind.geometric (p.val.coeff 0) : Ring B) -
          (coefficientEuler B EulerKind.geometric (p.val.coeff 0) : Ring B) ∈ piece B 0
    rw [add_sub_cancel_right]
    exact groupRingCharacter_mem B _
  · rw [psi_positive B p n hn _ he]
    simpa only [zero_add] using SetLike.mul_mem_graded (intCast_mem B _) (torus_pow_mem B n)

def gradedPsi (B : Base (M := M)) :
    GradedRingHom (unboundedPiece B EulerKind.geometric) (piece B) where
  toRingHom := psi B
  map_mem := psi_mem B

end DiamondIntegral.Section4.RESAlternativePsi
