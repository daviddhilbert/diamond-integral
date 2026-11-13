import «section 4».GammaFunctionPolynomial
import «section 4».GammaBoundedFunctions

/-! The actual bounded polynomial source: its constant coefficient lies
in the original-base point group ring, and all positive coefficients are
bounded definable Euler functions. It embeds into the unbounded source. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedPolynomial
open GammaDefinableConvolution GammaBoundedFunctions GammaPointAlgebra

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def forgetBounded (B : Base (M := M)) (k : EulerKind) : boundedBaseSubring B k →+* baseSubring B k :=
  Subring.inclusion inf_le_left

theorem forgetBounded_injective (B : Base (M := M)) (k : EulerKind) :
    Function.Injective (forgetBounded B k) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun x : baseSubring B k => x.val) h

def boundedPointSubring (B : Base (M := M)) (k : EulerKind) : Subring (boundedBaseSubring B k) :=
  (pointSubring B k).comap (forgetBounded B k)

def sourceRing (B : Base (M := M)) (k : EulerKind) : Subring (Polynomial (boundedBaseSubring B k)) :=
  (boundedPointSubring B k).comap Polynomial.constantCoeff

theorem mem_sourceRing (B : Base (M := M)) (k : EulerKind) (p : Polynomial (boundedBaseSubring B k)) :
    p ∈ sourceRing B k ↔ forgetBounded B k (p.coeff 0) ∈ pointSubring B k := Iff.rfl

theorem monomial_mem_positive (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0)
    (f : boundedBaseSubring B k) : Polynomial.monomial n f ∈ sourceRing B k := by
  rw [mem_sourceRing, Polynomial.coeff_monomial, ite_eq_right hn, map_zero]
  exact (pointSubring B k).zero_mem

theorem point_mem_boundedPointSubring (B : Base (M := M)) (k : EulerKind) (a : Name B) :
    basePoint B k a ∈ boundedPointSubring B k := by
  let b : GammaNamesSubgroup.additiveNames B := ⟨a.val, a.property⟩
  refine ⟨AddMonoidAlgebra.single b 1, ?_⟩
  apply Subtype.ext
  rw [pointGroupRing_single, one_zsmul]
  rfl

theorem point_monomial_mem (B : Base (M := M)) (k : EulerKind) (n : ℕ) (a : Name B) :
    Polynomial.monomial n (basePoint B k a) ∈ sourceRing B k := by
  by_cases hn : n = 0
  · subst n
    rw [mem_sourceRing, Polynomial.coeff_monomial, ite_eq_left rfl]
    exact point_mem_boundedPointSubring B k a
  · exact monomial_mem_positive B k n hn _

def toUnbounded (B : Base (M := M)) (k : EulerKind) : sourceRing B k →+* GammaFunctionPolynomial.sourceRing B k :=
  (((Polynomial.mapRingHom (forgetBounded B k)).comp (sourceRing B k).subtype)).codRestrict
    (GammaFunctionPolynomial.sourceRing B k) (by
      intro p
      change Polynomial.map (forgetBounded B k) p.val ∈ GammaFunctionPolynomial.sourceRing B k
      rw [GammaFunctionPolynomial.mem_sourceRing, Polynomial.coeff_map]
      exact p.property)

theorem toUnbounded_injective (B : Base (M := M)) (k : EulerKind) :
    Function.Injective (toUnbounded B k) := by
  intro p q h
  apply Subtype.ext
  apply Polynomial.map_injective (forgetBounded B k) (forgetBounded_injective B k)
  exact congrArg (fun x : GammaFunctionPolynomial.sourceRing B k => x.val) h

end DiamondIntegral.Section4.GammaBoundedPolynomial
