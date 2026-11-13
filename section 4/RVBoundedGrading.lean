import «section 4».RVBoundedRing
import «section 4».PolynomialCoactionGrading

/-! The concrete doubly bounded measured RV ring has a full natural-number grading.
No category or tensor comparison is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBoundedGrading
open RVMeasuredCharts RVBoundedCharts RVBoundedRing
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : Ring B →+* R) (h : ∀ k (a : BoundedChart B k), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

def gradingInvariant (B : Base (M := M)) : Invariant B (Polynomial (Ring B)) where
  value n a := Polynomial.monomial n (objectClass a)
  unit := by simp [objectClass_unit]
  product k l a b := by
    rw [objectClass_product, Polynomial.monomial_mul_monomial, Nat.add_comm k l]
  iso n a b F := congrArg (Polynomial.monomial n) (objectClass_iso F)
  empty n a ha := by rw [objectClass_empty a ha, map_zero]
  scissor n a b c d h := by
    simpa only [map_add] using congrArg (Polynomial.monomial n) (objectClass_scissor a b c d h)

def coaction (B : Base (M := M)) : Ring B →+* Polynomial (Ring B) :=
  lift B (gradingInvariant B)

theorem coaction_class (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    coaction B (objectClass a) = Polynomial.monomial n (objectClass a) :=
  lift_objectClass B (gradingInvariant B) a

theorem coaction_counit (B : Base (M := M)) :
    (Polynomial.evalRingHom 1).comp (coaction B) = RingHom.id (Ring B) := by
  apply hom_ext B
  intro n a
  change Polynomial.eval 1 (coaction B (objectClass a)) = objectClass a
  rw [coaction_class, Polynomial.eval_monomial, one_pow, mul_one]

theorem coaction_coassoc (B : Base (M := M)) :
    (Polynomial.mapRingHom (coaction B)).comp (coaction B) =
      PolynomialDiagonal.diagonal.comp (coaction B) := by
  apply hom_ext B
  intro n a
  change (coaction B (objectClass a)).map (coaction B) =
    PolynomialDiagonal.diagonal (coaction B (objectClass a))
  rw [coaction_class, Polynomial.map_monomial, coaction_class,
    PolynomialDiagonal.diagonal_monomial]

def gradingCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) where
  map := coaction B
  counit := coaction_counit B
  coassoc := coaction_coassoc B

def gradedPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) :=
  (gradingCoaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (gradedPiece B) :=
  (gradingCoaction B).grading

theorem class_mem (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    objectClass a ∈ gradedPiece B n := coaction_class B a

end DiamondIntegral.Section4.RVBoundedGrading
