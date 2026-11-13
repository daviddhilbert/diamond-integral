import «section 4».RVOrdinaryRing
import «section 4».RVGrading

/-! The ordinary RV chart ring is graded, and forgetting volume preserves
every homogeneous component. The finite-coproduct category comparison is
not part of this construction. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryGrading
open RVMeasuredCharts RVOrdinaryRing
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

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

theorem coaction_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    coaction B (objectClass a) = Polynomial.monomial n (objectClass a) :=
  lift_objectClass B (gradingInvariant B) a

theorem coaction_counit (B : Base (M := M)) :
    (Polynomial.evalRingHom 1).comp (coaction B) = RingHom.id (Ring B) := by
  apply RVOrdinaryRing.hom_ext B
  intro n a
  change Polynomial.eval 1 (coaction B (objectClass a)) = objectClass a
  rw [coaction_class, Polynomial.eval_monomial, one_pow, mul_one]

theorem coaction_coassoc (B : Base (M := M)) :
    (Polynomial.mapRingHom (coaction B)).comp (coaction B) =
      PolynomialDiagonal.diagonal.comp (coaction B) := by
  apply RVOrdinaryRing.hom_ext B
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

theorem class_mem (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    objectClass a ∈ gradedPiece B n := coaction_class B a

theorem forget_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (forget B)).comp (RVGrading.coaction B) =
      (coaction B).comp (forget B) := by
  apply RVGrading.hom_ext B
  intro n a
  change (RVGrading.coaction B (RVChartRing.objectClass a)).map (forget B) =
    coaction B (forget B (RVChartRing.objectClass a))
  rw [RVGrading.coaction_class, Polynomial.map_monomial,
    forget_objectClass, coaction_class]

theorem forget_mem (B : Base (M := M)) {n : ℕ} {x : RVChartRing.Ring B}
    (hx : x ∈ RVGrading.gradedPiece B n) : forget B x ∈ gradedPiece B n := by
  change RVGrading.coaction B x = Polynomial.monomial n x at hx
  change coaction B (forget B x) = Polynomial.monomial n (forget B x)
  have he : coaction B (forget B x) = (RVGrading.coaction B x).map (forget B) :=
    (RingHom.congr_fun (forget_coaction B) x).symm
  rw [he, hx, Polynomial.map_monomial]

theorem forget_component (B : Base (M := M)) (n : ℕ) (x : RVChartRing.Ring B) :
    forget B ((RVGrading.coaction B x).coeff n) = (coaction B (forget B x)).coeff n := by
  change forget B ((RVGrading.coaction B x).coeff n) = _
  have h := congrArg (fun p : Polynomial (Ring B) => p.coeff n)
    (RingHom.congr_fun (forget_coaction B) x)
  simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map] using h

end DiamondIntegral.Section4.RVOrdinaryGrading
