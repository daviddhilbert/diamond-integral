import «section 4».RVDisjointPresentation
import «section 4».CoactionGradedMaps

/-! The actual tagged-disjoint-union presentation has a full natural-
number grading. The presentation equivalence preserves every homogeneous
piece in both directions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDisjointGrading
open RVMeasuredCharts RVDisjointPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradingInvariant (B : Base (M := M)) : Invariant B (Polynomial (Ring B)) where
  value n a := Polynomial.monomial n (objectClass a)
  unit := by simp [objectClass_unit]
  product k l a b := by
    rw [objectClass_product, Polynomial.monomial_mul_monomial, Nat.add_comm k l]
  iso n a b F := congrArg (Polynomial.monomial n) (objectClass_iso F)
  empty n a ha := by rw [objectClass_empty a ha, map_zero]
  coproduct n a b := by
    simpa only [map_add] using congrArg (Polynomial.monomial n) (objectClass_coproduct a b)

def coaction (B : Base (M := M)) : Ring B →+* Polynomial (Ring B) := lift B (gradingInvariant B)

theorem coaction_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    coaction B (objectClass a) = Polynomial.monomial n (objectClass a) := lift_objectClass B (gradingInvariant B) a

theorem coaction_counit (B : Base (M := M)) :
    (Polynomial.evalRingHom 1).comp (coaction B) = RingHom.id (Ring B) := by
  apply hom_ext B
  intro n a
  change Polynomial.eval 1 (coaction B (objectClass a)) = objectClass a
  rw [coaction_class, Polynomial.eval_monomial, one_pow, mul_one]

theorem coaction_coassoc (B : Base (M := M)) :
    (Polynomial.mapRingHom (coaction B)).comp (coaction B) = PolynomialDiagonal.diagonal.comp (coaction B) := by
  apply hom_ext B
  intro n a
  change (coaction B (objectClass a)).map (coaction B) = PolynomialDiagonal.diagonal (coaction B (objectClass a))
  rw [coaction_class, Polynomial.map_monomial, coaction_class, PolynomialDiagonal.diagonal_monomial]

def gradingCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) where
  map := coaction B
  counit := coaction_counit B
  coassoc := coaction_coassoc B

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (gradingCoaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (gradingCoaction B).grading

theorem class_mem (B : Base (M := M)) {n : ℕ} (a : Chart B n) : objectClass a ∈ piece B n := coaction_class B a

theorem toChart_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (toChartRing B)).comp (coaction B) = (RVGrading.coaction B).comp (toChartRing B) := by
  apply hom_ext B
  intro n a
  change (coaction B (objectClass a)).map (toChartRing B) = RVGrading.coaction B (toChartRing B (objectClass a))
  rw [coaction_class, Polynomial.map_monomial, toChartRing_class, RVGrading.coaction_class]

theorem fromChart_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (fromChartRing B)).comp (RVGrading.coaction B) = (coaction B).comp (fromChartRing B) := by
  apply RVGrading.hom_ext B
  intro n a
  change (RVGrading.coaction B (RVChartRing.objectClass a)).map (fromChartRing B) =
    coaction B (fromChartRing B (RVChartRing.objectClass a))
  rw [RVGrading.coaction_class, Polynomial.map_monomial, fromChartRing_class, coaction_class]

theorem toChart_mem (B : Base (M := M)) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    toChartRing B x ∈ RVGrading.gradedPiece B n := by
  change coaction B x = Polynomial.monomial n x at hx
  change RVGrading.coaction B (toChartRing B x) = Polynomial.monomial n (toChartRing B x)
  have he := RingHom.congr_fun (toChart_coaction B) x
  change (coaction B x).map (toChartRing B) = RVGrading.coaction B (toChartRing B x) at he
  rw [← he, hx, Polynomial.map_monomial]

theorem fromChart_mem (B : Base (M := M)) {n : ℕ} {x : RVChartRing.Ring B} (hx : x ∈ RVGrading.gradedPiece B n) :
    fromChartRing B x ∈ piece B n := by
  change RVGrading.coaction B x = Polynomial.monomial n x at hx
  change coaction B (fromChartRing B x) = Polynomial.monomial n (fromChartRing B x)
  have he := RingHom.congr_fun (fromChart_coaction B) x
  change (RVGrading.coaction B x).map (fromChartRing B) = coaction B (fromChartRing B x) at he
  rw [← he, hx, Polynomial.map_monomial]

def gradedToChart (B : Base (M := M)) : GradedRingHom (piece B) (RVGrading.gradedPiece B) where
  toRingHom := toChartRing B
  map_mem := fun hx => toChart_mem B hx

def gradedFromChart (B : Base (M := M)) : GradedRingHom (RVGrading.gradedPiece B) (piece B) where
  toRingHom := fromChartRing B
  map_mem := fun hx => fromChart_mem B hx

theorem equivalence_mem_iff (B : Base (M := M)) (n : ℕ) (x : Ring B) :
    equivalence B x ∈ RVGrading.gradedPiece B n ↔ x ∈ piece B n := by
  change toChartRing B x ∈ RVGrading.gradedPiece B n ↔ x ∈ piece B n
  constructor
  · intro hx
    have h := fromChart_mem B hx
    have he := RingHom.congr_fun (from_to B) x
    change fromChartRing B (toChartRing B x) = x at he
    rwa [he] at h
  · exact toChart_mem B

end DiamondIntegral.Section4.RVDisjointGrading
