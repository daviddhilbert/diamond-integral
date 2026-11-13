import «section 4».GammaFiniteRVFiniteUnionPresentation
import «section 4».GammaFiniteRVGrading
import «section 4».CoactionGradedMaps

/-! Full object-degree grading on finite Gamma unions and preservation
of every degree by both directions of the presentation equivalence. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteRVFiniteUnionGrading
open GammaFiniteRVFiniteUnionPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem evaluation_mem (B : Base (M := M)) {n : ℕ} (a : Family B n) :
    evaluation a ∈ GammaFiniteRVGrading.gradedPiece B n := by
  change (∑ i, GammaFiniteRVPresentation.objectClass (a.chart i)) ∈ GammaFiniteRVGrading.gradedPiece B n
  exact (GammaFiniteRVGrading.gradedPiece B n).sum_mem (fun i _ => GammaFiniteRVGrading.class_mem B (a.chart i))

def coaction (B : Base (M := M)) : Ring B →+* Polynomial (Ring B) :=
  (Polynomial.mapRingHom (fromChartRing B)).comp ((GammaFiniteRVGrading.coaction B).comp (toChartRing B))

theorem coaction_class (B : Base (M := M)) {n : ℕ} (a : Family B n) :
    coaction B (objectClass a) = Polynomial.monomial n (objectClass a) := by
  change (GammaFiniteRVGrading.coaction B (toChartRing B (objectClass a))).map (fromChartRing B) = _
  rw [toChart_class]
  have hm : GammaFiniteRVGrading.coaction B (evaluation a) = Polynomial.monomial n (evaluation a) :=
    evaluation_mem B a
  rw [hm, Polynomial.map_monomial]
  have h := RingHom.congr_fun (from_to B) (objectClass a)
  change fromChartRing B (toChartRing B (objectClass a)) = objectClass a at h
  rw [toChart_class] at h
  rw [h]

theorem coaction_counit (B : Base (M := M)) :
    (Polynomial.evalRingHom 1).comp (coaction B) = RingHom.id _ := by
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

theorem class_mem (B : Base (M := M)) {n : ℕ} (a : Family B n) : objectClass a ∈ piece B n := coaction_class B a

theorem toChart_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (toChartRing B)).comp (coaction B) = (GammaFiniteRVGrading.coaction B).comp (toChartRing B) := by
  apply hom_ext B
  intro n a
  change (coaction B (objectClass a)).map (toChartRing B) = GammaFiniteRVGrading.coaction B (toChartRing B (objectClass a))
  rw [coaction_class, Polynomial.map_monomial, toChart_class]
  exact (evaluation_mem B a).symm

theorem fromChart_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (fromChartRing B)).comp (GammaFiniteRVGrading.coaction B) = (coaction B).comp (fromChartRing B) := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change (GammaFiniteRVGrading.coaction B (GammaFiniteRVPresentation.objectClass a)).map (fromChartRing B) =
    coaction B (fromChartRing B (GammaFiniteRVPresentation.objectClass a))
  rw [GammaFiniteRVGrading.coaction_class, Polynomial.map_monomial, fromChart_class]
  exact (coaction_class B (single a)).symm

theorem toChart_mem (B : Base (M := M)) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    toChartRing B x ∈ GammaFiniteRVGrading.gradedPiece B n := by
  change coaction B x = Polynomial.monomial n x at hx
  change GammaFiniteRVGrading.coaction B (toChartRing B x) = Polynomial.monomial n (toChartRing B x)
  have he := RingHom.congr_fun (toChart_coaction B) x
  change (coaction B x).map (toChartRing B) = GammaFiniteRVGrading.coaction B (toChartRing B x) at he
  rw [← he, hx, Polynomial.map_monomial]

theorem fromChart_mem (B : Base (M := M)) {n : ℕ} {x : GammaFiniteRVPresentation.ChartRing B}
    (hx : x ∈ GammaFiniteRVGrading.gradedPiece B n) : fromChartRing B x ∈ piece B n := by
  change GammaFiniteRVGrading.coaction B x = Polynomial.monomial n x at hx
  change coaction B (fromChartRing B x) = Polynomial.monomial n (fromChartRing B x)
  have he := RingHom.congr_fun (fromChart_coaction B) x
  change (GammaFiniteRVGrading.coaction B x).map (fromChartRing B) = coaction B (fromChartRing B x) at he
  rw [← he, hx, Polynomial.map_monomial]

def gradedToChart (B : Base (M := M)) : GradedRingHom (piece B) (GammaFiniteRVGrading.gradedPiece B) where
  toRingHom := toChartRing B
  map_mem := fun hx => toChart_mem B hx

def gradedFromChart (B : Base (M := M)) : GradedRingHom (GammaFiniteRVGrading.gradedPiece B) (piece B) where
  toRingHom := fromChartRing B
  map_mem := fun hx => fromChart_mem B hx

end DiamondIntegral.Section4.GammaFiniteRVFiniteUnionGrading
