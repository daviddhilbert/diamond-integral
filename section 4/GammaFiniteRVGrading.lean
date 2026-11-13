import «section 4».GammaFiniteRVPresentation
import «section 4».PolynomialCoactionGrading

/-! The intrinsic finite RV-lift-restricted Gamma presentation has a full
natural-number grading, including finite homogeneous decomposition. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteRVGrading
open GammaFiniteRVCharts GammaFiniteRVPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradingInvariant (B : Base (M := M)) : Invariant B (Polynomial (ChartRing B)) where
  value n a := Polynomial.monomial n (objectClass a)
  unit := by simp [class_unit]
  product n m a b := by
    rw [class_product, Polynomial.monomial_mul_monomial, Nat.add_comm m n]
  iso n a b F := congrArg (Polynomial.monomial n) (class_iso F)
  empty n μ hμ := by rw [class_empty, map_zero]
  scissor n I J hI hJ hiI hiJ hU hN μ hμ := by
    simpa only [map_add] using congrArg (Polynomial.monomial n) (class_scissor B n I J hI hJ hiI hiJ hU hN μ hμ)

def coaction (B : Base (M := M)) : ChartRing B →+* Polynomial (ChartRing B) := lift B (gradingInvariant B)

theorem coaction_class (B : Base (M := M)) {n : ℕ} (a : FiniteChart B n) :
    coaction B (objectClass a) = Polynomial.monomial n (objectClass a) := lift_class B (gradingInvariant B) a

theorem coaction_counit (B : Base (M := M)) :
    (Polynomial.evalRingHom 1).comp (coaction B) = RingHom.id (ChartRing B) := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change Polynomial.eval 1 (coaction B (objectClass a)) = objectClass a
  rw [coaction_class, Polynomial.eval_monomial, one_pow, mul_one]

theorem coaction_coassoc (B : Base (M := M)) :
    (Polynomial.mapRingHom (coaction B)).comp (coaction B) = PolynomialDiagonal.diagonal.comp (coaction B) := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change (coaction B (objectClass a)).map (coaction B) = PolynomialDiagonal.diagonal (coaction B (objectClass a))
  rw [coaction_class, Polynomial.map_monomial, coaction_class, PolynomialDiagonal.diagonal_monomial]

def gradingCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (ChartRing B) where
  map := coaction B
  counit := coaction_counit B
  coassoc := coaction_coassoc B

def gradedPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (ChartRing B) := (gradingCoaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (gradedPiece B) := (gradingCoaction B).grading

theorem class_mem (B : Base (M := M)) {n : ℕ} (a : FiniteChart B n) : objectClass a ∈ gradedPiece B n :=
  coaction_class B a

theorem map_coaction_of_classes (B : Base (M := M)) {R : Type*} [CommRing R]
    (c : PolynomialCoactionGrading.Coaction R) (f : ChartRing B →+* R)
    (h : ∀ n (a : FiniteChart B n), f (objectClass a) ∈ c.piece n) :
    (Polynomial.mapRingHom f).comp (coaction B) = c.map.comp f := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change (coaction B (objectClass a)).map f = c.map (f (objectClass a))
  rw [coaction_class, Polynomial.map_monomial]
  exact (h n a).symm

theorem map_mem_of_classes (B : Base (M := M)) {R : Type*} [CommRing R]
    (c : PolynomialCoactionGrading.Coaction R) (f : ChartRing B →+* R)
    (h : ∀ n (a : FiniteChart B n), f (objectClass a) ∈ c.piece n)
    {n : ℕ} {x : ChartRing B} (hx : x ∈ gradedPiece B n) : f x ∈ c.piece n := by
  change coaction B x = Polynomial.monomial n x at hx
  change c.map (f x) = Polynomial.monomial n (f x)
  have he : c.map (f x) = (coaction B x).map f :=
    (RingHom.congr_fun (map_coaction_of_classes B c f h) x).symm
  rw [he, hx, Polynomial.map_monomial]

end DiamondIntegral.Section4.GammaFiniteRVGrading
