import «section 4».RVOrdinaryFamilyPresentation
import «section 4».CoactionGradedMaps

/-! Every intrinsic admissible-family disjoint-union presentation has its
full object-degree grading. A classwise criterion proves degree
preservation for maps out of the entire ring. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryFamilyGrading
open RVMeasuredCharts RVAdmissibleFamilies RVOrdinaryFamilyPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradingInvariant {B : Base (M := M)} (F : Family B) : Invariant F (Polynomial (Ring F)) where
  value n a ha := Polynomial.monomial n (objectClass F (⟨a, ha⟩ : Object F n))
  unit := by
    change Polynomial.monomial 0 (objectClass F (unit F)) = 1
    simp [objectClass_unit]
  product k l a b ha hb := by
    change Polynomial.monomial (l + k) (objectClass F (product F (⟨a, ha⟩ : Object F k) (⟨b, hb⟩ : Object F l))) = _
    rw [objectClass_product, Polynomial.monomial_mul_monomial, Nat.add_comm k l]
  iso n a b ha hb f := congrArg (Polynomial.monomial n)
    (objectClass_iso F (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) f)
  empty n a ha h := by rw [objectClass_empty F (⟨a, ha⟩ : Object F n) h, map_zero]
  coproduct n a b ha hb := by
    change Polynomial.monomial n (objectClass F (coproduct F (⟨a, ha⟩ : Object F n) (⟨b, hb⟩ : Object F n))) = _
    simpa only [map_add] using congrArg (Polynomial.monomial n)
      (objectClass_coproduct F (⟨a, ha⟩ : Object F n) (⟨b, hb⟩ : Object F n))

def coaction {B : Base (M := M)} (F : Family B) : Ring F →+* Polynomial (Ring F) := lift F (gradingInvariant F)

theorem coaction_class {B : Base (M := M)} (F : Family B) {n : ℕ} (a : Object F n) :
    coaction F (objectClass F a) = Polynomial.monomial n (objectClass F a) := lift_objectClass F (gradingInvariant F) a

theorem coaction_counit {B : Base (M := M)} (F : Family B) :
    (Polynomial.evalRingHom 1).comp (coaction F) = RingHom.id (Ring F) := by
  apply hom_ext F
  intro n a
  change Polynomial.eval 1 (coaction F (objectClass F a)) = objectClass F a
  rw [coaction_class, Polynomial.eval_monomial, one_pow, mul_one]

theorem coaction_coassoc {B : Base (M := M)} (F : Family B) :
    (Polynomial.mapRingHom (coaction F)).comp (coaction F) = PolynomialDiagonal.diagonal.comp (coaction F) := by
  apply hom_ext F
  intro n a
  change (coaction F (objectClass F a)).map (coaction F) = PolynomialDiagonal.diagonal (coaction F (objectClass F a))
  rw [coaction_class, Polynomial.map_monomial, coaction_class, PolynomialDiagonal.diagonal_monomial]

def gradingCoaction {B : Base (M := M)} (F : Family B) : PolynomialCoactionGrading.Coaction (Ring F) where
  map := coaction F
  counit := coaction_counit F
  coassoc := coaction_coassoc F

def piece {B : Base (M := M)} (F : Family B) (n : ℕ) : AddSubgroup (Ring F) := (gradingCoaction F).piece n
instance gradedRing {B : Base (M := M)} (F : Family B) : GradedRing (piece F) := (gradingCoaction F).grading

theorem class_mem {B : Base (M := M)} (F : Family B) {n : ℕ} (a : Object F n) : objectClass F a ∈ piece F n := coaction_class F a

theorem map_coaction_of_classes {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R]
    (c : PolynomialCoactionGrading.Coaction R) (f : Ring F →+* R)
    (h : ∀ n (a : Object F n), c.map (f (objectClass F a)) = Polynomial.monomial n (f (objectClass F a))) :
    (Polynomial.mapRingHom f).comp (coaction F) = c.map.comp f := by
  apply hom_ext F
  intro n a
  change (coaction F (objectClass F a)).map f = c.map (f (objectClass F a))
  rw [coaction_class, Polynomial.map_monomial]
  exact (h n a).symm

theorem map_mem_of_classes {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R]
    (c : PolynomialCoactionGrading.Coaction R) (f : Ring F →+* R)
    (h : ∀ n (a : Object F n), c.map (f (objectClass F a)) = Polynomial.monomial n (f (objectClass F a)))
    {n : ℕ} {x : Ring F} (hx : x ∈ piece F n) : f x ∈ c.piece n := by
  change coaction F x = Polynomial.monomial n x at hx
  change c.map (f x) = Polynomial.monomial n (f x)
  have he := RingHom.congr_fun (map_coaction_of_classes F c f h) x
  change (coaction F x).map f = c.map (f x) at he
  rw [← he, hx, Polynomial.map_monomial]

end DiamondIntegral.Section4.RVOrdinaryFamilyGrading
