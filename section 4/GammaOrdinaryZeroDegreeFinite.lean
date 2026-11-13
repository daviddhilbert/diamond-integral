import «section 4».GammaOrdinaryFiniteMapGradings
import «section 4».RVZeroDegreeRES

/-! Every ordinary Gamma chart of degree zero is finite. The finite
coefficient map has an actual degree-zero inverse, constructed directly
without volume forms or an RV tensor decomposition. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryZeroDegreeFinite
open GammaOrdinaryCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def finiteZero {B : Base (M := M)} (a : Chart B 0) : FiniteChart B 0 := ⟨a, Set.toFinite _⟩
def value (B : Base (M := M)) : ∀ n, Chart B n → GammaOrdinaryFiniteRing.Ring B
  | 0, a => GammaOrdinaryFiniteRing.objectClass (finiteZero a)
  | _ + 1, _ => 0

def invariant (B : Base (M := M)) : GammaOrdinaryRing.Invariant B (GammaOrdinaryFiniteRing.Ring B) where
  value := value B
  unit := GammaOrdinaryFiniteRing.class_unit B
  product n m a b := by
    cases m <;> cases n
    · exact GammaOrdinaryFiniteRing.class_product (finiteZero a) (finiteZero b)
    · exact (mul_zero _).symm
    · exact (zero_mul _).symm
    · exact (zero_mul _).symm
  iso n a b f := by
    cases n
    · exact GammaOrdinaryFiniteRing.class_iso f
    · rfl
  empty n a ha := by
    cases n
    · exact GammaOrdinaryFiniteRing.class_empty (finiteZero a) ha
    · rfl
  scissor n a b c d h := by
    cases n
    · exact GammaOrdinaryFiniteRing.class_scissor (finiteZero a) (finiteZero b) (finiteZero c) (finiteZero d) h
    · rfl

def full (B : Base (M := M)) : GammaOrdinaryRing.Ring B →+* GammaOrdinaryFiniteRing.Ring B :=
  GammaOrdinaryRing.lift B (invariant B)

theorem full_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    full B (GammaOrdinaryRing.objectClass a) = value B n a := GammaOrdinaryRing.lift_class B (invariant B) a

theorem finite_full (B : Base (M := M)) :
    (GammaOrdinaryFiniteMaps.full B).comp (full B) = (GammaOrdinaryGrading.gradingCoaction B).zeroProjection := by
  apply GammaOrdinaryRing.hom_ext B
  intro n a
  change GammaOrdinaryFiniteMaps.full B (full B (GammaOrdinaryRing.objectClass a)) = _
  rw [full_class]
  change GammaOrdinaryFiniteMaps.full B (value B n a) =
    (GammaOrdinaryGrading.coaction B (GammaOrdinaryRing.objectClass a)).coeff 0
  rw [GammaOrdinaryGrading.coaction_class]
  cases n with
  | zero =>
    change GammaOrdinaryFiniteMaps.full B (GammaOrdinaryFiniteRing.objectClass (finiteZero a)) = _
    rw [GammaOrdinaryFiniteMaps.full_class, Polynomial.coeff_monomial_same]
    rfl
  | succ n => simp only [value, map_zero, Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]

theorem full_finite (B : Base (M := M)) :
    (full B).comp (GammaOrdinaryFiniteMaps.full B) = (GammaOrdinaryFiniteGrading.gradingCoaction B).zeroProjection := by
  apply GammaOrdinaryFiniteRing.hom_ext B
  intro n a
  change full B (GammaOrdinaryFiniteMaps.full B (GammaOrdinaryFiniteRing.objectClass a)) = _
  rw [GammaOrdinaryFiniteMaps.full_class, full_class]
  change value B n a.toChart = (GammaOrdinaryFiniteGrading.coaction B (GammaOrdinaryFiniteRing.objectClass a)).coeff 0
  rw [GammaOrdinaryFiniteGrading.coaction_class]
  cases n with
  | zero => exact (Polynomial.coeff_monomial_same 0 _).symm
  | succ n => simp only [value, Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]

theorem full_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (full B)).comp (GammaOrdinaryGrading.coaction B) =
      (GammaOrdinaryFiniteGrading.coaction B).comp (full B) := by
  apply GammaOrdinaryRing.hom_ext B
  intro n a
  change (GammaOrdinaryGrading.coaction B (GammaOrdinaryRing.objectClass a)).map (full B) =
    GammaOrdinaryFiniteGrading.coaction B (full B (GammaOrdinaryRing.objectClass a))
  rw [GammaOrdinaryGrading.coaction_class, Polynomial.map_monomial, full_class]
  cases n with
  | zero => exact (GammaOrdinaryFiniteGrading.coaction_class B (finiteZero a)).symm
  | succ n => simp only [value, map_zero, Polynomial.monomial_zero_right]

theorem full_mem (B : Base (M := M)) {n : ℕ} {x : GammaOrdinaryRing.Ring B}
    (hx : x ∈ GammaOrdinaryGrading.gradedPiece B n) :
    full B x ∈ GammaOrdinaryFiniteGrading.gradedPiece B n := by
  change GammaOrdinaryGrading.coaction B x = Polynomial.monomial n x at hx
  change GammaOrdinaryFiniteGrading.coaction B (full B x) = Polynomial.monomial n (full B x)
  have he := RingHom.congr_fun (full_coaction B) x
  change (GammaOrdinaryGrading.coaction B x).map (full B) = GammaOrdinaryFiniteGrading.coaction B (full B x) at he
  rw [← he, hx, Polynomial.map_monomial]

theorem full_zero_preimage (B : Base (M := M)) {x : GammaOrdinaryRing.Ring B}
    (hx : x ∈ GammaOrdinaryGrading.gradedPiece B 0) :
    full B x ∈ GammaOrdinaryFiniteGrading.gradedPiece B 0 ∧ GammaOrdinaryFiniteMaps.full B (full B x) = x :=
  ⟨full_mem B hx, (RingHom.congr_fun (finite_full B) x).trans
    ((GammaOrdinaryGrading.gradingCoaction B).zeroProjection_of_mem hx)⟩

end DiamondIntegral.Section4.GammaOrdinaryZeroDegreeFinite
