import «section 4».GammaFiniteRVMapGradings
import «section 4».GammaBoundedRVProfiles
import «section 4».RVZeroDegreeRES

/-! Every Gamma chart of degree zero is finite. The actual finite-Gamma
coefficient maps admit explicit inverse maps in degree zero, in both the
full and bounded RV-contraction-restricted presentations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaZeroDegreeFinite
open GammaWeightedCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def finiteZero {B : Base (M := M)} (a : Chart B 0) : GammaFiniteRVCharts.FiniteChart B 0 :=
  ⟨a, Set.toFinite _⟩

def value (B : Base (M := M)) : ∀ n, Chart B n → GammaFiniteRVPresentation.ChartRing B
  | 0, a => GammaFiniteRVPresentation.objectClass (finiteZero a)
  | _ + 1, _ => 0

def invariant (B : Base (M := M)) : GammaRVChartPresentation.Invariant B (GammaFiniteRVPresentation.ChartRing B) where
  value := value B
  unit := GammaFiniteRVPresentation.class_unit B
  product n m a b := by
    cases m <;> cases n
    · exact GammaFiniteRVPresentation.class_product (finiteZero a) (finiteZero b)
    · exact (mul_zero _).symm
    · exact (zero_mul _).symm
    · exact (zero_mul _).symm
  iso n a b F := by
    cases n
    · exact GammaFiniteRVPresentation.class_iso F
    · rfl
  empty n μ hμ := by
    cases n
    · exact GammaFiniteRVPresentation.class_empty B 0 μ hμ
    · rfl
  scissor n I J hI hJ hU hN μ hμ := by
    cases n
    · exact GammaFiniteRVPresentation.class_scissor B 0 I J hI hJ (Set.toFinite I) (Set.toFinite J) hU hN μ hμ
    · rfl

def full (B : Base (M := M)) : GammaRVChartPresentation.ChartRing B →+* GammaFiniteRVPresentation.ChartRing B :=
  GammaRVChartPresentation.lift B (invariant B)

theorem full_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    full B (GammaRVChartPresentation.objectClass a) = value B n a :=
  GammaRVChartPresentation.lift_class B (invariant B) a

theorem forget_full (B : Base (M := M)) :
    (GammaFiniteRVMaps.forget B).comp (full B) = (GammaRVGrading.gradingCoaction B).zeroProjection := by
  apply GammaRVChartPresentation.hom_ext B
  intro n a
  change GammaFiniteRVMaps.forget B (full B (GammaRVChartPresentation.objectClass a)) = _
  rw [full_class]
  change GammaFiniteRVMaps.forget B (value B n a) = (GammaRVGrading.coaction B (GammaRVChartPresentation.objectClass a)).coeff 0
  rw [GammaRVGrading.coaction_class]
  cases n with
  | zero =>
    change GammaFiniteRVMaps.forget B (GammaFiniteRVPresentation.objectClass (finiteZero a)) = _
    rw [GammaFiniteRVMaps.forget_class, Polynomial.coeff_monomial_same]
    rfl
  | succ n => simp only [value, map_zero, Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]

theorem full_forget (B : Base (M := M)) :
    (full B).comp (GammaFiniteRVMaps.forget B) = (GammaFiniteRVGrading.gradingCoaction B).zeroProjection := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change full B (GammaFiniteRVMaps.forget B (GammaFiniteRVPresentation.objectClass a)) = _
  rw [GammaFiniteRVMaps.forget_class, full_class]
  change value B n a.toChart = (GammaFiniteRVGrading.coaction B (GammaFiniteRVPresentation.objectClass a)).coeff 0
  rw [GammaFiniteRVGrading.coaction_class]
  cases n with
  | zero => exact (Polynomial.coeff_monomial_same 0 _).symm
  | succ n => simp only [value, Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]

def gradedFull (B : Base (M := M)) :
    GradedRingHom (GammaRVGrading.gradedPiece B) (GammaFiniteRVGrading.gradedPiece B) where
  toRingHom := full B
  map_mem := GammaRVGrading.map_mem_of_classes B (GammaFiniteRVGrading.gradingCoaction B) (full B) (by
    intro n a
    rw [full_class]
    cases n
    · exact GammaFiniteRVGrading.class_mem B (finiteZero a)
    · exact (GammaFiniteRVGrading.gradedPiece B _).zero_mem)

theorem full_zero_preimage (B : Base (M := M)) {x : GammaRVChartPresentation.ChartRing B}
    (hx : x ∈ GammaRVGrading.gradedPiece B 0) :
    full B x ∈ GammaFiniteRVGrading.gradedPiece B 0 ∧ GammaFiniteRVMaps.forget B (full B x) = x :=
  ⟨(gradedFull B).map_mem hx, (RingHom.congr_fun (forget_full B) x).trans
    ((GammaRVGrading.gradingCoaction B).zeroProjection_of_mem hx)⟩

def bounded (B : Base (M := M)) : GammaBoundedRVPresentation.ChartRing B →+* GammaFiniteRVPresentation.ChartRing B :=
  (full B).comp (GammaBoundedRVMaps.forget B)

theorem bounded_class (B : Base (M := M)) {n : ℕ} (a : GammaBoundedRVCharts.BoundedChart B n) :
    bounded B (GammaBoundedRVPresentation.objectClass a) = value B n a.toChart := by
  change full B (GammaBoundedRVMaps.forget B (GammaBoundedRVPresentation.objectClass a)) = _
  rw [GammaBoundedRVMaps.forget_class, full_class]

theorem finite_bounded (B : Base (M := M)) :
    (GammaFiniteRVMaps.bounded B).comp (bounded B) = (GammaBoundedRVGrading.gradingCoaction B).zeroProjection := by
  apply GammaBoundedRVPresentation.hom_ext B
  intro n a
  change GammaFiniteRVMaps.bounded B (bounded B (GammaBoundedRVPresentation.objectClass a)) = _
  rw [bounded_class]
  change GammaFiniteRVMaps.bounded B (value B n a.toChart) =
    (GammaBoundedRVGrading.coaction B (GammaBoundedRVPresentation.objectClass a)).coeff 0
  rw [GammaBoundedRVGrading.coaction_class]
  cases n with
  | zero =>
    change GammaFiniteRVMaps.bounded B (GammaFiniteRVPresentation.objectClass (finiteZero a.toChart)) = _
    rw [GammaFiniteRVMaps.bounded_class, Polynomial.coeff_monomial_same]
    rfl
  | succ n => simp only [value, map_zero, Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]

def gradedBounded (B : Base (M := M)) :
    GradedRingHom (GammaBoundedRVGrading.gradedPiece B) (GammaFiniteRVGrading.gradedPiece B) :=
  (gradedFull B).comp (GammaBoundedRVProfiles.gradedForget B)

theorem bounded_zero_preimage (B : Base (M := M)) {x : GammaBoundedRVPresentation.ChartRing B}
    (hx : x ∈ GammaBoundedRVGrading.gradedPiece B 0) :
    bounded B x ∈ GammaFiniteRVGrading.gradedPiece B 0 ∧ GammaFiniteRVMaps.bounded B (bounded B x) = x :=
  ⟨(gradedBounded B).map_mem hx, (RingHom.congr_fun (finite_bounded B) x).trans
    ((GammaBoundedRVGrading.gradingCoaction B).zeroProjection_of_mem hx)⟩

end DiamondIntegral.Section4.GammaZeroDegreeFinite
