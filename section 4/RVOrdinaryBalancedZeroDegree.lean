import «section 4».GammaOrdinaryZeroDegreeFinite
import «section 4».RVOrdinaryIntegerTensor
import «section 4».RVOrdinaryBalancedGradings
import «section 4».RVOrdinaryDegreeZero
import «section 4».TensorZeroDegree
import «section 4».CoactionKernel

/-! The actual ordinary tensor and RV comparison are isomorphic in
degree zero. The proof balances every zero-degree Gamma element through
the finite Gamma coefficient ring and uses the actual RES/RV zero-degree
inverse. Its entire comparison kernel is homogeneous and decomposes into
positive-degree kernel elements; global kernel generators remain separate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryBalancedZeroDegree
open RVOrdinaryBalancedTensor RVOrdinaryBalancedGradings RVOrdinaryIntegerTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem comparison_res (B : Base (M := M)) (x : RESOrdinaryRing.Ring B) :
    comparison B (resInclusion B x) = RVOrdinaryMaps.ofRES B x := by
  change comparison B (x ⊗ₜ[GammaOrdinaryAlgebras.Coeff B] 1) = _
  rw [comparison_tmul, map_one, mul_one]

theorem res_surjective (B : Base (M := M)) {x : Source B} (hx : x ∈ piece B 0) :
    ∃ r : RESOrdinaryRing.Ring B, r ∈ RESOrdinaryGrading.gradedPiece B 0 ∧ resInclusion B r = x := by
  apply TensorZeroDegree.zero_surjective (data B) _ hx
  intro b hb
  obtain ⟨hc, he⟩ := GammaOrdinaryZeroDegreeFinite.full_zero_preimage B hb
  exact ⟨GammaOrdinaryZeroDegreeFinite.full B b, hc, he⟩

theorem res_injective (B : Base (M := M)) :
    Set.InjOn (resInclusion B) (RESOrdinaryGrading.gradedPiece B 0) := by
  intro x hx y hy he
  have h := congrArg (comparison B) he
  rw [comparison_res, comparison_res] at h
  exact RVOrdinaryDegreeZero.full_injective_on_degree_zero B hx hy h

def zeroMap (B : Base (M := M)) : (RESOrdinaryGrading.gradingCoaction B).zeroSubring →+*
    (coaction B).zeroSubring :=
  ((resInclusion B).toRingHom.comp (RESOrdinaryGrading.gradingCoaction B).zeroSubring.subtype).codRestrict
    (coaction B).zeroSubring (fun x => tmul_mem B x.property (SetLike.one_mem_graded _))

theorem zeroMap_bijective (B : Base (M := M)) : Function.Bijective (zeroMap B) := by
  constructor
  · intro x y h
    exact Subtype.ext (res_injective B x.property y.property (congrArg Subtype.val h))
  · intro x
    obtain ⟨r, hr, he⟩ := res_surjective B x.property
    exact ⟨⟨r, hr⟩, Subtype.ext he⟩

def zeroEquiv (B : Base (M := M)) : (RESOrdinaryGrading.gradingCoaction B).zeroSubring ≃+*
    (coaction B).zeroSubring := RingEquiv.ofBijective (zeroMap B) (zeroMap_bijective B)

theorem comparison_injective (B : Base (M := M)) : Set.InjOn (comparison B) (piece B 0) := by
  intro x hx y hy h
  obtain ⟨a, ha, rfl⟩ := res_surjective B hx
  obtain ⟨b, hb, rfl⟩ := res_surjective B hy
  rw [comparison_res, comparison_res] at h
  exact congrArg (resInclusion B) (RVOrdinaryDegreeZero.full_injective_on_degree_zero B ha hb h)

def zeroComparison (B : Base (M := M)) : (coaction B).zeroSubring →+*
    (RVOrdinaryGrading.gradingCoaction B).zeroSubring :=
  ((comparison B).toRingHom.comp (coaction B).zeroSubring.subtype).codRestrict
    (RVOrdinaryGrading.gradingCoaction B).zeroSubring (fun x => (gradedComparison B).map_mem x.property)

theorem zeroComparison_bijective (B : Base (M := M)) : Function.Bijective (zeroComparison B) := by
  constructor
  · intro x y h
    exact Subtype.ext (comparison_injective B x.property y.property (congrArg Subtype.val h))
  · intro x
    obtain ⟨r, hr, he⟩ := RVOrdinaryDegreeZero.full_degree_zero_surjective B x.val x.property
    refine ⟨⟨resInclusion B r, tmul_mem B hr (SetLike.one_mem_graded _)⟩, ?_⟩
    exact Subtype.ext ((comparison_res B r).trans he)

def comparisonZeroEquiv (B : Base (M := M)) : (coaction B).zeroSubring ≃+*
    (RVOrdinaryGrading.gradingCoaction B).zeroSubring :=
  RingEquiv.ofBijective (zeroComparison B) (zeroComparison_bijective B)

theorem compatibility (B : Base (M := M)) :
    (Polynomial.mapRingHom (comparison B).toRingHom).comp (coaction B).map =
      (RVOrdinaryGrading.gradingCoaction B).map.comp (comparison B).toRingHom :=
  (coaction B).map_coaction_of_mem (RVOrdinaryGrading.gradingCoaction B) (comparison B).toRingHom
    (fun _ _ hx => (gradedComparison B).map_mem hx)

theorem kernel_homogeneous (B : Base (M := M)) :
    (RingHom.ker (comparison B).toRingHom).IsHomogeneous (piece B) :=
  (coaction B).kernel_homogeneous (RVOrdinaryGrading.gradingCoaction B) (comparison B).toRingHom (compatibility B)

theorem kernel_positive_decomposition (B : Base (M := M)) (x : Source B) (hx : comparison B x = 0) :
    (∑ n ∈ ((coaction B).map x).support.filter (fun n => 0 < n), ((coaction B).map x).coeff n) = x :=
  (coaction B).kernel_positive_decomposition (RVOrdinaryGrading.gradingCoaction B)
    (comparison B).toRingHom (compatibility B) (comparison_injective B) x hx

end DiamondIntegral.Section4.RVOrdinaryBalancedZeroDegree
