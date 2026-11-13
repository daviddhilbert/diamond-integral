import «section 4».TensorZeroDegree
import «section 4».GammaZeroDegreeFinite
import «section 4».RVBalancedRadiusDegreeZero
import «section 4».RVZeroDegreeRetraction

/-! In both actual finite-Gamma-balanced tensors, the RES factor is the
entire degree-zero subring. The same holds after the tensor radius
quotient. These equivalences require no positive-degree kernel theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBalancedZeroDegree
open RVBalancedGradings RVZeroDegreeEquivalences
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem measured_surjective (B : Base (M := M)) {x : RVFiniteBalancedTensor.Source B}
    (hx : x ∈ measuredPiece B 0) :
    ∃ r : RESChartRing.Ring B, r ∈ RESRingCoaction.gradedPiece B 0 ∧ RVFiniteBalancedTensor.resInclusion B r = x := by
  apply TensorZeroDegree.zero_surjective (measuredData B) _ hx
  intro b hb
  obtain ⟨hc, he⟩ := GammaZeroDegreeFinite.full_zero_preimage B hb
  exact ⟨GammaZeroDegreeFinite.full B b, hc, he⟩

theorem measured_injective (B : Base (M := M)) :
    Set.InjOn (RVFiniteBalancedTensor.resInclusion B) (RESRingCoaction.gradedPiece B 0) := by
  intro x hx y hy h
  have he : RVChartMaps.ofRES B x = RVChartMaps.ofRES B y :=
    (RVFiniteBalancedTensor.comparison_res B x).symm.trans
      ((congrArg (RVFiniteBalancedTensor.comparison B) h).trans (RVFiniteBalancedTensor.comparison_res B y))
  exact RVZeroDegreeRetraction.full_injective_on_degree_zero B hx hy he

def measuredMap (B : Base (M := M)) : resZero B →+* (measuredCoaction B).zeroSubring :=
  ((RVFiniteBalancedTensor.resInclusion B).toRingHom.comp (resZero B).subtype).codRestrict
    (measuredCoaction B).zeroSubring
    (fun x => measured_tmul_mem B x.property (SetLike.one_mem_graded _))

theorem measuredMap_bijective (B : Base (M := M)) : Function.Bijective (measuredMap B) := by
  constructor
  · intro x y h
    exact Subtype.ext (measured_injective B x.property y.property (congrArg Subtype.val h))
  · intro x
    obtain ⟨r, hr, hrx⟩ := measured_surjective B x.property
    exact ⟨⟨r, hr⟩, Subtype.ext hrx⟩

def measuredEquiv (B : Base (M := M)) : resZero B ≃+* (measuredCoaction B).zeroSubring :=
  RingEquiv.ofBijective (measuredMap B) (measuredMap_bijective B)

theorem measuredEquiv_apply (B : Base (M := M)) (x : resZero B) :
    (measuredEquiv B x).val = RVFiniteBalancedTensor.resInclusion B x.val := rfl

theorem bounded_surjective (B : Base (M := M)) {x : RVBoundedBalancedTensor.Source B}
    (hx : x ∈ boundedPiece B 0) :
    ∃ r : RESChartRing.Ring B, r ∈ RESRingCoaction.gradedPiece B 0 ∧ RVBoundedBalancedTensor.resInclusion B r = x := by
  apply TensorZeroDegree.zero_surjective (boundedData B) _ hx
  intro b hb
  obtain ⟨hc, he⟩ := GammaZeroDegreeFinite.bounded_zero_preimage B hb
  exact ⟨GammaZeroDegreeFinite.bounded B b, hc, he⟩

theorem bounded_injective (B : Base (M := M)) :
    Set.InjOn (RVBoundedBalancedTensor.resInclusion B) (RESRingCoaction.gradedPiece B 0) := by
  intro x hx y hy h
  have he : RVBoundedMaps.ofRES B x = RVBoundedMaps.ofRES B y :=
    (RVBoundedBalancedTensor.comparison_res B x).symm.trans
      ((congrArg (RVBoundedBalancedTensor.comparison B) h).trans (RVBoundedBalancedTensor.comparison_res B y))
  exact RVZeroDegreeRetraction.bounded_injective_on_degree_zero B hx hy he

def boundedMap (B : Base (M := M)) : resZero B →+* (boundedCoaction B).zeroSubring :=
  ((RVBoundedBalancedTensor.resInclusion B).toRingHom.comp (resZero B).subtype).codRestrict
    (boundedCoaction B).zeroSubring
    (fun x => bounded_tmul_mem B x.property (SetLike.one_mem_graded _))

theorem boundedMap_bijective (B : Base (M := M)) : Function.Bijective (boundedMap B) := by
  constructor
  · intro x y h
    exact Subtype.ext (bounded_injective B x.property y.property (congrArg Subtype.val h))
  · intro x
    obtain ⟨r, hr, hrx⟩ := bounded_surjective B x.property
    exact ⟨⟨r, hr⟩, Subtype.ext hrx⟩

def boundedEquiv (B : Base (M := M)) : resZero B ≃+* (boundedCoaction B).zeroSubring :=
  RingEquiv.ofBijective (boundedMap B) (boundedMap_bijective B)

theorem boundedEquiv_apply (B : Base (M := M)) (x : resZero B) :
    (boundedEquiv B x).val = RVBoundedBalancedTensor.resInclusion B x.val := rfl

def radiusEquiv (B : Base (M := M)) : resZero B ≃+* (RVBalancedRadiusQuotient.coaction B).zeroSubring :=
  (boundedEquiv B).trans (RVBalancedRadiusDegreeZero.zeroEquiv B)

theorem radiusEquiv_apply (B : Base (M := M)) (x : resZero B) :
    (radiusEquiv B x).val = RVBalancedRadiusQuotient.ofRES B x.val := rfl

theorem measured_comparison_injective (B : Base (M := M)) :
    Set.InjOn (RVFiniteBalancedTensor.comparison B) (measuredPiece B 0) := by
  intro x hx y hy h
  obtain ⟨a, ha, rfl⟩ := measured_surjective B hx
  obtain ⟨b, hb, rfl⟩ := measured_surjective B hy
  rw [RVFiniteBalancedTensor.comparison_res, RVFiniteBalancedTensor.comparison_res] at h
  exact congrArg (RVFiniteBalancedTensor.resInclusion B)
    (RVZeroDegreeRetraction.full_injective_on_degree_zero B ha hb h)

theorem bounded_comparison_injective (B : Base (M := M)) :
    Set.InjOn (RVBoundedBalancedTensor.comparison B) (boundedPiece B 0) := by
  intro x hx y hy h
  obtain ⟨a, ha, rfl⟩ := bounded_surjective B hx
  obtain ⟨b, hb, rfl⟩ := bounded_surjective B hy
  rw [RVBoundedBalancedTensor.comparison_res, RVBoundedBalancedTensor.comparison_res] at h
  exact congrArg (RVBoundedBalancedTensor.resInclusion B)
    (RVZeroDegreeRetraction.bounded_injective_on_degree_zero B ha hb h)

theorem radius_comparison_injective (B : Base (M := M)) :
    Set.InjOn (RVBalancedRadiusQuotient.comparison B) ((RVBalancedRadiusQuotient.coaction B).piece 0) := by
  intro x hx y hy h
  obtain ⟨a, ha⟩ := (radiusEquiv B).surjective ⟨x, hx⟩
  obtain ⟨b, hb⟩ := (radiusEquiv B).surjective ⟨y, hy⟩
  have hax : RVBalancedRadiusQuotient.ofRES B a.val = x := congrArg Subtype.val ha
  have hby : RVBalancedRadiusQuotient.ofRES B b.val = y := congrArg Subtype.val hb
  rw [← hax, ← hby, RVBalancedRadiusQuotient.comparison_ofRES, RVBalancedRadiusQuotient.comparison_ofRES] at h
  have he : ReductionDegreeZero.radiusEquiv B a = ReductionDegreeZero.radiusEquiv B b := Subtype.ext h
  have hab : a = b := (ReductionDegreeZero.radiusEquiv B).injective he
  exact hax.symm.trans ((congrArg (fun r : resZero B => RVBalancedRadiusQuotient.ofRES B r.val) hab).trans hby)

end DiamondIntegral.Section4.RVBalancedZeroDegree
