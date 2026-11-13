import «section 4».RESFiniteUnitBalancing
import «section 4».GammaBoundedRVProfiles
import «section 4».GammaPointFamilies

/-! The ordinary RES forgetful map agrees with bounded Gamma evaluation
on the whole intrinsic finite-Gamma ring, for either Euler choice. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAllBoundedFiniteBalancing
open GammaFiniteRVCharts GammaFiniteRVPresentation GammaFiniteGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def resMap (B : Base (M := M)) : ChartRing B →+* RESOrdinaryReduction.ReducedRing B :=
  (RESOrdinaryReduction.forget B).comp (GammaFiniteRVMaps.sharp B)

def gammaMap (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) : ChartRing B →+* RESOrdinaryReduction.ReducedRing B :=
  (GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom.comp (GammaFiniteRVMaps.bounded B)

theorem gammaMap_class (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : FiniteChart B n) :
    gammaMap hc h00 linear hκ hs B hr hγ hΓ k (objectClass a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : RESOrdinaryReduction.ReducedRing B) *
        RESOrdinaryReduction.torusClass B ^ n := by
  change GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryReduction.torusClass B)
    (GammaBoundedRVMaps.auxiliary B (GammaFiniteRVMaps.bounded B (objectClass a))) = _
  rw [GammaFiniteRVMaps.bounded_class, GammaBoundedRVMaps.auxiliary_class]
  exact GammaBoundedChartMap.specialize_boundedClass hc h00 linear hκ hs B hr hγ hΓ k a.toChart
    (GammaFiniteBounds.finite_domain_bounded a.support a.finite_support) (RESOrdinaryReduction.torusClass B)

theorem weightedUnit_balance (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    resMap B (objectClass (weightedUnit B β hβ)) = gammaMap hc h00 linear hκ hs B hr hγ hΓ k (objectClass (weightedUnit B β hβ)) := by
  calc
    resMap B (objectClass (weightedUnit B β hβ)) = 1 := by
      change RESOrdinaryReduction.forget B (GammaFiniteRVMaps.sharp B (objectClass (weightedUnit B β hβ))) = 1
      rw [RESFiniteUnitBalancing.sharp_weightedUnit_class]
      exact RESOrdinaryReduction.forget_weightedUnit B β hβ
    _ = gammaMap hc h00 linear hκ hs B hr hγ hΓ k (objectClass (weightedUnit B β hβ)) := by
      symm
      rw [gammaMap_class]
      have hi : GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 0
          (GammaIndicators.indicatorFamily B Set.univ (GammaIntegerFamilies.univ_definable_base B 0)) = 1 := by
        simp [GammaIteratedIntegral.integrateAll, GammaIteratedIntegral.evaluateZero, GammaIndicators.indicatorFamily]
      change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 0
        (GammaIndicators.indicatorFamily B Set.univ (GammaIntegerFamilies.univ_definable_base B 0)) : RESOrdinaryReduction.ReducedRing B) *
          RESOrdinaryReduction.torusClass B ^ 0 = 1
      rw [hi, Int.cast_one, pow_zero, mul_one]

theorem fibre_balance (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    resMap B (objectClass (fibre B α β hα hβ)) = gammaMap hc h00 linear hκ hs B hr hγ hΓ k (objectClass (fibre B α β hα hβ)) := by
  have hl : resMap B (objectClass (fibre B α β hα hβ)) = RESOrdinaryReduction.torusClass B := by
    change RESOrdinaryReduction.forget B (GammaFiniteRVMaps.sharp B (objectClass (fibre B α β hα hβ))) = _
    rw [GammaFiniteRVMaps.sharp_class]
    exact RESOrdinaryReduction.forget_fibre B α β hα hβ
  have hr' : gammaMap hc h00 linear hκ hs B hr hγ hΓ k (objectClass (fibre B α β hα hβ)) = RESOrdinaryReduction.torusClass B := by
    rw [gammaMap_class]
    have hi : GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 1
        (GammaIndicators.indicatorFamily B {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
          (GammaDefinableMaps.constant_definable (n := 0) B α hα)) = 1 := by
      apply GammaPointFamilies.integrateAll_singleton h00 hκ hs B hr hγ k 1 _ ![α] 1
      intro z
      have he : z = ![α] ↔ z 0 = α := by
        constructor
        · intro h; exact congrFun h 0
        · intro h; funext i; fin_cases i; exact h
      by_cases hz : z 0 = α <;> simp [GammaIndicators.indicatorFamily, he, hz]
    change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 1
      (GammaIndicators.indicatorFamily B {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
        (GammaDefinableMaps.constant_definable (n := 0) B α hα)) : RESOrdinaryReduction.ReducedRing B) *
          RESOrdinaryReduction.torusClass B ^ 1 = RESOrdinaryReduction.torusClass B
    rw [hi, Int.cast_one, pow_one, one_mul]
  exact hl.trans hr'.symm

theorem finite_balance (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    resMap B = gammaMap hc h00 linear hκ hs B hr hγ hΓ k := by
  apply hom_ext_by_generators B
  · intro β hβ
    exact weightedUnit_balance hc h00 linear hκ hs B hr hγ hΓ k β hβ
  · intro α β hα hβ
    exact fibre_balance hc h00 linear hκ hs B hr hγ hΓ k α β hα hβ

theorem finite_balance_apply (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : ChartRing B) :
    RESOrdinaryReduction.forget B (GammaFiniteRVMaps.sharp B x) =
      GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k (GammaFiniteRVMaps.bounded B x) :=
  RingHom.congr_fun (finite_balance hc h00 linear hκ hs B hr hγ hΓ k) x

end DiamondIntegral.Section4.RESAllBoundedFiniteBalancing
