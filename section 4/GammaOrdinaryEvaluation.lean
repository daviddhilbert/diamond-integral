import «section 4».GammaEulerEvaluation
import «section 4».GammaFiniteGenerators
import «section 4».RESFiniteUnitBalancing

/-! Both unmeasured Euler evaluations on the full RV-lift-restricted
Gamma presentation are graded and balance over the entire intrinsic
finite-Gamma ring with ordinary RES. No boundedness or canonical-structure
premise is imposed on this full Gamma evaluation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryEvaluation
open GammaFiniteRVCharts GammaFiniteRVPresentation GammaFiniteGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaRVChartPresentation.ChartRing B →+* RESOrdinaryReduction.ReducedRing B :=
  GammaEulerEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryReduction.torusClass B)

theorem evaluation_class (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (GammaRVChartPresentation.objectClass a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : RESOrdinaryReduction.ReducedRing B) *
          RESOrdinaryReduction.torusClass B ^ n :=
  GammaEulerEvaluation.evaluation_class h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryReduction.torusClass B) a

theorem evaluation_class_mem (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (GammaRVChartPresentation.objectClass a) ∈ RESReductionGradings.ordinaryPiece B n := by
  rw [evaluation_class]
  simpa only [zero_add] using SetLike.mul_mem_graded
    (RESPsiGradings.ordinary_intCast_mem B (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
      (GammaIndicators.indicatorFamily B a.support a.support_definable)))
    (RESPsiGradings.ordinary_torus_pow_mem B n)

def gradedEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (GammaRVGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B) where
  toRingHom := evaluation h00 linear hκ hs B hr hγ hΓ k
  map_mem := GammaRVGrading.map_mem_of_classes B (RESReductionGradings.ordinaryCoaction B)
    (evaluation h00 linear hκ hs B hr hγ hΓ k)
    (fun _ a => evaluation_class_mem h00 linear hκ hs B hr hγ hΓ k a)

def resMap (B : Base (M := M)) : ChartRing B →+* RESOrdinaryReduction.ReducedRing B :=
  (RESOrdinaryReduction.forget B).comp (GammaFiniteRVMaps.sharp B)

def gammaMap (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) : ChartRing B →+* RESOrdinaryReduction.ReducedRing B :=
  (evaluation h00 linear hκ hs B hr hγ hΓ k).comp (GammaFiniteRVMaps.forget B)

theorem gammaMap_class (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : FiniteChart B n) :
    gammaMap h00 linear hκ hs B hr hγ hΓ k (objectClass a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : RESOrdinaryReduction.ReducedRing B) *
          RESOrdinaryReduction.torusClass B ^ n := by
  change evaluation h00 linear hκ hs B hr hγ hΓ k (GammaFiniteRVMaps.forget B (objectClass a)) = _
  rw [GammaFiniteRVMaps.forget_class, evaluation_class]

theorem weightedUnit_balance (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    resMap B (objectClass (weightedUnit B β hβ)) = gammaMap h00 linear hκ hs B hr hγ hΓ k (objectClass (weightedUnit B β hβ)) := by
  calc
    resMap B (objectClass (weightedUnit B β hβ)) = 1 := by
      change RESOrdinaryReduction.forget B (GammaFiniteRVMaps.sharp B (objectClass (weightedUnit B β hβ))) = 1
      rw [RESFiniteUnitBalancing.sharp_weightedUnit_class]
      exact RESOrdinaryReduction.forget_weightedUnit B β hβ
    _ = gammaMap h00 linear hκ hs B hr hγ hΓ k (objectClass (weightedUnit B β hβ)) := by
      symm
      rw [gammaMap_class]
      have hi : GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 0
          (GammaIndicators.indicatorFamily B Set.univ (GammaIntegerFamilies.univ_definable_base B 0)) = 1 := by
        simp [GammaIteratedIntegral.integrateAll, GammaIteratedIntegral.evaluateZero, GammaIndicators.indicatorFamily]
      change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 0
        (GammaIndicators.indicatorFamily B Set.univ (GammaIntegerFamilies.univ_definable_base B 0)) : RESOrdinaryReduction.ReducedRing B) *
          RESOrdinaryReduction.torusClass B ^ 0 = 1
      rw [hi, Int.cast_one, pow_zero, mul_one]

theorem fibre_balance (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    resMap B (objectClass (fibre B α β hα hβ)) = gammaMap h00 linear hκ hs B hr hγ hΓ k (objectClass (fibre B α β hα hβ)) := by
  have hl : resMap B (objectClass (fibre B α β hα hβ)) = RESOrdinaryReduction.torusClass B := by
    change RESOrdinaryReduction.forget B (GammaFiniteRVMaps.sharp B (objectClass (fibre B α β hα hβ))) = _
    rw [GammaFiniteRVMaps.sharp_class]
    exact RESOrdinaryReduction.forget_fibre B α β hα hβ
  have hr' : gammaMap h00 linear hκ hs B hr hγ hΓ k (objectClass (fibre B α β hα hβ)) = RESOrdinaryReduction.torusClass B := by
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

theorem finite_balance (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    resMap B = gammaMap h00 linear hκ hs B hr hγ hΓ k := by
  apply hom_ext_by_generators B
  · intro β hβ
    exact weightedUnit_balance h00 linear hκ hs B hr hγ hΓ k β hβ
  · intro α β hα hβ
    exact fibre_balance h00 linear hκ hs B hr hγ hΓ k α β hα hβ

theorem finite_balance_apply (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : ChartRing B) :
    RESOrdinaryReduction.forget B (GammaFiniteRVMaps.sharp B x) =
      evaluation h00 linear hκ hs B hr hγ hΓ k (GammaFiniteRVMaps.forget B x) :=
  RingHom.congr_fun (finite_balance h00 linear hκ hs B hr hγ hΓ k) x


end DiamondIntegral.Section4.GammaOrdinaryEvaluation
