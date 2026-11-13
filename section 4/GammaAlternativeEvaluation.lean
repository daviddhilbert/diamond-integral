import «section 4».RESAlternativePsi
import «section 4».RESAllFiniteBalancing

/-! The alternative geometric evaluation is graded on the actual Gamma
presentation and balances over the whole intrinsic finite-Gamma ring.
Positive Gamma degree uses numerical Euler integration; degree zero
retains its original volume weights. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaAlternativeEvaluation
open RESAlternativeReduction GammaFiniteRVCharts GammaFiniteRVPresentation GammaFiniteGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradedEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    GradedRingHom (GammaRVGrading.gradedPiece B) (piece B) :=
  (RESAlternativePsi.gradedPsi B).comp
    (GammaRVMapGradings.gradedInterpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric)

def evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) : GammaRVChartPresentation.ChartRing B →+* Ring B :=
  (gradedEvaluation h00 linear hκ hs B hr hγ hΓ).toRingHom

theorem evaluation_class_positive (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {n : ℕ} (hn : n ≠ 0) (a : GammaWeightedCharts.Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ (GammaRVChartPresentation.objectClass a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ EulerKind.geometric n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : Ring B) * torusClass B ^ n := by
  change RESAlternativePsi.psi B (GammaRVChartPresentation.interpretation
    h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (GammaRVChartPresentation.objectClass a)) = _
  have hi := congrArg (RESAlternativePsi.psi B) (GammaRVChartPresentation.interpretation_symbol
    h00 linear hκ hs B hr hγ hΓ EulerKind.geometric a)
  apply hi.trans
  calc
    RESAlternativePsi.psi B (GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ EulerKind.geometric a) =
        GammaEulerEvaluation.polynomial B EulerKind.geometric (torusClass B)
          (GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ EulerKind.geometric a) := by
      rw [RESAlternativePsi.psi_positive B _ n hn _ rfl]
      change _ = Polynomial.eval₂ _ _ (Polynomial.monomial n _)
      rw [Polynomial.eval₂_monomial]
      rfl
    _ = _ := GammaEulerEvaluation.polynomial_chart h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (torusClass B) a

def resMap (B : Base (M := M)) : ChartRing B →+* Ring B :=
  (fromMeasured B).comp (GammaFiniteRVMaps.sharp B)

def gammaMap (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) : ChartRing B →+* Ring B :=
  (evaluation h00 linear hκ hs B hr hγ hΓ).comp (GammaFiniteRVMaps.forget B)

theorem weightedUnit_balance (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    resMap B (objectClass (weightedUnit B β hβ)) =
      gammaMap h00 linear hκ hs B hr hγ hΓ (objectClass (weightedUnit B β hβ)) := by
  change fromMeasured B (GammaFiniteRVMaps.sharp B (objectClass (weightedUnit B β hβ))) =
    evaluation h00 linear hκ hs B hr hγ hΓ (GammaFiniteRVMaps.forget B (objectClass (weightedUnit B β hβ)))
  rw [RESFiniteUnitBalancing.sharp_weightedUnit_class, GammaFiniteRVMaps.forget_class]
  change fromMeasured B (RESChartRing.objectClass (RVMeasuredCharts.weightedRESUnit B β hβ)) =
    RESAlternativePsi.psi B (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
      (GammaRVChartPresentation.objectClass (weightedUnit B β hβ).toChart))
  have hi := congrArg (RESAlternativePsi.psi B) (GammaRVChartPresentation.interpretation_symbol
    h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (weightedUnit B β hβ).toChart)
  have hp : GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ EulerKind.geometric (weightedUnit B β hβ).toChart =
      GammaUnboundedSpecialization.pointMonomial B EulerKind.geometric 0
        (⟨GammaDefinableEuler.toPaperGamma β, hβ⟩ : GammaNamesSubgroup.additiveNames B) :=
    (GammaChartOperations.chartPolynomial_ofTotal h00 hκ hs B hr hγ EulerKind.geometric 0 Set.univ
      (GammaIntegerFamilies.univ_definable_base B 0) (fun _ => β) (GammaDefinableMaps.constant_definable B β hβ)).trans
        (RESFiniteUnitBalancing.weightedUnit_polynomial h00 hκ hs B hr hγ EulerKind.geometric β hβ)
  exact (hi.trans ((congrArg (RESAlternativePsi.psi B) hp).trans
    (RESAlternativePsi.psi_point_zero B
      (⟨GammaDefinableEuler.toPaperGamma β, hβ⟩ : GammaNamesSubgroup.additiveNames B)))).symm

theorem fibre_balance (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    resMap B (objectClass (fibre B α β hα hβ)) =
      gammaMap h00 linear hκ hs B hr hγ hΓ (objectClass (fibre B α β hα hβ)) := by
  have hl : resMap B (objectClass (fibre B α β hα hβ)) = torusClass B := by
    change quotient B (RESMeasuredReduction.quotient B
      (GammaFiniteRVMaps.sharp B (objectClass (fibre B α β hα hβ)))) = _
    rw [GammaFiniteRVMaps.sharp_class]
    change quotient B (RESMeasuredReduction.quotient B (RESChartRing.objectClass (RESFibreObjects.fibre B α β hα hβ))) = _
    rw [RESMeasuredReduction.fibre_class, map_mul]
    exact weighted_torus B (⟨GammaDefinableEuler.toPaperGamma (α * β),
      GammaGroupNames.mul_definable_base B α β hα hβ⟩ : GammaNamesSubgroup.additiveNames B)
  have hr' : gammaMap h00 linear hκ hs B hr hγ hΓ (objectClass (fibre B α β hα hβ)) = torusClass B := by
    change evaluation h00 linear hκ hs B hr hγ hΓ
      (GammaFiniteRVMaps.forget B (objectClass (fibre B α β hα hβ))) = _
    rw [GammaFiniteRVMaps.forget_class, evaluation_class_positive h00 linear hκ hs B hr hγ hΓ (by decide : (1 : ℕ) ≠ 0)]
    have hi : GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ EulerKind.geometric 1
        (GammaIndicators.indicatorFamily B {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
          (GammaDefinableMaps.constant_definable (n := 0) B α hα)) = 1 := by
      apply GammaPointFamilies.integrateAll_singleton h00 hκ hs B hr hγ EulerKind.geometric 1 _ ![α] 1
      intro z
      have he : z = ![α] ↔ z 0 = α := by
        constructor
        · intro h; exact congrFun h 0
        · intro h; funext i; fin_cases i; exact h
      by_cases hz : z 0 = α <;> simp [GammaIndicators.indicatorFamily, he, hz]
    change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ EulerKind.geometric 1
      (GammaIndicators.indicatorFamily B {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
        (GammaDefinableMaps.constant_definable (n := 0) B α hα)) : Ring B) * torusClass B ^ 1 = torusClass B
    rw [hi, Int.cast_one, pow_one, one_mul]
  exact hl.trans hr'.symm

theorem finite_balance (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    resMap B = gammaMap h00 linear hκ hs B hr hγ hΓ := by
  apply hom_ext_by_generators B
  · exact weightedUnit_balance h00 linear hκ hs B hr hγ hΓ
  · exact fibre_balance h00 linear hκ hs B hr hγ hΓ

end DiamondIntegral.Section4.GammaAlternativeEvaluation
