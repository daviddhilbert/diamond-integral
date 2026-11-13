import «section 4».RESFiniteUnitBalancing
import «section 4».RESFiniteBalancing

/-! The measured RES quotient and constructed Gamma evaluation agree
on the whole intrinsic finite-Gamma ring. This supplies full balancing
for that presentation, without a global RV kernel or descent theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAllFiniteBalancing
open GammaFiniteRVPresentation GammaFiniteGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def resMap (B : Base (M := M)) : ChartRing B →+* RESMeasuredReduction.ReducedRing B :=
  (RESMeasuredReduction.quotient B).comp (GammaFiniteRVMaps.sharp B)

def gammaMap (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) : ChartRing B →+* RESMeasuredReduction.ReducedRing B :=
  (GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom.comp (GammaFiniteRVMaps.forget B)

theorem fibre_balance (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    resMap B (objectClass (fibre B α β hα hβ)) = gammaMap h00 linear hκ hs B hr hγ hΓ k (objectClass (fibre B α β hα hβ)) := by
  change RESMeasuredReduction.quotient B (GammaFiniteRVMaps.sharp B (objectClass (fibre B α β hα hβ))) =
    GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k
      (GammaFiniteRVMaps.forget B (objectClass (fibre B α β hα hβ)))
  rw [GammaFiniteRVMaps.sharp_class, GammaFiniteRVMaps.forget_class]
  change RESMeasuredReduction.quotient B (RESChartRing.objectClass (RESFibreObjects.fibre B α β hα hβ)) =
    RESUnboundedPsi.psi B k (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k
      (GammaRVChartPresentation.objectClass (RESFibreObjects.gammaFibre B α β hα hβ)))
  have hi := congrArg (RESUnboundedPsi.psi B k) (GammaRVChartPresentation.interpretation_symbol
    h00 linear hκ hs B hr hγ hΓ k (RESFibreObjects.gammaFibre B α β hα hβ))
  have hp := congrArg (RESUnboundedPsi.psi B k) (GammaChartOperations.chartPolynomial_ofTotal
    h00 hκ hs B hr hγ k 1 {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
    (GammaDefinableMaps.constant_definable (n := 0) B α hα) (fun _ => β) (GammaDefinableMaps.constant_definable B β hβ))
  exact (hi.trans (hp.trans (RESFiniteBalancing.psi_singleton_fibre h00 hκ hs B hr hγ k α β hα hβ))).symm

theorem finite_balance (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    resMap B = gammaMap h00 linear hκ hs B hr hγ hΓ k := by
  apply hom_ext_by_generators B
  · intro β hβ
    exact RESFiniteUnitBalancing.unbounded_weightedUnit_balance h00 linear hκ hs B hr hγ hΓ k β hβ
  · intro α β hα hβ
    exact fibre_balance h00 linear hκ hs B hr hγ hΓ k α β hα hβ

theorem finite_balance_apply (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : ChartRing B) :
    RESMeasuredReduction.quotient B (GammaFiniteRVMaps.sharp B x) =
      GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k (GammaFiniteRVMaps.forget B x) :=
  RingHom.congr_fun (finite_balance h00 linear hκ hs B hr hγ hΓ k) x

end DiamondIntegral.Section4.RESAllFiniteBalancing
