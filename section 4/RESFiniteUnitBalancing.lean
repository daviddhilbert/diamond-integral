import «section 4».GammaFiniteGenerators
import «section 4».GammaFiniteRVMaps
import «section 4».GammaRVMapGradings
import «section 4».RVCoordinateMaps

/-! The degree-zero finite-Gamma balancing calculation uses actual
weighted RES units for all original-base definable Gamma weights. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESFiniteUnitBalancing
open RVMeasuredCharts GammaFiniteGenerators GammaFiniteRVPresentation
open GammaDefinableEuler GammaDefinableMaps GammaObjectPolynomial GammaPointAlgebra GammaNamesSubgroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def weightedUnitSharpIso (B : Base (M := M)) (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    Iso (GammaFiniteRVCharts.sharp (GammaFiniteGenerators.weightedUnit B β hβ)).toChart
      (weightedRESUnit B β hβ).toChart :=
  RVCoordinateMaps.coordinateIso
    (GammaFiniteRVCharts.sharp (GammaFiniteGenerators.weightedUnit B β hβ)).toChart (weightedRESUnit B β hβ).toChart id
    ⟨(by intro z hz; exact Set.mem_univ _),
      (by intro x hx y hy h; exact h),
      (by intro z hz; exact ⟨z, ⟨fun i => i.elim0, Set.mem_univ _⟩, rfl⟩)⟩
    (by
      intro z hz
      change β * (∏ i : Fin 0, codeValue (z i)) = β * (∏ i : Fin 0, codeValue ((Fin.elim0 : Fin 0 → M) i))
      simp)

theorem sharp_weightedUnit_class (B : Base (M := M)) (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    GammaFiniteRVMaps.sharp B (objectClass (GammaFiniteGenerators.weightedUnit B β hβ)) = RESChartRing.objectClass (weightedRESUnit B β hβ) := by
  rw [GammaFiniteRVMaps.sharp_class]
  exact RESChartRing.objectClass_iso (weightedUnitSharpIso B β hβ)

theorem weightedUnit_polynomial (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    objectPolynomial h00 hκ hs B hr hγ k 0 Set.univ (GammaIntegerFamilies.univ_definable_base B 0)
      (fun _ => β) (constant_definable B β hβ) =
      GammaUnboundedSpecialization.pointMonomial B k 0 (⟨toPaperGamma β, hβ⟩ : additiveNames B) := by
  have hc : profileCoefficient h00 hκ hs B hr hγ k Set.univ (GammaIntegerFamilies.univ_definable_base B 0)
      (fun _ : Fin 0 → Values.Gamma (M := M) => β) (constant_definable B β hβ) =
      pointMonoidHom B k (Multiplicative.ofAdd (⟨toPaperGamma β, hβ⟩ : additiveNames B)) := by
    apply Subtype.ext
    change (GammaWeightProfiles.profile h00 hκ hs B hr hγ k Set.univ (GammaIntegerFamilies.univ_definable_base B 0)
      (fun _ => β) (constant_definable B β hβ)).val = EulerFunction.point k (toPaperGamma β)
    have h := GammaZeroDegreeProfile.profile_zero_degree h00 hκ hs B hr hγ k Set.univ
      (GammaIntegerFamilies.univ_definable_base B 0) (fun _ => β) (constant_definable B β hβ)
    simpa only [Set.mem_univ, ite_true, one_zsmul] using h
  apply Subtype.ext
  exact congrArg (Polynomial.monomial 0) hc

theorem unbounded_weightedUnit_value (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k
      (GammaFiniteRVMaps.forget B (objectClass (GammaFiniteGenerators.weightedUnit B β hβ))) = RESMeasuredReduction.weightValue B β hβ := by
  rw [GammaFiniteRVMaps.forget_class]
  change RESUnboundedPsi.psi B k (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k
    (GammaRVChartPresentation.objectClass (GammaFiniteGenerators.weightedUnit B β hβ).toChart)) = _
  have hi := congrArg (RESUnboundedPsi.psi B k) (GammaRVChartPresentation.interpretation_symbol
    h00 linear hκ hs B hr hγ hΓ k (GammaFiniteGenerators.weightedUnit B β hβ).toChart)
  have hp : GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ k (GammaFiniteGenerators.weightedUnit B β hβ).toChart =
      GammaUnboundedSpecialization.pointMonomial B k 0 (⟨toPaperGamma β, hβ⟩ : additiveNames B) :=
    (GammaChartOperations.chartPolynomial_ofTotal h00 hκ hs B hr hγ k 0 Set.univ
      (GammaIntegerFamilies.univ_definable_base B 0) (fun _ => β) (constant_definable B β hβ)).trans
        (weightedUnit_polynomial h00 hκ hs B hr hγ k β hβ)
  exact hi.trans ((congrArg (RESUnboundedPsi.psi B k) hp).trans
    ((RESUnboundedPsi.psi_point_zero B k (⟨toPaperGamma β, hβ⟩ : additiveNames B)).trans
      (RESMeasuredReduction.weightCharacter_value B (⟨toPaperGamma β, hβ⟩ : additiveNames B))))

theorem unbounded_weightedUnit_balance (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    RESMeasuredReduction.quotient B (GammaFiniteRVMaps.sharp B (objectClass (GammaFiniteGenerators.weightedUnit B β hβ))) =
      GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k
        (GammaFiniteRVMaps.forget B (objectClass (GammaFiniteGenerators.weightedUnit B β hβ))) := by
  rw [sharp_weightedUnit_class, unbounded_weightedUnit_value]
  rfl

end DiamondIntegral.Section4.RESFiniteUnitBalancing
