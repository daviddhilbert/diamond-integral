import «section 4».GammaFiniteRVMaps
import «section 4».RESMeasuredReduction
import «section 4».RESOrdinaryReduction
import Mathlib.Algebra.Algebra.Basic

/-! The actual finite-Gamma coefficient maps give the canonical algebra
structures used by the measured and bounded tensor products. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.FiniteGammaAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance resAlgebra (B : Base (M := M)) :
    Algebra (GammaFiniteRVPresentation.ChartRing B) (RESChartRing.Ring B) := (GammaFiniteRVMaps.sharp B).toAlgebra

instance gammaAlgebra (B : Base (M := M)) :
    Algebra (GammaFiniteRVPresentation.ChartRing B) (GammaRVChartPresentation.ChartRing B) := (GammaFiniteRVMaps.forget B).toAlgebra

instance boundedGammaAlgebra (B : Base (M := M)) :
    Algebra (GammaFiniteRVPresentation.ChartRing B) (GammaBoundedRVPresentation.ChartRing B) := (GammaFiniteRVMaps.bounded B).toAlgebra

instance rvAlgebra (B : Base (M := M)) :
    Algebra (GammaFiniteRVPresentation.ChartRing B) (RVChartRing.Ring B) :=
  ((RVChartMaps.ofRES B).comp (GammaFiniteRVMaps.sharp B)).toAlgebra

instance boundedRVAlgebra (B : Base (M := M)) :
    Algebra (GammaFiniteRVPresentation.ChartRing B) (RVBoundedRing.Ring B) :=
  ((RVBoundedMaps.ofRES B).comp (GammaFiniteRVMaps.sharp B)).toAlgebra

instance measuredTargetAlgebra (B : Base (M := M)) :
    Algebra (GammaFiniteRVPresentation.ChartRing B) (RESMeasuredReduction.ReducedRing B) :=
  ((RESMeasuredReduction.quotient B).comp (GammaFiniteRVMaps.sharp B)).toAlgebra

instance ordinaryTargetAlgebra (B : Base (M := M)) :
    Algebra (GammaFiniteRVPresentation.ChartRing B) (RESOrdinaryReduction.ReducedRing B) :=
  ((RESOrdinaryReduction.forget B).comp (GammaFiniteRVMaps.sharp B)).toAlgebra

end DiamondIntegral.Section4.FiniteGammaAlgebras
