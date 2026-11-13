import «section 3».UnmeasuredTensorQuotientGrading
import «section 3».MeasuredTensorQuotientGrading
import «section 3».GammaGroundContext
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}

/-- The context's nontrivial Gamma names suffice; no nontrivial value
or RV representative in its VF-generated real part is required. -/
theorem GammaGroundContext.nontrivial_definable_gamma (C : GammaGroundContext M) :
    Section2.NontrivialDefinableGamma C.base := by
  obtain ⟨γ,hγ,hne⟩ := C.nontrivial_values
  exact Section2.nontrivialDefinableGamma_of_names C.base γ 1 hγ C.gamma.one_mem hne

/-- Corrected Proposition 3.18 at the actual full Gamma-ground context:
the unmeasured positive tensor is presented by the explicit congruence. -/
def proposition_3_18_unmeasured (C : GammaGroundContext M) :
    GammaGroundUnmeasuredCoefficientQuotient hc C.base ≃+* GammaGroundRVPositiveSemiring hc C.base :=
  gammaGroundUnmeasuredCoefficientQuotientEquiv C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

/-- The measured presentation retains every volume form, including on
finite factors and in degree zero, before any groupification. -/
def proposition_3_18_measured (C : GammaGroundContext M) :
    GammaGroundMeasuredCoefficientQuotient hc C.base ≃+* GammaGroundMeasuredRVPositiveSemiring hc C.base :=
  gammaGroundMeasuredCoefficientQuotientEquiv C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

theorem proposition_3_18_unmeasured_kernel (C : GammaGroundContext M) :
    gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := C.base) =
      RingCon.ker (gammaGroundUnmeasuredTensorMap (hc := hc) (ground := C.base)) :=
  gammaGroundUnmeasuredCoefficientCongruence_eq_ker C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

theorem proposition_3_18_measured_kernel (C : GammaGroundContext M) :
    gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := C.base) =
      RingCon.ker (gammaGroundMeasuredTensorMap (hc := hc) (ground := C.base)) :=
  gammaGroundMeasuredCoefficientCongruence_eq_ker C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

def proposition_3_18_unmeasured_graded (C : GammaGroundContext M) :
    GammaGroundUnmeasuredCoefficientQuotient hc C.base ≃+* GammaGroundRVDirectSum hc C.base :=
  gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

def proposition_3_18_measured_graded (C : GammaGroundContext M) :
    GammaGroundMeasuredCoefficientQuotient hc C.base ≃+* GammaGroundMeasuredRVDirectSum hc C.base :=
  gammaGroundMeasuredCoefficientQuotientEquivDirectSum C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma
end DiamondIntegral.Section3
