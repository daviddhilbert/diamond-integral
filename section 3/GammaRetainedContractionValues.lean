import «section 3».GammaFullRawAllOrderMeasuredValues
import «section 3».GammaRetainedNativeMeasuredPresentations

/-! Retained-density mixed objects have a contraction value independent
of every specified preparation and VF order. The choice below selects
only an actual checked standard contraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
namespace GammaRetainedMeasuredVFData
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hNames : commonRealNames B ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase B)
variable (U : GammaRetainedMeasuredVFData hc B (n+1))

def contraction : StandardContraction (U.nativeSet C hNames) (Equiv.refl _) :=
  (generated_base_standard_contraction_exists C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hGenerated hBC
    (U.nativeSet C hNames) U.point_definable (Equiv.refl _)).choose

theorem contraction_gamma : GammaProgramDefinable B (U.contraction C hBC hNames hGenerated).program :=
  (generated_base_standard_contraction_exists C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hGenerated hBC
    (U.nativeSet C hNames) U.point_definable (Equiv.refl _)).choose_spec.1

def contractionValue := gammaMeasuredPrincipalValue
  (gammaNativeRawMeasuredContraction C hBC (A := U.nativeSet C hNames) U.point_definable U.finite
    (U.contraction C hBC hNames hGenerated) (U.contraction_gamma C hBC hNames hGenerated) U.form.extendByOne)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem contractionValue_eq
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction (U.nativeSet C hNames) σ)
    (hT : GammaProgramDefinable B T.program) :
    U.contractionValue C hBC hNames hGenerated =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC (A := U.nativeSet C hNames) U.point_definable U.finite T hT U.form.extendByOne) :=
  gammaFull_raw_all_order_measured_values C hBC hv hg hNames hGenerated δ hδ hδ1
    (U.nativeSet C hNames) U.point_definable U.finite U.form.extendByOne
    (U.contraction C hBC hNames hGenerated) T (U.contraction_gamma C hBC hNames hGenerated) hT

end GammaRetainedMeasuredVFData
end DiamondIntegral.Section3
