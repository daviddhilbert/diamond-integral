import «section 3».GammaMixedContractionValues
import «section 3».GammaSmallDimensionContractionValues
import «section 3».GammaGroundVFDimensionMaps

/-! The mixed contraction value vanishes on every intrinsically
VF-small domain. A genuine retained presentation preserves intrinsic
dimension, so the checked raw vanishing theorem applies directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRetained_small_contraction_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hNames : commonRealNames B ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase B)
    (U : GammaRetainedMeasuredVFData hc B (n+1))
    (hsmall : Section2.vfDimension U.domain.carrier < ((n+1 : ℕ) : WithBot ℕ)) :
    U.contractionValue C hBC hNames hGenerated = 0 := by
  let A := U.nativeSet C hNames
  have hdim : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      (rawSpecialSet hc A) < n+1 :=
    (vf_small_iff_companion hc C.saturated C.small hv (Nat.succ_pos n) (rawSpecialSet hc A)).mp hsmall
  exact gammaSmall_dimension_contraction_value C hBC A U.point_definable U.finite
    (U.contraction C hBC hNames hGenerated) (U.contraction_gamma C hBC hNames hGenerated) hdim U.form.extendByOne

theorem gammaMixed_small_contraction_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (U : GammaGroundMeasuredVFData hc B (n+1))
    (hsmall : Section2.vfDimension U.domain.carrier < ((n+1 : ℕ) : WithBot ℕ)) :
    gammaMixedContractionValue C hBC hv hg hGenerated U = 0 := by
  let C' := gammaMixedCodeContext C hBC hg
  have hBC' := gammaMixedCodeContext_real C hBC hg
  have hNames' := gammaMixedCodeContext_names C hBC hg
  have hg' := gammaMixedCodeContext_gamma C hBC hg
  let P := gammaMixedRetainedRepresentation C' hBC' hv U
  have hdim := gammaGroundVFDimension_eq_of_bijection P.map.map C'.uncountable.le C'.saturated
    ((Cardinal.mk_le_mk_of_subset hBC').trans_lt C'.small) hv
  exact gammaRetained_small_contraction_value C' hBC' hv hNames' hGenerated P.data (hdim ▸ hsmall)

end DiamondIntegral.Section3
