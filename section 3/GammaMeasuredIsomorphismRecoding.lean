import «section 3».GammaMeasuredIsomorphismSchemata
import «section 3».GammaMeasuredRowAgreements
import Integration7.VolumeIsoSchemaRowTransport
import IntegrationSection6.GammaSchemaValidityTransport

/-! Exact primitive row recoding preserves measured Gamma charts. The
ordinary chart and Gamma-weight transports are reused verbatim; only the
Gamma quotient-function validity uses its checked replacement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaMeasuredRVIsoSchema.recode (I : GammaMeasuredRVIsoSchema hc B p a b k sp)
    (C : GammaParameterRecode B p q sp sq) : GammaMeasuredRVIsoSchema hc B q a b k sq where
  source := I.source.recode C
  target := I.target.recode C
  chart := (C.relation ⟨I.chart,I.chart_definable⟩).val
  chart_definable := (C.relation ⟨I.chart,I.chart_definable⟩).property

def GammaMeasuredRVIsoSchema.RecodeAgreement (I : GammaMeasuredRVIsoSchema hc B p a b k sp)
    (C : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M) : Prop :=
  (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement I.source.toRVTemplate z t ∧
  (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement I.target.toRVTemplate z t ∧
  C.RelationAgreement ⟨I.chart,I.chart_definable⟩ z t

theorem GammaMeasuredRVIsoSchema.recode_valid
    (I : GammaMeasuredRVIsoSchema hc B p a b k sp) (C : GammaParameterRecode B p q sp sq)
    (z : Fin p → M) (t : Fin q → M) (ht : ∀ i, sortEval (sq i) (t i))
    (h : I.RecodeAgreement C z t) (hI : I.valid z) : (I.recode C).valid t := by
  have hS := (GammaVolumeParameterRecode.mk C).volumeObject_rows I.source.toRVTemplate z t h.1
  have hT := (GammaVolumeParameterRecode.mk C).volumeObject_rows I.target.toRVTemplate z t h.2.1
  refine ⟨I.source.recode_valid C z t ht h.1 hI.1,I.target.recode_valid C z t ht h.2.1 hI.2.1,?_,?_⟩
  · exact I.ordinary.valid_of_rowAgreement (I.recode C).ordinary z t ht rfl rfl
      (essentialFiniteVolumeSchema_rowAgreement hS.1) (essentialFiniteVolumeSchema_rowAgreement hT.1) h.2.2 hI.2.2.1
  · exact volumeChartGammaRowValid_of_rowAgreement hI.1.1.1 ht hS hT h.2.2 hI.2.2.2

end DiamondIntegral.Section3
