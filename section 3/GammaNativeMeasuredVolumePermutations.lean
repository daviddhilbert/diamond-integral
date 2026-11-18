import «section 3».GammaNativeChainDensity
import «section 3».GammaNativeMeasuredIsomorphisms
import «section 3».GammaNativeStructuralValues
import IntegrationSection6.FiniteGammaVolumeReindexing

/-! Permuting structural RV volume coordinates retains the full Gamma
weight and hence the original principal class. The existing native
Gamma reindexing isomorphism retains every actual RV label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable (U : GammaObjectAt B Set.univ (n+1)) (σ : Equiv.Perm (Fin (n+1)))

def gammaNativeVolumePermutation :
    GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain (U.reindexVolume σ)) :=
  Section5.nativeRVGroundIso (gammaReindexVolumeIsoAt U σ)

theorem gammaNativeVolumePermutation_label (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    (gammaNativeVolumePermutation U σ |>.map u).val = u.val := rfl

theorem gammaNativeVolumePermutation_volume (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    (Section5.nativeRVGroundVolume (U.reindexVolume σ) ((gammaNativeVolumePermutation U σ).map u)).val =
      (Section5.nativeRVGroundVolume U u).val ∘ σ := by
  have hNew := gammaNativeRVGroundVolume_value (U.reindexVolume σ) ((gammaNativeVolumePermutation (hc := hc) U σ).map u)
  have hOld := gammaNativeRVGroundVolume_value U u
  exact hNew.trans (congrArg (fun v => v ∘ σ) hOld.symm)

def gammaNativePermutedForm
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (U.reindexVolume σ)) :=
  ω.comp (gammaNativeVolumePermutation U σ).symm.map

theorem gammaNativePermutedForm_value
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    gammaNativePermutedForm U σ ω ((gammaNativeVolumePermutation U σ).map u) = ω u :=
  congrArg ω ((gammaNativeVolumePermutation U σ).map.inverse_apply (gammaNativeVolumePermutation U σ).bijective u)

def gammaNativeVolumePermutationMeasured
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω)
      (gammaNativeMeasuredNormalization (U.reindexVolume σ) (gammaNativePermutedForm U σ ω)) := by
  apply gammaNativeMeasuredNormalizationHom ω (gammaNativePermutedForm U σ ω) (gammaReindexVolumeIsoAt U σ)
  intro u
  let E := gammaNativeVolumePermutation (hc := hc) U σ
  have hForm : gammaGroundFormValue ω u =
      gammaGroundFormValue (gammaNativePermutedForm U σ ω) (E.map u) :=
    congrArg (cast (gammaCarrier hc)) (congrArg Subtype.val (gammaNativePermutedForm_value U σ ω u)).symm
  have hProd : (∏ j, Values.vrv ((Section5.nativeRVGroundVolume (U.reindexVolume σ) (E.map u)).val j)) =
      ∏ j, Values.vrv ((Section5.nativeRVGroundVolume U u).val j) :=
    (congrArg (fun v => ∏ j, Values.vrv (v j)) (gammaNativeVolumePermutation_volume U σ u)).trans
      (Equiv.prod_comp σ (fun j => Values.vrv ((Section5.nativeRVGroundVolume U u).val j)))
  exact congrArg₂ (fun a b : Values.GammaTop (M := M) => a*b) (congrArg Subtype.val hForm) hProd.symm

theorem gammaNativeVolumePermutation_class
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass (U.reindexVolume σ) (gammaNativePermutedForm U σ ω) :=
  gammaNativeSpecialClass_hom U (U.reindexVolume σ) ω (gammaNativePermutedForm U σ ω)
    (gammaNativeVolumePermutationMeasured U σ ω)

end DiamondIntegral.Section3
