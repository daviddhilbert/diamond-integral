import «section 5».Completed18LocalLiftSurjective
import «section 5».Completed18LocalKernel
import «section 5».NativeLiftGroundTransfer
import «section 2».GeneralDiscPoints
import IntegrationSection6.VFParameterCoefficientBases

/-! The exact earlier-section lifting/kernel record is constructed over
the original ground. Definable closure is only an equivalent parameter
presentation; no algebraic extension or change-of-base injectivity is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def completed18OriginalLiftInput (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
    (hγ : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ∈B.gamma) (hδ1 : 1<δ)
    (hB : VFGammaGeneratedBase B) : OriginalBaseUnmeasuredLiftInput hc B where
  lift := completed18LocalLift hκ.le hs h00 hr hB
  lift_class := completed18LocalLift_class hκ.le hs h00 hr hB
  surjective := completed18LocalLift_surjective hκ hs h00 hr hB
  kernel := completed18LocalLift_kernel hκ hs h00 hr FBase hγ δ hδ hδ1 hB

theorem completed18ContextPositive (C : GammaGroundContext M) :
    ∃ δ∈C.base.gamma,1<δ := by
  obtain ⟨γ,hγ⟩ := C.nontrivial_gamma
  by_cases h : 1<γ.val
  · exact ⟨γ.val,γ.property,h⟩
  · exact ⟨γ.val⁻¹,C.gamma.inv_mem γ.property,
      one_lt_inv'.mpr (lt_of_le_of_ne (le_of_not_gt h) hγ)⟩

def completed18GroundLiftInput (C : GammaGroundContext M)
    (hc : CanonicalStructure.IsCanonical (M := M)) : YinGammaGroundUnmeasuredLiftInput C hc := by
  let D := closureBase C.base
  let δ : Values.Gamma (M := M) := (completed18ContextPositive C).choose
  have hδ : δ∈C.base.gamma := (completed18ContextPositive C).choose_spec.1
  have hδ1 : 1<δ := (completed18ContextPositive C).choose_spec.2
  have hr : Cardinal.mk D.real<C.κ := closureBase_real_small C.uncountable C.base C.small_real C.small_gamma
  have hγ : Cardinal.mk D.gamma<C.κ := closureBase_gamma_small C.uncountable C.base C.small_real C.small_gamma
  have hD : VFGammaGeneratedBase D := C.fieldBase.gamma_closure_generated C.base.gamma
  let I : OriginalBaseUnmeasuredLiftInput hc D := completed18OriginalLiftInput hc D C.uncountable
    C.saturated C.model00 hr (closureBase_field C.base) hγ δ ((subset_closureBase C.base).2 hδ) hδ1 hD
  let J : OriginalBaseUnmeasuredLiftInput hc C.base := sortedTransferOriginalLiftInput
    (fun {_} sn U h => (DefinableOverBase.closureBase_iff C.base sn U).mp h)
    (fun {_} sn U h => (DefinableOverBase.closureBase_iff C.base sn U).mpr h) I
  exact ⟨J.lift,J.lift_class,J.surjective,J.kernel⟩

end DiamondIntegral.Section5
