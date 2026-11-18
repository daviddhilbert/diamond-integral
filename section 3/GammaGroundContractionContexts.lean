import «section 3».GammaGroundContext
import IntegrationSection6.SmallGammaDefinableClosure
import Section4.SmallGeneratedBase

/-! A small containing code context can be chosen even when the
original real base has trivial valuation. Its extra RV names are used
only internally; the mathematical ground stays the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem GammaGroundContext.exists_positive_gamma (C : GammaGroundContext M) :
    ∃ δ : Values.Gamma (M := M), δ ∈ C.base.gamma ∧ 1 < δ := by
  obtain ⟨γ,hγ,hne⟩ := C.nontrivial_values
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨γ⁻¹,C.gamma.inv_mem hγ,one_lt_inv'.mpr hlt⟩
  · exact ⟨γ,hγ,hgt⟩

def gammaGroundContractionContext (C : GammaGroundContext M) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := Substructure.closure LRV (commonRealNames (closureBase C.base))
  small := small_generated_substructure C.uncountable _
    (commonRealNames_small C.uncountable.le (closureBase C.base)
      (closureBase_real_small C.uncountable C.base C.small_real C.small_gamma)
      (closureBase_gamma_small C.uncountable C.base C.small_real C.small_gamma))
  nontrivial_values := by
    obtain ⟨γ,hγ,hne⟩ := C.nontrivial_values
    have hγP := (subset_closureBase C.base).2 hγ
    have h1P := (subset_closureBase C.base).2 C.gamma.one_mem
    let a := representative γ
    let b := representative (1 : Values.Gamma (M := M))
    refine ⟨⟨raw a,Substructure.subset_closure (Or.inr ⟨γ,hγP,rfl⟩)⟩,
      ⟨raw b,Substructure.subset_closure (Or.inr ⟨1,h1P,rfl⟩)⟩,
      raw_rv a,raw_rv b,raw_ne_zero a,raw_ne_zero b,?_⟩
    intro h
    exact hne ((representative_value γ).symm.trans
      (((value_eq_iff a b).mpr h).trans (representative_value 1)))

theorem gammaGroundContractionContext_contains (C : GammaGroundContext M) :
    commonRealNames (closureBase C.base) ⊆ ((gammaGroundContractionContext C).base : Set M) :=
  Substructure.subset_closure

end DiamondIntegral.Section3
