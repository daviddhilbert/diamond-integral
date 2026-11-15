import «section 5».Completed18RelativeCells
import «section 5».Completed18FiniteBases
import IntegrationSection6.GammaRVParameterFieldBase

/-! Completed [18] two-order comparison over a definable extension of an
arbitrary original base. The extension consists only of definable names. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section4 IntegrationInACVF.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure RelativeCor58Data (κ : Cardinal) (B : Base (M := M)) {m : ℕ} (U : Set (Point (M := M) 2 m)) where
  workBase : Base (M := M)
  work_small : Cardinal.mk workBase.real < κ
  definable_in : BaseDefinableIn workBase B
  injection : PositionedCellLabelInjection workBase U
  comparison : GammaMixedStandardComparison workBase injection.target

theorem completed_relative_corollary_5_8 {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {m : ℕ} (U : Set (Point (M := M) 2 m)) (hU : GammaSetDefinable B U) :
    Nonempty (RelativeCor58Data κ B U) := by
  obtain ⟨G,F,hG,hr,hδG,hGB,r,z,hz,hUGz⟩ := finite_generated_rv_parameter_base hκ B δ hδ U hU
  let E := RVLabelSlices.labelBase G z
  obtain ⟨T⟩ := positioned_cells_with_rv_parameters hκ.le hs h00 G hr hG δ hδG hδ1 z U hUGz
  have hEB : BaseDefinableIn E B := by
    refine ⟨?_,hGB.2⟩
    rintro x (hx | ⟨i,rfl⟩)
    · exact hGB.1 hx
    · exact (subset_closureBase B).1 (hz i)
  have hEsmall : Cardinal.mk E.real < κ := small_union_range hκ.le G.real hr (fun i => (z i).val)
  let FE : VFFieldBase E.real := VFFieldBase.withRVParameters F (fun i => (z i).val) (fun i => (z i).property)
  obtain ⟨C⟩ := T.full_standard_comparison hκ.le hs h00 hEsmall δ hδG hδ1 FE
  exact ⟨⟨E,hEsmall,hEB,T,C⟩⟩

end DiamondIntegral.Section5
