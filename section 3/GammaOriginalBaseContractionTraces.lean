import «section 3».GammaOriginalBaseHeadTraces
import IntegrationSection5.StandardSpecialPresentation

/-! Every coordinate order has an actual traced contraction and global
special presentation over the original Gamma base. Definably named VF
field coefficients are eliminated from the complete certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {S : Set M} {n a l : ℕ}

theorem gammaProgram_reduce (H : GammaDefinableBaseReduction C B)
    {A : DefSet (M := M) S n a} {D : DefSet (M := M) S 0 l}
    (P : OrderedContractionProgram S A D) (hP : GammaProgramDefinable C P) :
    GammaProgramDefinable B P := by
  induction P with
  | zero A => exact H.definable hP
  | step T tail ih => exact ⟨H.definable hP.1,H.definable hP.2.1,ih hP.2.2⟩

theorem gamma_original_base_standard_contraction_traced
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ C : StandardContraction A σ, GammaProgramDefinable B C.program ∧
      ∃ R : StandardNaturalTrace C, GammaUniformTrace (G := B) R.trace := by
  let D := vfFieldNamedBase B
  have hAD : GammaSetDefinable D (carrier A) := hA.mono Set.subset_union_left (Set.Subset.refl _)
  obtain ⟨C,hC,R,hR⟩ := standard_contraction_exists_gamma_traced hs h00 D
    (vfFieldNamedBase_small B hκ hr) (vfFieldNamedBase_field B) (Set.subset_univ _) A hAD σ
  let H := vfFieldBaseReduction B
  exact ⟨C,gammaProgram_reduce H C.program hC,R,gammaUniformTrace_reduce H R.trace hR⟩

theorem gamma_original_base_standard_special_presentation
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ C : StandardContraction A σ, GammaProgramDefinable B C.program ∧ Nonempty (StandardSpecialPresentation B C) := by
  obtain ⟨C,hC,R,hR⟩ := gamma_original_base_standard_contraction_traced hκ hs h00 hr A hA σ
  exact ⟨C,hC,standard_special_presentation_of_trace C R hR⟩

end DiamondIntegral.Section3
