import IntegrationSection5.GammaHeadCertifiedTrace
import IntegrationSection6.GammaFieldBaseReduction

/-! The actual uniform trace certificate descends through a definable
base extension. Head preparations therefore have such certificates over
an arbitrary original real/Gamma base, without a field-base hypothesis. -/
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
variable {B C : Base (M := M)} {S : Set M} {n a b : ℕ}

theorem gammaUniformTrace_reduce (H : GammaDefinableBaseReduction C B)
    {A : DefSet (M := M) S n a} {D : DefSet (M := M) S n b}
    (T : UniformRelativeTrace S n A D) (hT : GammaUniformTrace (G := C) T) :
    GammaUniformTrace (G := B) T := by
  induction T with
  | nil A => exact H.definable hT
  | canonical i tail ih => exact ⟨H.definable hT.1,ih hT.2⟩
  | focus D tail ih => exact ⟨H.definable hT.1,⟨H.definable hT.2.1.locus,H.definable hT.2.1.center⟩,ih hT.2.2⟩

theorem gamma_original_base_head_preparation_traced
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : DefSet (M := M) Set.univ (n+1) a) (hA : GammaSetDefinable B (carrier A)) :
    ∃ T : HeadPreparation A, SpecialRelativeBoundary T.map 0 none (some false) ∧
      (∃ j, Tagged (carrier T.target) 0 j) ∧ GammaSetDefinable B (carrier T.target) ∧
        GammaGraphDefinable B (pointMapGraph T.map) ∧
        ∃ W : UniformRelativeTrace Set.univ (n+1) A T.target,
          GammaUniformTrace (G := B) W ∧ ∀ u, W.toMap u = T.map u := by
  let C := vfFieldNamedBase B
  have hAC : GammaSetDefinable C (carrier A) := hA.mono Set.subset_union_left (Set.Subset.refl _)
  obtain ⟨T,hBound,hTag,hTarget,hMap,W,hWG,hW⟩ := gamma_head_preparation_certified_trace
    hs h00 C (vfFieldNamedBase_small B hκ hr) (vfFieldNamedBase_field B) (Set.subset_univ _) A hAC
  let H := vfFieldBaseReduction B
  exact ⟨T,hBound,hTag,H.definable hTarget,H.definable hMap,W,gammaUniformTrace_reduce H W hWG,hW⟩

end DiamondIntegral.Section3
