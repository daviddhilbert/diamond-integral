import IntegrationSection5.FullStandardComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters IntegrationInACVF.Section3ACVF

structure Corollary58Data (G : GammaParameters.Base (M := M)) {m : ℕ} (A : Set (Point (M := M) 2 m)) where
  injection : PositionedCellLabelInjection G A
  comparison : GammaMixedStandardComparison G injection.target

theorem lemma_5_8 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    {m : ℕ} (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) :
    Nonempty (Corollary58Data G A) := by
  obtain ⟨T⟩ := exists_positioned_cell_label_injection hκ hs h00 G hsmall hGenerated δ hδ hδ1 A hA
  obtain ⟨C⟩ := T.full_standard_comparison hκ hs h00 hsmall δ hδ hδ1 F
  exact ⟨⟨T,C⟩⟩

end IntegrationInACVF.Section5
