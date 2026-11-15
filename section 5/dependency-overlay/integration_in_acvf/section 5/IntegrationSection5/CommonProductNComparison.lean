import IntegrationSection5.CommonProductNonrectangleProfiles
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

structure CommonProductNComparison (T : PositionedCellLabelInjection G A) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) where
  matching : CommonProductMatching T δ hδ
  left : PaddedUnaryBranchExtension (G := G) matching.unary.specialA matching.leftAmbient matching.leftProjection
    (CommonProductMatching.oldNLabels (T := T)) none
  right : PaddedUnaryBranchExtension (G := G) matching.unary.specialB matching.rightAmbient matching.rightProjection
    (CommonProductMatching.oldNLabels (T := T)) none
  comparison : GammaRVIso G
    (selectedVolumeObject (Map.image (rawKeyMap left.lift.active_image))
      ![Fin.natAdd 1 (suffixIndex left.lift.arity_le ((Fin.natAdd 1 ∘ matching.leftProjection) 0)),0])
    (selectedVolumeObject (Map.image (rawKeyMap right.lift.active_image))
      ![Fin.natAdd 1 (suffixIndex right.lift.arity_le ((Fin.natAdd 1 ∘ matching.rightProjection) 0)),0])

theorem common_product_n_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) : Nonempty (CommonProductNComparison T δ hδ1) := by
  obtain ⟨Q⟩ := T.common_product_matching hκ hs h00 hsmall δ hδ hδ1 F
  obtain ⟨L⟩ := Q.left_padded_tail
  obtain ⟨R⟩ := Q.right_padded_tail
  exact ⟨⟨Q,L,R,Q.padded_nonrectangle_profile_comparison hκ hs hsmall L R⟩⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
