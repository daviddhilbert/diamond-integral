import IntegrationSection5.RVSliceTranslation
import IntegrationSection5.NonrectangleHorizontalPreparation
import IntegrationSection5.NonrectangleVerticalPreparation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

def nonrectangleRVLabels (T : PositionedCellLabelInjection G A) : Set (Fin T.arity → RV (M := M)) :=
  {s | (Fin.elim0,s) ∈ rectangleFailureCodes T.target}

theorem rvSlice_target_nonrectangle (T : PositionedCellLabelInjection G A) :
    rvSliceSet T.target T.nonrectangleRVLabels = nonrectangleFamilyBranch T.target := rfl

def swappedTarget (T : PositionedCellLabelInjection G A) : Set (Point (M := M) 2 T.arity) :=
  {p | vfPermutation (Equiv.swap 0 1) p ∈ T.target}

theorem swappedTarget_gamma (T : PositionedCellLabelInjection G A) : GammaSetDefinable G T.swappedTarget :=
  gamma_mixedVFSelect_preimage (Equiv.swap 0 1) T.target (T.iso.target_definable (gammaLogicInput G))

theorem rvSlice_swapped_nonrectangle (T : PositionedCellLabelInjection G A) :
    rvSliceSet T.swappedTarget T.nonrectangleRVLabels = T.swappedNonrectangleFamily := rfl

theorem global_nonrectangle_horizontal_preparation (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hLabels : ∀ p, (e.equiv p).val.2 = p.val.2)
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p) :
    ∃ U : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 (T.horizontalCentre e),
      HeadSaturated (carrier U.branch.target) := by
  have hN := nonrectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G))
  have hRV : ∀ p ∈ nonrectangleFamilyBranch T.target,
      rv (T.horizontalCentre e p) = rv (vfAt p 0) := by
    intro p hp
    obtain ⟨f,t,hDef,hRect,hpR,hc,hfc⟩ := T.horizontalCentre_cell_data δ hδ e hLabels hSpec ⟨p,hp⟩
    exact cell_first_rv_eq hDef.1 hc ⟨(vfAt p 0,vfAt p 1),hpR,rfl⟩
  have hClosure : ∀ p ∈ nonrectangleFamilyBranch T.target, ∀ x,
      rv (x-T.horizontalCentre e p) = rv (vfAt p 0-T.horizontalCentre e p) → replace 0 p x ∈ nonrectangleFamilyBranch T.target := by
    intro p hp x hx
    obtain ⟨f,t,hDef,hRect,hpR,hc,hfc⟩ := T.horizontalCentre_cell_data δ hδ e hLabels hSpec ⟨p,hp⟩
    have hNew := nonrectangle_horizontal_closure δ hδ hDef.1 hRect (vfAt p 0,vfAt p 1) hpR
      (T.horizontalCentre e p) hc hfc x hx
    have he : replace 0 p x = (![x,vfAt p 1],p.2) := by
      apply Prod.ext
      · funext j; fin_cases j <;> simp [replace,vfAt]
      · rfl
    exact ⟨he.symm ▸ hNew,hp.2⟩
  obtain ⟨U⟩ := rvSlice_translation_preparation T.target (T.iso.target_definable (gammaLogicInput G))
    T.nonrectangleRVLabels hN 0 (T.horizontalCentre e) (T.horizontalCentre_independent e)
    hRV (T.horizontalCentre_graph e)
  refine ⟨U,?_⟩
  exact mixed_translation_headSaturated _ _ (T.horizontalCentre_independent e) hClosure
    (fun p hp q hq hl => (T.same_labels_same_vf_rv p q hp.1 hq.1 hl).1) U.branch

theorem global_nonrectangle_vertical_preparation (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p) :
    ∃ U : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 (T.verticalCentre e),
      HeadSaturated (carrier U.branch.target) := by
  have hRV : ∀ p ∈ T.swappedNonrectangleFamily, rv (T.verticalCentre e p) = rv (vfAt p 0) := by
    intro p hp
    obtain ⟨f,t,hDef,hpR,hC,hSecond⟩ := T.verticalCentre_cell_data δ hδ e hSpec ⟨p,hp⟩
    exact cell_second_rv_eq hDef.1 hSecond ⟨(vfAt p 1,vfAt p 0),hpR,rfl⟩
  have hClosure : ∀ p ∈ T.swappedNonrectangleFamily, ∀ x,
      rv (x-T.verticalCentre e p) = rv (vfAt p 0-T.verticalCentre e p) → replace 0 p x ∈ T.swappedNonrectangleFamily := by
    intro p hp x hx
    obtain ⟨f,t,hDef,hpR,hC,hSecond⟩ := T.verticalCentre_cell_data δ hδ e hSpec ⟨p,hp⟩
    rw [hC] at hx
    have hNew := cell_vertical_closure hDef.1 (vfAt p 1,vfAt p 0) hpR x hx
    have he : vfPermutation (Equiv.swap (0 : Fin 2) 1) (replace 0 p x) = (![vfAt p 1,x],p.2) := by
      apply Prod.ext
      · funext j; fin_cases j <;> simp [vfPermutation,replace,vfAt]
      · rfl
    exact ⟨he.symm ▸ hNew,hp.2⟩
  have hOldRV : ∀ p ∈ T.swappedNonrectangleFamily, ∀ q ∈ T.swappedNonrectangleFamily,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq hl
    have h := (T.same_labels_same_vf_rv (vfPermutation (Equiv.swap 0 1) p)
      (vfPermutation (Equiv.swap 0 1) q) hp.1 hq.1 hl).2
    simpa only [vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_right] using h
  obtain ⟨U⟩ := rvSlice_translation_preparation T.swappedTarget T.swappedTarget_gamma
    T.nonrectangleRVLabels T.swappedNonrectangleFamily_gamma 0 (T.verticalCentre e)
    (T.verticalCentre_independent e) hRV (T.verticalCentre_graph e)
  exact ⟨U,mixed_translation_headSaturated _ _ (T.verticalCentre_independent e) hClosure hOldRV U.branch⟩

theorem global_nonrectangle_head_preparations (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1),
      (∀ p, (e.equiv p).val.2 = p.val.2) ∧
      (∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p) ∧
      ∃ L : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 (T.horizontalCentre e),
        HeadSaturated (carrier L.branch.target) ∧
        ∃ R : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 (T.verticalCentre e),
          HeadSaturated (carrier R.branch.target) := by
  obtain ⟨e,hLabels,hSpec⟩ := T.nonrectangle_position_gamma_iso δ hδ
  obtain ⟨L,hL⟩ := T.global_nonrectangle_horizontal_preparation δ hδ e hLabels hSpec
  obtain ⟨R,hR⟩ := T.global_nonrectangle_vertical_preparation δ hδ e hSpec
  exact ⟨e,hLabels,hSpec,L,hL,R,hR⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
