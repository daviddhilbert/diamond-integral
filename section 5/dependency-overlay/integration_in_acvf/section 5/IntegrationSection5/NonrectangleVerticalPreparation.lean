import IntegrationSection5.NonrectangleHorizontalPreparation

/-! The actual opposite-order first preparation of the nonrectangle family, using the same global positioning bijection and retaining every original RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

def swappedNonrectangleFamily (T : PositionedCellLabelInjection G A) : Set (Point (M := M) 2 T.arity) :=
  {p | vfPermutation (Equiv.swap 0 1) p ∈ nonrectangleFamilyBranch T.target}

theorem swappedNonrectangleFamily_gamma (T : PositionedCellLabelInjection G A) :
    GammaSetDefinable G T.swappedNonrectangleFamily :=
  gamma_mixedVFSelect_preimage (Equiv.swap 0 1 : Fin 2 → Fin 2) _
    (nonrectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G)))

def swapped_nonrectangle_passive_mem (T : PositionedCellLabelInjection G A)
    (p : Point (M := M) 2 T.arity) (hp : p ∈ T.swappedNonrectangleFamily) :
    activeUnaryProjection 1 id p ∈ mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0 := by
  refine ⟨vfPermutation (Equiv.swap 0 1) p,hp,?_⟩
  apply Prod.ext
  · funext j
    fin_cases j
    simp only [activeUnaryProjection,vfPermutation,Function.comp_apply,vfAt,Equiv.swap_apply_left]
  · rfl

def verticalCentre (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)) :
    Point (M := M) 2 T.arity → VF (M := M) :=
  scalarZeroExtension T.swappedNonrectangleFamily (projectedIsoScalar e 1 T.swapped_nonrectangle_passive_mem)

theorem verticalCentre_graph (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)) :
    GammaScalarGraphDefinable G (fun p y => p ∈ T.swappedNonrectangleFamily ∧ y = T.verticalCentre e p) :=
  gamma_scalarZeroExtension _ (gamma_projectedIsoScalar T.swappedNonrectangleFamily_gamma e 1 T.swapped_nonrectangle_passive_mem)

theorem verticalCentre_independent (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (p : Point (M := M) 2 T.arity) (hp : p ∈ T.swappedNonrectangleFamily)
    (q : Point (M := M) 2 T.arity) (hq : q ∈ T.swappedNonrectangleFamily)
    (he : erase 0 p = erase 0 q) : T.verticalCentre e p = T.verticalCentre e q := by
  let g := projectedIsoScalar e 1 T.swapped_nonrectangle_passive_mem
  have hP := scalarZeroExtension_on g ⟨p,hp⟩
  have hQ := scalarZeroExtension_on g ⟨q,hq⟩
  exact hP.trans ((projectedIsoScalar_independent e T.swapped_nonrectangle_passive_mem ⟨p,hp⟩ ⟨q,hq⟩ he).trans hQ.symm)

theorem verticalCentre_cell_data (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (p : T.swappedNonrectangleFamily) :
    ∃ f : VF (M := M) → VF (M := M), ∃ t : RV (M := M),
      let R := nativeTwoFibre T.target p.val.2
      Cells.DefinableCellData (RVLabelSlices.labelBase G p.val.2) R f t ∧
      (vfAt p.val 1,vfAt p.val 0) ∈ R ∧
      T.verticalCentre e p.val = f (vfAt p.val 1) ∧ T.verticalCentre e p.val ∈ Cells.second R := by
  let q := vfPermutation (Equiv.swap (0 : Fin 2) 1) p.val
  have hq : q ∈ nonrectangleFamilyBranch T.target := p.property
  have hqR : (vfAt p.val 1,vfAt p.val 0) ∈ nativeTwoFibre T.target p.val.2 := by
    change (![vfAt p.val 1,vfAt p.val 0],p.val.2) ∈ T.target
    have he : (![vfAt p.val 1,vfAt p.val 0],p.val.2) = q := by
      apply Prod.ext
      · funext i; fin_cases i <;> simp [q,vfPermutation,vfAt]
      · rfl
    exact he.symm ▸ hq.1
  have hNe : (nativeTwoFibre (nonrectangleFamilyBranch T.target) p.val.2).Nonempty := by
    refine ⟨(vfAt p.val 1,vfAt p.val 0),?_⟩
    change (![vfAt p.val 1,vfAt p.val 0],p.val.2) ∈ nonrectangleFamilyBranch T.target
    have he : (![vfAt p.val 1,vfAt p.val 0],p.val.2) = q := by
      apply Prod.ext
      · funext i; fin_cases i <;> simp [q,vfPermutation,vfAt]
      · rfl
    exact he.symm ▸ hq
  obtain ⟨hEq,hNonrect⟩ := nonrectangleFamilyBranch_native_fibre T.target p.val.2 hNe
  obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ p.val.2 hNe
  let a : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0 :=
    ⟨activeUnaryProjection 1 id p.val,T.swapped_nonrectangle_passive_mem p.val p.property⟩
  have hC : T.verticalCentre e p.val = f (vfAt p.val 1) :=
    (scalarZeroExtension_on (projectedIsoScalar e 1 T.swapped_nonrectangle_passive_mem) p).trans
      ((hSpec a).trans (hAgree a rfl))
  have hFirst : vfAt p.val 1 ∈ Cells.first (nativeTwoFibre (nonrectangleFamilyBranch T.target) p.val.2) :=
    (mixed_first_projection_fibre_iff _ a.val).mp a.property
  have hSecond := hBij.mapsTo hFirst
  rw [hEq] at hSecond
  exact ⟨f,t,hDef,hqR,hC,hC.symm ▸ hSecond⟩

theorem nonrectangle_vertical_preparation (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p) :
    ∃ U : CanonicalTranslationPreparation (G := G) T.swappedNonrectangleFamily 0 (T.verticalCentre e),
      HeadSaturated (carrier U.target) := by
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
  exact mixed_strip_preparation _ T.swappedNonrectangleFamily_gamma (T.verticalCentre e)
    (T.verticalCentre_independent e) hRV (T.verticalCentre_graph e) hClosure hOldRV

end IntegrationInACVF.Section5.PositionedCellLabelInjection
