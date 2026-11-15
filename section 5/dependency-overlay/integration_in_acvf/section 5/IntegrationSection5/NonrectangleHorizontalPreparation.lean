import IntegrationSection5.NonrectanglePositionIso
import IntegrationSection5.NonrectangleStripGeometry
import IntegrationSection5.GammaProjectedScalar
import IntegrationSection5.MixedStripPreparation

/-! The actual first-coordinate preparation of the entire nonrectangle family. The globally selected inverse positioning map constructs the centre; cell geometry proves saturation with every old RV label retained. -/
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

def nonrectangle_second_mem (T : PositionedCellLabelInjection G A)
    (p : Point (M := M) 2 T.arity) (hp : p ∈ nonrectangleFamilyBranch T.target) :
    activeUnaryProjection 1 id p ∈ mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1 := ⟨p,hp,rfl⟩

def horizontalCentre (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)) :
    Point (M := M) 2 T.arity → VF (M := M) :=
  scalarZeroExtension (nonrectangleFamilyBranch T.target)
    (projectedIsoScalar (GammaIso.symm (gammaLogicInput G) e) 1 T.nonrectangle_second_mem)

theorem horizontalCentre_on (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (p : nonrectangleFamilyBranch T.target) :
    T.horizontalCentre e p.val =
      vfAt (e.equiv.symm ⟨activeUnaryProjection 1 id p.val,⟨p.val,p.property,rfl⟩⟩).val 0 :=
  scalarZeroExtension_on _ p

theorem horizontalCentre_graph (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)) :
    GammaScalarGraphDefinable G (fun p y => p ∈ nonrectangleFamilyBranch T.target ∧ y = T.horizontalCentre e p) := by
  have hN := nonrectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G))
  exact gamma_scalarZeroExtension _ (gamma_projectedIsoScalar hN
    (GammaIso.symm (gammaLogicInput G) e) 1 T.nonrectangle_second_mem)

theorem horizontalCentre_independent (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (p : Point (M := M) 2 T.arity) (hp : p ∈ nonrectangleFamilyBranch T.target)
    (q : Point (M := M) 2 T.arity) (hq : q ∈ nonrectangleFamilyBranch T.target)
    (he : erase 0 p = erase 0 q) : T.horizontalCentre e p = T.horizontalCentre e q := by
  let g := projectedIsoScalar (GammaIso.symm (gammaLogicInput G) e) 1 T.nonrectangle_second_mem
  have hP := scalarZeroExtension_on g ⟨p,hp⟩
  have hQ := scalarZeroExtension_on g ⟨q,hq⟩
  exact hP.trans ((projectedIsoScalar_independent (GammaIso.symm (gammaLogicInput G) e)
    T.nonrectangle_second_mem ⟨p,hp⟩ ⟨q,hq⟩ he).trans hQ.symm)

theorem horizontalCentre_cell_data (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hLabels : ∀ p, (e.equiv p).val.2 = p.val.2)
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (p : nonrectangleFamilyBranch T.target) :
    ∃ f : VF (M := M) → VF (M := M), ∃ t : RV (M := M),
      let R := nativeTwoFibre T.target p.val.2
      Cells.DefinableCellData (RVLabelSlices.labelBase G p.val.2) R f t ∧
      R ≠ Cells.first R ×ˢ Cells.second R ∧
      (vfAt p.val 0,vfAt p.val 1) ∈ R ∧
      T.horizontalCentre e p.val ∈ Cells.first R ∧ f (T.horizontalCentre e p.val) = vfAt p.val 1 := by
  let N := nonrectangleFamilyBranch T.target
  have hNe : (nativeTwoFibre N p.val.2).Nonempty := by
    refine ⟨(vfAt p.val 0,vfAt p.val 1),?_⟩
    change (![vfAt p.val 0,vfAt p.val 1],p.val.2) ∈ N
    rw [nativePairPoint_eta]
    exact p.property
  obtain ⟨hEq,hNonrect⟩ := nonrectangleFamilyBranch_native_fibre T.target p.val.2 hNe
  obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ p.val.2 hNe
  let b : mixedUnaryProjectionSet N 1 := ⟨activeUnaryProjection 1 id p.val,⟨p.val,p.property,rfl⟩⟩
  let c := e.equiv.symm b
  have hcb : e.equiv c = b := e.equiv.apply_symm_apply b
  have hLc : c.val.2 = p.val.2 := by
    have h := hLabels c
    rw [hcb] at h
    exact h.symm
  have hcFirst := (mixed_first_projection_fibre_iff N c.val).mp c.property
  rw [hLc,hEq] at hcFirst
  have hfc : f (vfAt c.val 0) = vfAt p.val 1 := by
    calc
      f (vfAt c.val 0) = T.nonrectanglePosition c := (hAgree c hLc).symm
      _ = vfAt (e.equiv c).val 0 := (hSpec c).symm
      _ = vfAt p.val 1 := by rw [hcb]; rfl
  have hcValue : T.horizontalCentre e p.val = vfAt c.val 0 := T.horizontalCentre_on e p
  refine ⟨f,t,hDef,hNonrect,?_,?_,?_⟩
  · change (![vfAt p.val 0,vfAt p.val 1],p.val.2) ∈ T.target
    rw [nativePairPoint_eta]
    exact p.property.1
  · rw [hcValue]
    exact hcFirst
  · rw [hcValue]
    exact hfc

theorem nonrectangle_horizontal_preparation (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
        (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1),
      (∀ p, (e.equiv p).val.2 = p.val.2) ∧
      (∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p) ∧
      ∃ U : CanonicalTranslationPreparation (G := G) (nonrectangleFamilyBranch T.target) 0 (T.horizontalCentre e),
        HeadSaturated (carrier U.target) := by
  obtain ⟨e,hLabels,hSpec⟩ := T.nonrectangle_position_gamma_iso δ hδ
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
  obtain ⟨U,hU⟩ := mixed_strip_preparation _ hN (T.horizontalCentre e) (T.horizontalCentre_independent e)
    hRV (T.horizontalCentre_graph e) hClosure
    (fun p hp q hq hl => (T.same_labels_same_vf_rv p q hp.1 hq.1 hl).1)
  exact ⟨e,hLabels,hSpec,U,hU⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
