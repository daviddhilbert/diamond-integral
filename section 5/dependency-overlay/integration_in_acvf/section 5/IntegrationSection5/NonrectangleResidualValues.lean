import IntegrationSection5.NonrectangleHorizontalPreparation

/-! The horizontal transverse RV class is uniform over each existing cell code, even though its value varies between cells. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}

theorem nonrectangle_horizontal_residual_eq (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (h : CellData R f t) (hRect : R ≠ first R ×ˢ second R)
    (p q : VF (M := M) × VF (M := M)) (hp : p ∈ R) (hq : q ∈ R)
    (c d : VF (M := M)) (hc : c ∈ first R) (hd : d ∈ first R)
    (hfc : f c = p.2) (hfd : f d = q.2) : rv (p.1-c) = rv (q.1-d) := by
  rcases nonrectangle_cell_alternative δ hδ h hRect with ⟨r,hb⟩ | ⟨ht,hi⟩
  · have hStrip := balanced_cell_horizontal_strip hb
    have hcInv : c = positionInverse hb.2.2.1.bijective p.2 := by
      apply hb.2.2.1.bijective.injOn hc (positionInverse_mem hb.2.2.1.bijective p.2 ⟨p,hp,rfl⟩)
      exact hfc.trans (positionInverse_right hb.2.2.1.bijective p.2 ⟨p,hp,rfl⟩).symm
    have hdInv : d = positionInverse hb.2.2.1.bijective q.2 := by
      apply hb.2.2.1.bijective.injOn hd (positionInverse_mem hb.2.2.1.bijective q.2 ⟨q,hq,rfl⟩)
      exact hfd.trans (positionInverse_right hb.2.2.1.bijective q.2 ⟨q,hq,rfl⟩).symm
    have hpv : rv (p.1-positionInverse hb.2.2.1.bijective p.2) = r := ((Set.ext_iff.mp hStrip p).mp hp).2
    have hqv : rv (q.1-positionInverse hb.2.2.1.bijective q.2) = r := ((Set.ext_iff.mp hStrip q).mp hq).2
    rw [← hcInv] at hpv
    rw [← hdInv] at hqv
    exact hpv.trans hqv.symm
  · have hpG := (Set.ext_iff.mp (graph_of_zero_paradigm h ht) p).mp hp
    have hqG := (Set.ext_iff.mp (graph_of_zero_paradigm h ht) q).mp hq
    have hcp : c = p.1 := hi hc hpG.1 (hfc.trans hpG.2)
    have hdq : d = q.1 := hi hd hqG.1 (hfd.trans hqG.2)
    rw [hcp,hdq,sub_self,sub_self]

namespace PositionedCellLabelInjection
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

theorem horizontalCentre_uniform_cell_data (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hLabels : ∀ p, (e.equiv p).val.2 = p.val.2)
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (s : Fin T.arity → RV (M := M)) (hs : (nativeTwoFibre (nonrectangleFamilyBranch T.target) s).Nonempty) :
    ∃ f : VF (M := M) → VF (M := M), ∃ t : RV (M := M),
      let R := nativeTwoFibre T.target s
      Cells.DefinableCellData (RVLabelSlices.labelBase G s) R f t ∧ R ≠ first R ×ˢ second R ∧
      ∀ p : nonrectangleFamilyBranch T.target, p.val.2 = s →
        (vfAt p.val 0,vfAt p.val 1) ∈ R ∧ T.horizontalCentre e p.val ∈ first R ∧
          f (T.horizontalCentre e p.val) = vfAt p.val 1 := by
  let N := nonrectangleFamilyBranch T.target
  obtain ⟨hEq,hNonrect⟩ := nonrectangleFamilyBranch_native_fibre T.target s hs
  obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ s hs
  refine ⟨f,t,hDef,hNonrect,?_⟩
  intro p hps
  let b : mixedUnaryProjectionSet N 1 := ⟨activeUnaryProjection 1 id p.val,⟨p.val,p.property,rfl⟩⟩
  let c := e.equiv.symm b
  have hcb : e.equiv c = b := e.equiv.apply_symm_apply b
  have hLc : c.val.2 = s := by
    have h := hLabels c
    rw [hcb] at h
    exact h.symm.trans hps
  have hcFirst := (mixed_first_projection_fibre_iff N c.val).mp c.property
  rw [hLc,hEq] at hcFirst
  have hfc : f (vfAt c.val 0) = vfAt p.val 1 := by
    calc
      f (vfAt c.val 0) = T.nonrectanglePosition c := (hAgree c hLc).symm
      _ = vfAt (e.equiv c).val 0 := (hSpec c).symm
      _ = vfAt p.val 1 := by rw [hcb]; rfl
  have hcValue : T.horizontalCentre e p.val = vfAt c.val 0 := T.horizontalCentre_on e p
  refine ⟨?_,?_,?_⟩
  · change (![vfAt p.val 0,vfAt p.val 1],s) ∈ T.target
    rw [← hps,nativePairPoint_eta]
    exact p.property.1
  · rw [hcValue]
    exact hcFirst
  · rw [hcValue]
    exact hfc

theorem horizontalCentre_residual_same_labels (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hLabels : ∀ p, (e.equiv p).val.2 = p.val.2)
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (p q : Point (M := M) 2 T.arity) (hp : p ∈ nonrectangleFamilyBranch T.target)
    (hq : q ∈ nonrectangleFamilyBranch T.target) (hl : p.2 = q.2) :
    rv (vfAt p 0-T.horizontalCentre e p) = rv (vfAt q 0-T.horizontalCentre e q) := by
  have hNe : (nativeTwoFibre (nonrectangleFamilyBranch T.target) p.2).Nonempty := by
    refine ⟨(vfAt p 0,vfAt p 1),?_⟩
    change (![vfAt p 0,vfAt p 1],p.2) ∈ nonrectangleFamilyBranch T.target
    rwa [nativePairPoint_eta]
  obtain ⟨f,t,hDef,hNonrect,hData⟩ := T.horizontalCentre_uniform_cell_data δ hδ e hLabels hSpec p.2 hNe
  have hpD := hData ⟨p,hp⟩ rfl
  have hqD := hData ⟨q,hq⟩ hl.symm
  exact nonrectangle_horizontal_residual_eq δ hδ hDef.1 hNonrect
    (vfAt p 0,vfAt p 1) (vfAt q 0,vfAt q 1) hpD.1 hqD.1
    (T.horizontalCentre e p) (T.horizontalCentre e q) hpD.2.1 hqD.2.1 hpD.2.2 hqD.2.2

end PositionedCellLabelInjection
end IntegrationInACVF.Section5
