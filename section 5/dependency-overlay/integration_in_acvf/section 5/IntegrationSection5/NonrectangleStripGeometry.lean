import IntegrationSection5.NonrectangleCellGeometry
import IntegrationSection5.CellStripNormalForms
import IntegrationSection5.PositionedCellLabelInjection
import IntegrationSection5.NativeCellProjections

/-! Horizontal and vertical RV-class closure for nonrectangle cells and uniform original-coordinate RV constancy over cell labels. -/
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

theorem nonrectangle_horizontal_closure (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (h : CellData R f t) (hRect : R ≠ first R ×ˢ second R)
    (p : VF (M := M) × VF (M := M)) (hp : p ∈ R)
    (c : VF (M := M)) (hc : c ∈ first R) (hfc : f c = p.2)
    (x : VF (M := M)) (hx : rv (x-c) = rv (p.1-c)) : (x,p.2) ∈ R := by
  rcases nonrectangle_cell_alternative δ hδ h hRect with ⟨r,hb⟩ | ⟨ht,hi⟩
  · have hStrip := balanced_cell_horizontal_strip hb
    have hInv : c = positionInverse hb.2.2.1.bijective p.2 := by
      apply hb.2.2.1.bijective.injOn hc
        (positionInverse_mem hb.2.2.1.bijective p.2 ⟨p,hp,rfl⟩)
      exact hfc.trans (positionInverse_right hb.2.2.1.bijective p.2 ⟨p,hp,rfl⟩).symm
    have hPoint := (Set.ext_iff.mp hStrip p).mp hp
    apply (Set.ext_iff.mp hStrip (x,p.2)).mpr
    refine ⟨hPoint.1,?_⟩
    change rv (x-positionInverse hb.2.2.1.bijective p.2) = r
    have hOld : rv (p.1-positionInverse hb.2.2.1.bijective p.2) = r := hPoint.2
    rw [← hInv] at hOld ⊢
    exact hx.trans hOld
  · have hGraph := graph_of_zero_paradigm h ht
    have hPoint := (Set.ext_iff.mp hGraph p).mp hp
    have hcp : c = p.1 := hi hc hPoint.1 (hfc.trans hPoint.2)
    have hx0 : rv (x-c) = rv (0 : VF (M := M)) := hx.trans (by rw [hcp,sub_self])
    have hxc : x = c := sub_eq_zero.mp ((rv_eq_zero_iff _).mp hx0)
    simpa only [hxc,hcp] using hp

theorem cell_vertical_closure (h : CellData R f t)
    (p : VF (M := M) × VF (M := M)) (hp : p ∈ R)
    (x : VF (M := M)) (hx : rv (x-f p.1) = rv (p.2-f p.1)) : (p.1,x) ∈ R := by
  have hFirst : p.1 ∈ first R := ⟨p,hp,rfl⟩
  have hOld := (Set.ext_iff.mp (h.fibres p.1 hFirst) p.2).mp hp
  exact (Set.ext_iff.mp (h.fibres p.1 hFirst) x).mpr (hx.trans hOld)

namespace PositionedCellLabelInjection
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

theorem same_labels_same_vf_rv (T : PositionedCellLabelInjection G A)
    (p q : Point (M := M) 2 T.arity) (hp : p ∈ T.target) (hq : q ∈ T.target) (hl : p.2 = q.2) :
    rv (vfAt p 0) = rv (vfAt q 0) ∧ rv (vfAt p 1) = rv (vfAt q 1) := by
  have hpR : (vfAt p 0,vfAt p 1) ∈ nativeTwoFibre T.target p.2 :=
    (nativePairPoint_eta p).symm ▸ hp
  have hqR : (vfAt q 0,vfAt q 1) ∈ nativeTwoFibre T.target p.2 := by
    change (![vfAt q 0,vfAt q 1],p.2) ∈ T.target
    rw [hl,nativePairPoint_eta]
    exact hq
  obtain ⟨f,t,h⟩ := T.forget.cells p.2 ⟨(vfAt p 0,vfAt p 1),hpR⟩
  obtain ⟨r,s,hrs⟩ := h.1.rv_polydisc
  exact ⟨((hrs _ hpR).1).trans ((hrs _ hqR).1).symm,
    ((hrs _ hpR).2).trans ((hrs _ hqR).2).symm⟩

end PositionedCellLabelInjection
end IntegrationInACVF.Section5
