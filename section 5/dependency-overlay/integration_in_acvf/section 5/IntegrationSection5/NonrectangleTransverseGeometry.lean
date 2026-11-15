import IntegrationSection5.NonrectangleResidualValues
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

theorem nonrectangle_transverse_forward (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (h : CellData R f t) (hRect : R ≠ first R ×ˢ second R)
    (p : VF (M := M) × VF (M := M)) (hp : p ∈ R)
    (c : VF (M := M)) (hc : c ∈ first R) (hfc : f c = p.2)
    (u : VF (M := M)) (hu : rv u = rv (p.1-c)) :
    c-u ∈ first R ∧ (c,f (c-u)) ∈ R := by
  rcases nonrectangle_cell_alternative δ hδ h hRect with ⟨r,hb⟩ | ⟨ht,hi⟩
  · have hcInv : c = positionInverse hb.2.2.1.bijective p.2 := by
      apply hb.2.2.1.bijective.injOn hc (positionInverse_mem hb.2.2.1.bijective p.2 ⟨p,hp,rfl⟩)
      exact hfc.trans (positionInverse_right hb.2.2.1.bijective p.2 ⟨p,hp,rfl⟩).symm
    have hr : rv (p.1-c) = r := by
      rw [hcInv]
      exact ((Set.ext_iff.mp (balanced_cell_horizontal_strip hb) p).mp hp).2
    have hx : rv (c-(c-u)) = r := by rw [sub_sub_cancel,hu,hr]
    have hm := (Set.ext_iff.mp (hb.2.2.1.horizontal c hc) (c-u)).mpr hx
    exact hm
  · have hpG := (Set.ext_iff.mp (graph_of_zero_paradigm h ht) p).mp hp
    have hcp : c = p.1 := hi hc hpG.1 (hfc.trans hpG.2)
    have hu0 : u = 0 := (rv_eq_zero_iff _).mp (hu.trans (by rw [hcp,sub_self]))
    rw [hu0,sub_zero]
    exact ⟨hc,(Set.ext_iff.mp (graph_of_zero_paradigm h ht) (c,f c)).mpr ⟨hc,rfl⟩⟩

end IntegrationInACVF.Section5
