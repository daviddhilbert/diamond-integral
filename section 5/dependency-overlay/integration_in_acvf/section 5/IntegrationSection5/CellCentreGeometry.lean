import IntegrationSection5.PositionInverseGraph

/-! Positioning values and inverse positioning values lie in the correct
actual RV classes for the cell translation foci. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section4.BalancedFibres
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

theorem cell_first_rv_eq (h : CellData R f t) {a b : VF (M := M)}
    (ha : a ∈ first R) (hb : b ∈ first R) : rv a = rv b := by
  obtain ⟨u,v,huv⟩ := h.rv_polydisc
  obtain ⟨p,hp,hpa⟩ := ha
  obtain ⟨q,hq,hqb⟩ := hb
  exact (congrArg rv hpa).symm.trans (((huv p hp).1).trans (((huv q hq).1).symm.trans (congrArg rv hqb)))

theorem cell_second_rv_eq (h : CellData R f t) {a b : VF (M := M)}
    (ha : a ∈ second R) (hb : b ∈ second R) : rv a = rv b := by
  obtain ⟨u,v,huv⟩ := h.rv_polydisc
  obtain ⟨p,hp,hpa⟩ := ha
  obtain ⟨q,hq,hqb⟩ := hb
  exact (congrArg rv hpa).symm.trans (((huv p hp).2).trans (((huv q hq).2).symm.trans (congrArg rv hqb)))

theorem balanced_vertical_centre_rv (h : CellData R f t) (hb : IsBalanced R f r t)
    (p : VF (M := M) × VF (M := M)) (hp : p ∈ R) : rv (f p.1) = rv p.2 :=
  cell_second_rv_eq h (hb.2.2.1.bijective.mapsTo ⟨p,hp,rfl⟩) ⟨p,hp,rfl⟩

theorem balanced_horizontal_centre_rv (h : CellData R f t) (hb : IsBalanced R f r t)
    (p : VF (M := M) × VF (M := M)) (hp : p ∈ R) :
    rv (positionInverse hb.2.2.1.bijective p.2) = rv p.1 :=
  cell_first_rv_eq h (positionInverse_mem hb.2.2.1.bijective p.2 ⟨p,hp,rfl⟩) ⟨p,hp,rfl⟩

theorem zero_paradigm_position_bijective (h : CellData R f t) (ht : t = rv (0 : VF (M := M)))
    (hi : Set.InjOn f (first R)) : Set.BijOn f (first R) (second R) := by
  have hGraph := graph_of_zero_paradigm h ht
  refine ⟨?_,hi,?_⟩
  · intro a ha
    exact ⟨(a,f a),hGraph.symm ▸ ⟨ha,rfl⟩,rfl⟩
  · rintro b ⟨p,hp,hpb⟩
    have hg := hGraph ▸ hp
    exact ⟨p.1,hg.1,hg.2.symm.trans hpb⟩

end IntegrationInACVF.Section5
