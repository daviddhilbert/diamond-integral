import «section 6».GammaTransitionImages

/-! Full representative graphs determine actual values even when two
maps use different literal source and target subsets of the same spaces.
No choice of a distinguished quotient representative is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] {S : Set M}
variable {P Q : Space LRV M} {A A' : DefSet P S} {B B' : DefSet Q S}

theorem map_values_eq_of_code_graph_eq (f : Map A B) (g : Map A' B')
    (hGraph : P.relation Q f.graph=P.relation Q g.graph)
    (p : A) (q : A') (hPoint : p.val=q.val) : (f p).val=(g q).val := by
  obtain ⟨x,hx⟩ := P.onto p.val
  obtain ⟨y,hy⟩ := Q.onto (f p).val
  have hMem := (P.relation_decode Q f.graph x y).mpr ⟨p,hx.symm,hy.symm⟩
  rw [hGraph] at hMem
  obtain ⟨a,ha,hga⟩ := (P.relation_decode Q g.graph x y).mp hMem
  have haq : a=q := Subtype.ext (ha.trans (hx.trans hPoint))
  rw [haq] at hga
  exact (hga.trans hy).symm

theorem map_eq_of_code_graph_eq (f g : Map A B)
    (hGraph : P.relation Q f.graph=P.relation Q g.graph) : f=g := by
  apply Map.ext
  intro p
  exact Subtype.ext (map_values_eq_of_code_graph_eq f g hGraph p p rfl)

end DiamondIntegral.Section6
