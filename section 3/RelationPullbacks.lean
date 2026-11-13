import Section4.MapCorestrict
import Section4.Products

/-! Pulling a full definable relation back along two actual definable
maps preserves its complete graph over the original parameter set. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M}
variable {P Q R T : Space L M} {rel : Q.Carrier → R.Carrier → Prop}

theorem relationDefinable_pullback (h : Q.RelationDefinable R S rel)
    (f : Map (DefSet.univ P S) (DefSet.univ Q S))
    (g : Map (DefSet.univ T S) (DefSet.univ R S)) :
    P.RelationDefinable T S (fun x y => rel (f ⟨x, Set.mem_univ _⟩).val (g ⟨y, Set.mem_univ _⟩).val) := by
  have hd := (f.graph_definable.comp P Q R h).comp P R T (g.graph_definable.swap T R)
  exact hd.congr P T (by
    intro x y
    constructor
    · rintro ⟨r, ⟨q, ⟨a, ha, hq⟩, hr⟩, ⟨b, hb, hgr⟩⟩
      have ha' : a = ⟨x, Set.mem_univ _⟩ := Subtype.ext ha
      have hb' : b = ⟨y, Set.mem_univ _⟩ := Subtype.ext hb
      subst a
      subst b
      exact hq.symm ▸ hgr.symm ▸ hr
    · intro hr
      exact ⟨(g ⟨y, Set.mem_univ _⟩).val,
        ⟨(f ⟨x, Set.mem_univ _⟩).val, ⟨⟨x, Set.mem_univ _⟩, rfl, rfl⟩, hr⟩,
        ⟨y, Set.mem_univ _⟩, rfl, rfl⟩)

end DiamondIntegral.Section3
