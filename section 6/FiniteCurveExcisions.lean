import Mathlib.Data.Set.Card

/-! A bijection between two cofinite cores with finitely many isolated
points restricts to a bijection of the cores after finite excisions.
The excised points and isolated points have an actual finite bijection,
which gives their cardinal balance. No definability input is used here. -/

noncomputable section
open Set Classical

namespace DiamondIntegral.Section6

theorem finite_curve_excisions {X Y : Type*} (P : Set X) (Q : Set Y)
    (F E : Finset X) (G D : Finset Y)
    (hE : Disjoint P (E : Set X)) (hD : Disjoint Q (D : Set Y))
    (f : X → Y) (hf : Set.BijOn f ((P \ F) ∪ E) ((Q \ G) ∪ D)) :
    ∃ C : Finset X, ∃ L : Finset Y,
      (C : Set X) ⊆ P \ F ∧ (L : Set Y) ⊆ Q \ G ∧
      Set.BijOn f (P \ (F ∪ C : Finset X)) (Q \ (G ∪ L : Finset Y)) ∧
      E.card + C.card = D.card + L.card := by
  let C : Set X := {x | x ∈ P \ F ∧ f x ∈ D}
  let L : Set Y := (f '' (E : Set X)) ∩ (Q \ G)
  have hCF : C.Finite := Set.Finite.of_injOn
    (fun x hx => hx.2) (fun x hx y hy he => hf.2.1 (Or.inl hx.1) (Or.inl hy.1) he) D.finite_toSet
  have hLF : L.Finite := (E.finite_toSet.image f).subset Set.inter_subset_left
  have hCSub : C ⊆ P \ F := fun _ hx => hx.1
  have hLSub : L ⊆ Q \ G := Set.inter_subset_right
  have hEC : Disjoint (E : Set X) C := Set.disjoint_left.mpr (fun x hxE hxC =>
    Set.disjoint_left.mp hE hxC.1.1 hxE)
  have hDL : Disjoint (D : Set Y) L := Set.disjoint_left.mpr (fun y hyD hyL =>
    Set.disjoint_left.mp hD hyL.2.1 hyD)
  have hCore : Set.BijOn f (P \ ((F : Set X) ∪ C)) (Q \ ((G : Set Y) ∪ L)) := by
    refine ⟨?_,?_,?_⟩
    · intro x hx
      have hxP : x ∈ P \ F := ⟨hx.1,fun h => hx.2 (Or.inl h)⟩
      have hxC : x ∉ C := fun h => hx.2 (Or.inr h)
      have hfy : f x ∈ Q \ G := by
        rcases hf.1 (Or.inl hxP) with h | h
        · exact h
        · exact False.elim (hxC ⟨hxP,h⟩)
      refine ⟨hfy.1,fun h => ?_⟩
      rcases h with h | h
      · exact hfy.2 h
      · obtain ⟨e,heE,he⟩ := h.1
        have hex : e = x := hf.2.1 (Or.inr heE) (Or.inl hxP) he
        exact Set.disjoint_left.mp hE hx.1 (hex ▸ heE)
    · intro x hx y hy he
      exact hf.2.1 (Or.inl ⟨hx.1,fun h => hx.2 (Or.inl h)⟩)
        (Or.inl ⟨hy.1,fun h => hy.2 (Or.inl h)⟩) he
    · intro y hy
      have hyQ : y ∈ Q \ G := ⟨hy.1,fun h => hy.2 (Or.inl h)⟩
      obtain ⟨x,hx,hfx⟩ := hf.2.2 (Or.inl hyQ)
      have hxP : x ∈ P \ F := by
        rcases hx with h | h
        · exact h
        · exact False.elim (hy.2 (Or.inr ⟨⟨x,h,hfx⟩,hyQ⟩))
      refine ⟨x,⟨hxP.1,?_⟩,hfx⟩
      rintro (hF | hC)
      · exact hxP.2 hF
      · exact Set.disjoint_left.mp hD hy.1 (hfx ▸ hC.2)
  have hPatch : Set.BijOn f ((E : Set X) ∪ C) ((D : Set Y) ∪ L) := by
    refine ⟨?_,?_,?_⟩
    · intro x hx
      rcases hx with h | h
      · rcases hf.1 (Or.inr h) with hy | hy
        · exact Or.inr ⟨⟨x,h,rfl⟩,hy⟩
        · exact Or.inl hy
      · exact Or.inl h.2
    · intro x hx y hy he
      exact hf.2.1 (hx.elim Or.inr (fun h => Or.inl h.1))
        (hy.elim Or.inr (fun h => Or.inl h.1)) he
    · intro y hy
      rcases hy with h | h
      · obtain ⟨x,hx,hfx⟩ := hf.2.2 (Or.inr h)
        refine ⟨x,?_,hfx⟩
        rcases hx with hx | hx
        · exact Or.inr ⟨hx,hfx.symm ▸ h⟩
        · exact Or.inl hx
      · obtain ⟨x,hx,hfx⟩ := h.1
        exact ⟨x,Or.inl hx,hfx⟩
  refine ⟨hCF.toFinset,hLF.toFinset,?_,?_,?_,?_⟩
  · simpa only [Set.Finite.coe_toFinset] using hCSub
  · simpa only [Set.Finite.coe_toFinset] using hLSub
  · simpa only [Finset.coe_union,Set.Finite.coe_toFinset] using hCore
  · have hCard := hPatch.ncard_eq
    rw [Set.ncard_union_eq hEC E.finite_toSet hCF,
      Set.ncard_union_eq hDL D.finite_toSet hLF,Set.ncard_coe_finset,Set.ncard_coe_finset,
      Set.ncard_eq_toFinset_card C hCF,Set.ncard_eq_toFinset_card L hLF] at hCard
    exact hCard

end DiamondIntegral.Section6
