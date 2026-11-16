import «section 6».GammaTransitionParameterLoci

/-! The full-code terminal test means precisely constancy of the
transported actual Gamma map on equal output RV labels. The proof does
not replace quotient codes by selected representatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

theorem gammaTransitionJointGraph_entries
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (x : GammaTransitionEntry (M := M) n r s → M) :
    Sum.elim a x ∈ gammaTransitionJointGraph R W ↔
      ∃ t : A,∃ c : (rawGammaPresentation (M := M)).domain,
        (rawGammaPresentation (M := M)).decode c=(ω t).val ∧
        x=Sum.elim (mixedValues t.val) (Sum.elim (mixedValues (f t).val) c.val) := by
  constructor
  · rintro ⟨hRx,hWx⟩
    obtain ⟨hx,hy,t,ht,hft⟩ := (Set.ext_iff.mp hR _).mp hRx
    obtain ⟨hx',hc,q,hq,hωq⟩ := (Set.ext_iff.mp hW _).mp hWx
    have htq : t=q := Subtype.ext (ht.trans hq.symm)
    subst q
    let c : (rawGammaPresentation (M := M)).domain := ⟨fun i => x (.inr (.inr i)),hc⟩
    refine ⟨t,c,hωq.symm,?_⟩
    have hInput : mixedValues t.val=x ∘ Sum.inl := by
      rw [ht]
      exact mixedValues_decode _
    have hOutput : mixedValues (f t).val=(fun i => x (.inr (.inl i))) := by
      rw [hft]
      exact mixedValues_decode _
    funext i
    rcases i with i | (i | i)
    · exact (congrFun hInput i).symm
    · exact (congrFun hOutput i).symm
    · rfl
  · rintro ⟨t,c,hc,rfl⟩
    constructor
    · apply (Set.ext_iff.mp hR _).mpr
      apply ((rawMixedSpace (M := M) n r).relation_decode (rawMixedSpace n s) f.graph
        ⟨mixedValues t.val,mixedValues_mem_domain _⟩ ⟨mixedValues (f t).val,mixedValues_mem_domain _⟩).mpr
      simpa only [decode_mixedValues] using (show f.graph t.val (f t).val from ⟨t,rfl,rfl⟩)
    · apply (Set.ext_iff.mp hW _).mpr
      apply ((rawMixedSpace (M := M) n r).relation_decode rawGammaPresentation ω.graph
        ⟨mixedValues t.val,mixedValues_mem_domain _⟩ c).mpr
      simpa only [decode_mixedValues] using
        (show ω.graph t.val ((rawGammaPresentation (M := M)).decode c) from ⟨t,rfl,hc.symm⟩)

theorem gammaTransitionConstantParameterLocus_iff
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph) :
    a ∈ gammaTransitionConstantParameterLocus R W ↔
      ∀ t u : A,(f t).val.2=(f u).val.2 → (ω t).val=(ω u).val := by
  constructor
  · intro h t u htu
    obtain ⟨c,hc⟩ := (rawGammaPresentation (M := M)).onto (ω t).val
    obtain ⟨d,hd⟩ := (rawGammaPresentation (M := M)).onto (ω u).val
    let x := Sum.elim (mixedValues t.val) (Sum.elim (mixedValues (f t).val) c.val)
    let y := Sum.elim (mixedValues u.val) (Sum.elim (mixedValues (f u).val) d.val)
    have hx := (gammaTransitionJointGraph_entries a R W f ω hR hW x).mpr ⟨t,c,hc,rfl⟩
    have hy := (gammaTransitionJointGraph_entries a R W f ω hR hW y).mpr ⟨u,d,hd,rfl⟩
    have hCond := h x y hx hy
    have hTags : ∀ j : Fin s,(mixedValues (f t).val) (.inr j)=(mixedValues (f u).val) (.inr j) := by
      intro j
      exact congrArg (fun v => (v j).val) htu
    have hEq : Sum.elim c.val d.val ∈ (rawGammaPresentation (M := M)).relation rawGammaPresentation Eq :=
      hCond hTags
    exact hc.symm.trans (((rawGammaPresentation (M := M)).relation_decode rawGammaPresentation Eq c d).mp hEq |>.trans hd)
  · intro h x y hx hy
    obtain ⟨t,c,hc,rfl⟩ := (gammaTransitionJointGraph_entries a R W f ω hR hW x).mp hx
    obtain ⟨u,d,hd,rfl⟩ := (gammaTransitionJointGraph_entries a R W f ω hR hW y).mp hy
    intro hTags
    have htu : (f t).val.2=(f u).val.2 := by
      funext j
      exact Subtype.ext (hTags j)
    apply ((rawGammaPresentation (M := M)).relation_decode rawGammaPresentation Eq c d).mpr
    exact hc.trans ((h t u htu).trans hd.symm)

end DiamondIntegral.Section6
