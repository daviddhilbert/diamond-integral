import «section 6».GammaCoreParameterLoci

/-! The core-form parameter test has exact semantics on complete
actual transition graphs, including every proper Gamma representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

theorem gammaCoreJointGraph_entries
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (coreTag : Fin s) (x : GammaTransitionEntry (M := M) n r s → M) :
    Sum.elim a x ∈ gammaCoreJointGraph R W coreTag ↔
      ∃ t : A,∃ c : (rawGammaPresentation (M := M)).domain,
        (rawGammaPresentation (M := M)).decode c=(ω t).val ∧
        x=Sum.elim (mixedValues t.val) (Sum.elim (mixedValues (f t).val) c.val) ∧
        (f t).val.2 coreTag=branchTag true := by
  constructor
  · rintro ⟨hx,hFlag⟩
    obtain ⟨t,c,hc,rfl⟩ := (gammaTransitionJointGraph_entries a R W f ω hR hW x).mp hx
    exact ⟨t,c,hc,rfl,Subtype.ext hFlag⟩
  · rintro ⟨t,c,hc,rfl,hFlag⟩
    refine ⟨(gammaTransitionJointGraph_entries a R W f ω hR hW _).mpr ⟨t,c,hc,rfl⟩,?_⟩
    exact congrArg Subtype.val hFlag

theorem gammaCoreConstantParameterLocus_iff
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (j : Fin n) (coreTag : Fin s) :
    a ∈ gammaCoreConstantParameterLocus R W j coreTag ↔
      ∀ t u : A,(f t).val.2 coreTag=branchTag true → (f u).val.2 coreTag=branchTag true →
        (f t).val.2=(f u).val.2 →
          (∀ i,i ≠ j → (f t).val.1 i=(f u).val.1 i) → (ω t).val=(ω u).val := by
  constructor
  · intro h t u ht hu hTags hOther
    obtain ⟨c,hc⟩ := (rawGammaPresentation (M := M)).onto (ω t).val
    obtain ⟨d,hd⟩ := (rawGammaPresentation (M := M)).onto (ω u).val
    let x := Sum.elim (mixedValues t.val) (Sum.elim (mixedValues (f t).val) c.val)
    let y := Sum.elim (mixedValues u.val) (Sum.elim (mixedValues (f u).val) d.val)
    have hx := (gammaCoreJointGraph_entries a R W f ω hR hW coreTag x).mpr ⟨t,c,hc,rfl,ht⟩
    have hy := (gammaCoreJointGraph_entries a R W f ω hR hW coreTag y).mpr ⟨u,d,hd,rfl,hu⟩
    have hCond := h x y hx hy
    have hVF : ∀ i,i ≠ j → (mixedValues (f t).val) (.inl i)=(mixedValues (f u).val) (.inl i) := by
      intro i hi
      exact congrArg Subtype.val (hOther i hi)
    have hRV : ∀ i : Fin s,(mixedValues (f t).val) (.inr i)=(mixedValues (f u).val) (.inr i) := by
      intro i
      exact congrArg (fun v => (v i).val) hTags
    have hEq : Sum.elim c.val d.val ∈ (rawGammaPresentation (M := M)).relation rawGammaPresentation Eq :=
      hCond hVF hRV
    exact hc.symm.trans ((((rawGammaPresentation (M := M)).relation_decode rawGammaPresentation Eq c d).mp hEq).trans hd)
  · intro h x y hx hy
    obtain ⟨t,c,hc,rfl,ht⟩ := (gammaCoreJointGraph_entries a R W f ω hR hW coreTag x).mp hx
    obtain ⟨u,d,hd,rfl,hu⟩ := (gammaCoreJointGraph_entries a R W f ω hR hW coreTag y).mp hy
    intro hOther hTags
    have hRV : (f t).val.2=(f u).val.2 := funext (fun i => Subtype.ext (hTags i))
    have hVF : ∀ i,i ≠ j → (f t).val.1 i=(f u).val.1 i :=
      fun i hi => Subtype.ext (hOther i hi)
    apply ((rawGammaPresentation (M := M)).relation_decode rawGammaPresentation Eq c d).mpr
    exact hc.trans ((h t u ht hu hRV hVF).trans hd.symm)

end DiamondIntegral.Section6
