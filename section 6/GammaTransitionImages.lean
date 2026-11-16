import «section 6».MeasuredProgramSubstitution

/-! Actual Gamma graphs are transported through an entire transition
by first-order projection. For a bijective transition this is exactly
inverse composition, including every Gamma representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p q n r s : ℕ}

def gammaTransitionImage
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M)) :
    Set (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ (rawGammaPresentation (M := M)).Index) → M) :=
  {z | ∃ x : Fin n ⊕ Fin r → M,
    Sum.elim (z ∘ Sum.inl) (Sum.elim x (fun i => z (.inr (.inl i)))) ∈ R ∧
      Sum.elim (z ∘ Sum.inl) (Sum.elim x (fun i => z (.inr (.inr i)))) ∈ W}

theorem gammaTransitionImage_definable
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) : S.Definable LRV (gammaTransitionImage R W) := by
  let Z := (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ (rawGammaPresentation (M := M)).Index)) ⊕ (Fin n ⊕ Fin r)
  have h₁ : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i)))
        (Sum.elim (z ∘ Sum.inr) (fun i => z (.inl (.inr (.inl i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  have h₂ : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i)))
        (Sum.elim (z ∘ Sum.inr) (fun i => z (.inl (.inr (.inr i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  exact ((hR.preimage_map h₁).inter (hW.preimage_map h₂)).exists_of_finite

theorem gammaTransitionImage_at
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (hf : Function.Bijective f)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph) :
    {z | Sum.elim a z ∈ gammaTransitionImage R W}=
      (rawMixedSpace n s).relation rawGammaPresentation (ω.comp (f.inverse hf)).graph := by
  ext z
  constructor
  · rintro ⟨x,hRx,hWx⟩
    obtain ⟨hx,hy,t,ht,hft⟩ := (Set.ext_iff.mp hR _).mp hRx
    obtain ⟨hx',hγ,u,hu,hωu⟩ := (Set.ext_iff.mp hW _).mp hWx
    have htu : t=u := Subtype.ext (ht.trans hu.symm)
    subst u
    refine ⟨hy,hγ,f t,hft,?_⟩
    change (ω (f.inverse hf (f t))).val=_
    rw [Map.inverse_apply]
    exact hωu
  · rintro ⟨hy,hγ,t,ht,hηt⟩
    let u := f.inverse hf t
    refine ⟨mixedValues u.val,?_,?_⟩
    · apply (Set.ext_iff.mp hR _).mpr
      refine ⟨mixedValues_mem_domain _,hy,u,(decode_mixedValues _).symm,?_⟩
      have he := congrArg (fun x : B => x.val) (Map.apply_inverse f hf t)
      exact he.trans ht
    · apply (Set.ext_iff.mp hW _).mpr
      exact ⟨mixedValues_mem_domain _,hγ,u,(decode_mixedValues _).symm,hηt⟩

def GammaFormParameterTemplate.transport
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (R : MixedTransitionParameterTemplate (M := M) S p n r s) : GammaFormParameterTemplate (M := M) S p n s :=
  ⟨gammaTransitionImage R.graph W.graph,gammaTransitionImage_definable _ _ R.definable W.definable⟩

theorem GammaFormParameterTemplate.ext_graph
    {W U : GammaFormParameterTemplate (M := M) S p n r} (he : W.graph=U.graph) : W=U := by
  cases W
  cases U
  cases he
  rfl

theorem GammaFormParameterTemplate.transport_substitute
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (R : MixedTransitionParameterTemplate (M := M) S p n r s)
    (R' : MixedTransitionParameterTemplate (M := M) S q n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (he : R'.graph=parameterSubstitution h R.graph) :
    (W.transport R).substitute h=(W.substitute h).transport R' := by
  apply GammaFormParameterTemplate.ext_graph
  change parameterSubstitution h (gammaTransitionImage R.graph W.graph)=
    gammaTransitionImage R'.graph (parameterSubstitution h W.graph)
  rw [he]
  rfl

end DiamondIntegral.Section6
