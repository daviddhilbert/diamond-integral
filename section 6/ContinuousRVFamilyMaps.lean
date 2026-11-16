import «section 6».PartialFocusRVFamilyTemplates

/-! Admissible whole-family templates give actual original-base
definable maps on any current mixed domain. Their complete family
graphs, rather than independently selected RV sections, define the map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r n m : ℕ}

theorem ContinuousRVGraphTemplate.family_graph
    (T : ContinuousRVGraphTemplate (M := M) S p r n m) (a : Fin p → M) (ha : a ∈ T.good) :
    rvVFGraph (T.value a ha)={z | z ∘ Sum.inl ∈ Set.range rvValues ∧ Sum.elim a z ∈ T.graph} := by
  ext z
  constructor
  · rintro ⟨u,x,rfl⟩
    exact ⟨⟨u,rfl⟩,T.value_mem a ha u x⟩
  · rintro ⟨⟨u,hu⟩,hz⟩
    have hEta : Sum.elim (rvValues u) (z ∘ Sum.inr)=z := by
      rw [hu]
      funext i; cases i <;> rfl
    have hRow : Sum.elim a (Sum.elim (rvValues u) (z ∘ Sum.inr)) ∈ T.graph := hEta.symm ▸ hz
    obtain ⟨x,hx⟩ := (Set.ext_iff.mp (T.value_graph a ha u) _).mp hRow
    exact ⟨u,x,(congrArg (Sum.elim (rvValues u)) hx).trans hEta⟩

theorem ContinuousRVGraphTemplate.family_graph_definable
    (T : ContinuousRVGraphTemplate (M := M) S p r n m) (a : Fin p → M) (ha : a ∈ T.good) :
    (S ∪ Set.range a).Definable LRV (rvVFGraph (T.value a ha)) := by
  rw [T.family_graph a ha]
  let fix (z : Fin r ⊕ (Fin n ⊕ Fin m) → M) := Sum.elim a z
  have hFix : (S ∪ Set.range a).DefinableMap LRV fix := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have hRV : (S ∪ Set.range a).Definable LRV (Set.range (rvValues (M := M) (n := r))) :=
    (rawRVSpace (M := M) r).definable_domain _
  exact (hRV.preimage_comp (Sum.inl : Fin r → Fin r ⊕ (Fin n ⊕ Fin m))).inter
    ((T.definable.mono Set.subset_union_left).preimage_map hFix)

def rvFamilyGraphIndex (n r m : ℕ) : Fin r ⊕ (Fin n ⊕ Fin m) → (Fin n ⊕ Fin r) ⊕ Fin m :=
  Sum.elim (Sum.inl ∘ Sum.inr) (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)

theorem rvVFGraph_relation_code
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M) :
    (rawMixedSpace (M := M) n r).relation (rawVFSpace m) (fun x y => f x.2 x.1=y)=
      (fun z : (Fin n ⊕ Fin r) ⊕ Fin m → M => z ∘ rvFamilyGraphIndex n r m) ⁻¹' rvVFGraph f := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawVFSpace (M := M) m
  let e : Fin r ⊕ (Fin n ⊕ Fin m) → (Fin n ⊕ Fin r) ⊕ Fin m :=
    Sum.elim (Sum.inl ∘ Sum.inr) (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)
  have hEq : P.relation Q (fun x y => f x.2 x.1=y)=
      (fun z : (Fin n ⊕ Fin r) ⊕ Fin m → M => z ∘ e) ⁻¹' rvVFGraph f := by
    ext z
    constructor
    · rintro ⟨hp,hq,hEq⟩
      let x := P.decode ⟨z ∘ Sum.inl,hp⟩
      let y := Q.decode ⟨z ∘ Sum.inr,hq⟩
      refine ⟨x.2,x.1,?_⟩
      have hX := mixedValues_decode (⟨z ∘ Sum.inl,hp⟩ : P.domain)
      have hY := vfValues_decode (⟨z ∘ Sum.inr,hq⟩ : Q.domain)
      change f x.2 x.1=y at hEq
      rw [hEq]
      funext i
      rcases i with i | (i | i)
      · exact congrFun hX (.inr i)
      · exact congrFun hX (.inl i)
      · exact congrFun hY i
    · rintro ⟨u,x,hCode⟩
      have hX : mixedValues (x,u)=z ∘ Sum.inl := by
        funext i
        cases i with
        | inl i => exact congrFun hCode (.inr (.inl i))
        | inr i => exact congrFun hCode (.inl i)
      have hY : vfValues (f u x)=z ∘ Sum.inr := by
        funext i
        exact congrFun hCode (.inr (.inr i))
      have hp : z ∘ Sum.inl ∈ P.domain := hX ▸ mixedValues_mem_domain (x,u)
      have hq : z ∘ Sum.inr ∈ Q.domain := ⟨f u x,hY⟩
      have hx : P.decode ⟨z ∘ Sum.inl,hp⟩=(x,u) :=
        mixedValues_injective ((mixedValues_decode _).trans hX.symm)
      have hy : Q.decode ⟨z ∘ Sum.inr,hq⟩=f u x := vfValues_injective ((vfValues_decode _).trans hY.symm)
      exact ⟨hp,hq,by rw [hx,hy]⟩
  exact hEq

theorem rvVFGraph_relation_definable
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (rvVFGraph f)) :
    (rawMixedSpace (M := M) n r).RelationDefinable (rawVFSpace m) S (fun x y => f x.2 x.1=y) := by
  change S.Definable LRV ((rawMixedSpace n r).relation (rawVFSpace m) (fun x y => f x.2 x.1=y))
  rw [rvVFGraph_relation_code f]
  exact hf.preimage_comp (rvFamilyGraphIndex n r m)

def rvFamilyMap (A : DefSet (rawMixedSpace (M := M) n r) S)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (rvVFGraph f)) : Map A (DefSet.univ (rawVFSpace (M := M) m) S) := by
  refine ⟨fun x => ⟨f x.val.2 x.val.1,Set.mem_univ _⟩,?_⟩
  apply ((rvVFGraph_relation_definable f hf).inter (rawMixedSpace n r) (rawVFSpace m)
    (A.definable.left_relation (rawMixedSpace n r) (rawVFSpace m))).congr
  intro x y
  constructor
  · rintro ⟨h,hx⟩
    exact ⟨⟨x,hx⟩,rfl,h⟩
  · rintro ⟨x,rfl,h⟩
    exact ⟨h,x.property⟩

end DiamondIntegral.Section6
