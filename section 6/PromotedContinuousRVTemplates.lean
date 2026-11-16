import «section 6».ContinuousRVGraphTemplates

/-! Compactness selects finitely many formulas for whole continuous
RV-indexed focus families. Every old RV label is retained inside one
complete family graph when the real parameter tuple is promoted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def rvVFGraph (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M) :
    Set (Fin r ⊕ (Fin n ⊕ Fin m) → M) :=
  {z | ∃ u x,Sum.elim (rvValues u) (Sum.elim (vfValues x) (vfValues (f u x)))=z}

theorem rvVFGraph_section
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M) (u : Fin r → RVInfinity M) :
    {z : Fin n ⊕ Fin m → M | Sum.elim (rvValues u) z ∈ rvVFGraph f}=vfGraph (f u) := by
  ext z
  constructor
  · rintro ⟨v,x,h⟩
    have hvu : v=u := rvValues_injective (by funext i; exact congrFun h (.inl i))
    subst v
    exact ⟨x,by funext i; exact congrFun h (.inr i)⟩
  · rintro ⟨x,h⟩
    exact ⟨u,x,congrArg (Sum.elim (rvValues u)) h⟩

theorem exists_promoted_continuous_rv_graph_template
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin p → M) (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hf : (S ∪ Set.range a).Definable LRV (rvVFGraph f)) (hCont : ∀ u,Continuous (f u)) :
    ∃ T : ContinuousRVGraphTemplate (M := M) S p r n m,a ∈ T.good ∧
      {z : Fin r ⊕ (Fin n ⊕ Fin m) → M | Sum.elim a z ∈ T.graph}=rvVFGraph f := by
  obtain ⟨R,hR,hSection⟩ := SpecialTransformations.ModelTheory.promote_definable_tuple_fibre LRV S a (rvVFGraph f) hf
  let H : Set (Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M) := {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R}
  let W := H ∩ {z | (∀ i,iVF (z (.inr (.inr (.inl i))))) ∧ ∀ i,iVF (z (.inr (.inr (.inr i))))}
  have hW : S.Definable LRV W := hR.inter
    (((vfRawUniverse_definable S n).preimage_comp
      (fun i : Fin n => (Sum.inr (Sum.inr (Sum.inl i)) : Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin m))))).inter
      ((vfRawUniverse_definable S m).preimage_comp
        (fun i : Fin m => (Sum.inr (Sum.inr (Sum.inr i)) : Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin m))))))
  let T : ContinuousRVGraphTemplate (M := M) S p r n m := ⟨W,hW,fun _ h => h.2⟩
  have hT : {z : Fin r ⊕ (Fin n ⊕ Fin m) → M | Sum.elim a z ∈ T.graph}=rvVFGraph f := by
    ext z
    have hAt : (a,z) ∈ R ↔ z ∈ rvVFGraph f := Set.ext_iff.mp hSection z
    constructor
    · intro hz
      exact hAt.mp hz.1
    · intro hz
      refine ⟨hAt.mpr hz,?_⟩
      obtain ⟨u,x,rfl⟩ := hz
      exact ⟨fun i => (x i).property,fun i => (f u x i).property⟩
  have hRow (u) : {z : Fin n ⊕ Fin m → M | Sum.elim a (Sum.elim (rvValues u) z) ∈ T.graph}=vfGraph (f u) := by
    ext z
    exact (Set.ext_iff.mp hT _).trans (Set.ext_iff.mp (rvVFGraph_section f u) z)
  exact ⟨T,T.good_of_graph hv a f hRow hCont,hT⟩

theorem exists_finite_continuous_rv_graph_templates
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin p → M)) (hA : S.Definable LRV A)
    (hLocal : ∀ a ∈ A,∃ f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M,
      (S ∪ Set.range a).Definable LRV (rvVFGraph f) ∧ ∀ u,Continuous (f u)) :
    ∃ k : ℕ,∃ T : Fin k → ContinuousRVGraphTemplate (M := M) S p r n m,
      ∀ a ∈ A,∃ i,a ∈ (T i).good := by
  let C := Set.range (fun T : ContinuousRVGraphTemplate (M := M) S p r n m => T.good)
  have hC : ∀ c ∈ C,S.Definable LRV c := by rintro c ⟨T,rfl⟩; exact T.good_definable
  have hCover (a) (ha : a ∈ A) : ∃ c ∈ C,a ∈ c := by
    obtain ⟨f,hf,hCont⟩ := hLocal a ha
    obtain ⟨T,hT,_⟩ := exists_promoted_continuous_rv_graph_template hv a f hf hCont
    exact ⟨T.good,⟨T,rfl⟩,hT⟩
  obtain ⟨C₀,hFin,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall A hA C hC hCover
  letI : Fintype C₀ := hFin.fintype
  let e := Fintype.equivFin C₀
  let chooseT (c : C₀) := (hSub c.property).choose
  have hT (c : C₀) : (chooseT c).good=c.val := (hSub c.property).choose_spec
  refine ⟨Fintype.card C₀,fun i => chooseT (e.symm i),?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hCov a ha
  refine ⟨e ⟨c,hc⟩,?_⟩
  change a ∈ (chooseT (e.symm (e ⟨c,hc⟩))).good
  rw [e.symm_apply_apply,hT]
  exact hac

end DiamondIntegral.Section6
