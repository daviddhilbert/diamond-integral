import «section 6».RVTemplateOperationValues

/-! A finite disjoint parameter choice joins complete continuous chart
formulas into one original-base template. Outside the covered parameter
set the complete family is zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r n m k : ℕ}

def finiteRVTemplateChoice (T : Fin k → ContinuousRVGraphTemplate (M := M) S p r n m)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (C : Fin k → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) :
    ContinuousRVGraphTemplate (M := M) S p r n m where
  graph := (⋃ i,({z | z ∘ Sum.inl ∈ C i} ∩ (T i).graph)) ∪
    ({z | z ∘ Sum.inl ∉ U} ∩ ContinuousRVGraphTemplate.zero.graph)
  definable := (Set.definable_iUnion_of_finite (fun i =>
    ((hC i).preimage_comp Sum.inl).inter (T i).definable)).union
      ((hU.preimage_comp Sum.inl).compl.inter ContinuousRVGraphTemplate.zero.definable)
  sorted z hz := by
    rcases hz with hz | hz
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact (T i).sorted z hi.2
    · exact ContinuousRVGraphTemplate.zero.sorted z hz.2

theorem finiteRVTemplateChoice_graph_at
    (T : Fin k → ContinuousRVGraphTemplate (M := M) S p r n m)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (C : Fin k → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hSub : ∀ i,C i ⊆ U) (hDisj : ∀ i j a,a ∈ C i → a ∈ C j → i=j)
    (a : Fin p → M) (i : Fin k) (hi : a ∈ C i) :
    {z : Fin r ⊕ (Fin n ⊕ Fin m) → M | Sum.elim a z ∈ (finiteRVTemplateChoice T U hU C hC).graph}=
      {z | Sum.elim a z ∈ (T i).graph} := by
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
      have hji := hDisj j i a hj.1 hi
      subst j
      exact hj.2
    · exact (hz.1 (hSub i hi)).elim
  · intro hz
    exact Or.inl (Set.mem_iUnion.mpr ⟨i,hi,hz⟩)

theorem finiteRVTemplateChoice_graph_outside
    (T : Fin k → ContinuousRVGraphTemplate (M := M) S p r n m)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (C : Fin k → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hSub : ∀ i,C i ⊆ U) (a : Fin p → M) (ha : a ∉ U) :
    {z : Fin r ⊕ (Fin n ⊕ Fin m) → M | Sum.elim a z ∈ (finiteRVTemplateChoice T U hU C hC).graph}=
      {z | Sum.elim a z ∈ (ContinuousRVGraphTemplate.zero (S := S)).graph} := by
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact (ha (hSub i hi.1)).elim
    · exact hz.2
  · intro hz
    exact Or.inr ⟨ha,hz⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finiteRVTemplateChoice_good
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : Fin k → ContinuousRVGraphTemplate (M := M) S p r n m)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (C : Fin k → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hSub : ∀ i,C i ⊆ U ∩ (T i).good)
    (hCover : ∀ a ∈ U,∃ i,a ∈ C i) (hDisj : ∀ i j a,a ∈ C i → a ∈ C j → i=j)
    (a : Fin p → M) : a ∈ (finiteRVTemplateChoice T U hU C hC).good := by
  let W := finiteRVTemplateChoice T U hU C hC
  have hSubU : ∀ i,C i ⊆ U := fun i a ha => (hSub i ha).1
  by_cases ha : a ∈ U
  · obtain ⟨i,hi⟩ := hCover a ha
    have hGood := (hSub i hi).2
    have hGraph := finiteRVTemplateChoice_graph_at T U hU C hC hSubU hDisj a i hi
    apply W.good_of_graph hv a ((T i).value a hGood)
    · intro u
      ext z
      exact (Set.ext_iff.mp hGraph _).trans (Set.ext_iff.mp ((T i).value_graph a hGood u) z)
    · exact (T i).value_continuous hv a hGood
  · have hGraph := finiteRVTemplateChoice_graph_outside T U hU C hC hSubU a ha
    apply W.good_of_graph hv a (fun _ _ _ => (0 : VF M))
    · intro u
      ext z
      exact (Set.ext_iff.mp hGraph _).trans (Set.ext_iff.mp (ContinuousRVGraphTemplate.zero_row a u) z)
    · exact fun _ => continuous_const

end DiamondIntegral.Section6
