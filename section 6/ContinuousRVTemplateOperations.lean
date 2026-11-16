import «section 6».BranchedShearPackingCodes

/-! Pure RV reindexing and definable RV case distinction preserve entire
continuous chart templates over the original base. These operations do
not choose formulas separately for individual VF points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r R n m : ℕ}
namespace ContinuousRVGraphTemplate

theorem value_eq_of_rows (T : ContinuousRVGraphTemplate (M := M) S p r n m)
    (a : Fin p → M) (ha : a ∈ T.good)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hRows : ∀ u,{z : Fin n ⊕ Fin m → M | Sum.elim a (Sum.elim (rvValues u) z) ∈ T.graph}=vfGraph (f u)) :
    T.value a ha=f := by
  funext u x i
  obtain ⟨y,hy⟩ := (Set.ext_iff.mp (hRows u) _).mp (T.value_mem a ha u x)
  have hyx : y=x := vfValues_injective (by funext j; exact congrFun hy (.inl j))
  subst y
  exact Subtype.ext (congrFun hy (.inr i)).symm

def reindexRV (T : ContinuousRVGraphTemplate (M := M) S p r n m) (σ : Fin r → Fin R) :
    ContinuousRVGraphTemplate (M := M) S p R n m where
  graph := {z | z ∘ Sum.map id (Sum.map σ id) ∈ T.graph}
  definable := T.definable.preimage_comp _
  sorted z hz := T.sorted (z ∘ Sum.map id (Sum.map σ id)) hz

theorem reindexRV_row (T : ContinuousRVGraphTemplate (M := M) S p r n m) (σ : Fin r → Fin R)
    (a : Fin p → M) (ha : a ∈ T.good) (u : Fin R → RVInfinity M) :
    {z : Fin n ⊕ Fin m → M | Sum.elim a (Sum.elim (rvValues u) z) ∈ (T.reindexRV σ).graph}=
      vfGraph (T.value a ha (u ∘ σ)) := by
  have hCode (z : Fin n ⊕ Fin m → M) :
      Sum.elim a (Sum.elim (rvValues u) z) ∘ Sum.map id (Sum.map σ id)=
        Sum.elim a (Sum.elim (rvValues (u ∘ σ)) z) := by
    funext i
    rcases i with i | (i | i) <;> rfl
  ext z
  change _ ∈ T.graph ↔ _
  rw [hCode]
  exact Set.ext_iff.mp (T.value_graph a ha (u ∘ σ)) z

def zero : ContinuousRVGraphTemplate (M := M) S p r n m where
  graph := {z | (∀ i : Fin n,iVF (z (.inr (.inr (.inl i))))) ∧
    ∀ j : Fin m,z (.inr (.inr (.inr j)))=iVFZero}
  definable := by
    have hInput : S.Definable LRV {z : Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M |
        ∀ i : Fin n,iVF (z (.inr (.inr (.inl i))))} :=
      (vfRawUniverse_definable S n).preimage_comp
        (fun i : Fin n => (Sum.inr (Sum.inr (Sum.inl i)) : Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin m))))
    have hOutput (j : Fin m) : S.Definable LRV {z : Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M |
        z (.inr (.inr (.inr j)))=iVFZero} :=
      (Set.DefinableFun.proj LRV).ofPred_eq rawVFZero_constant_definable
    convert hInput.inter (Set.definable_iInter_of_finite hOutput) using 1
    ext z
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Set.mem_iInter]
  sorted z hz := ⟨hz.1,fun j => (hz.2 j).symm ▸ (0 : VF M).property⟩

theorem zero_row (a : Fin p → M) (u : Fin r → RVInfinity M) :
    {z : Fin n ⊕ Fin m → M | Sum.elim a (Sum.elim (rvValues u) z) ∈
      (zero (M := M) (S := S) (p := p) (r := r) (n := n) (m := m)).graph}=
        vfGraph (fun _ : Fin n → VF M => fun _ : Fin m => (0 : VF M)) := by
  ext z
  constructor
  · intro hz
    let x : Fin n → VF M := fun i => ⟨z (.inl i),hz.1 i⟩
    refine ⟨x,?_⟩
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (hz.2 i).symm
  · rintro ⟨x,rfl⟩
    exact ⟨fun i => (x i).property,fun _ => rfl⟩

def rvCases (T U : ContinuousRVGraphTemplate (M := M) S p r n m)
    (P : Set (Fin r → M)) (hP : S.Definable LRV P) : ContinuousRVGraphTemplate (M := M) S p r n m where
  graph := ({z | z ∘ Sum.inr ∘ Sum.inl ∈ P} ∩ T.graph) ∪
    ({z | z ∘ Sum.inr ∘ Sum.inl ∉ P} ∩ U.graph)
  definable := ((hP.preimage_comp (Sum.inr ∘ Sum.inl)).inter T.definable).union
    ((hP.preimage_comp (Sum.inr ∘ Sum.inl)).compl.inter U.definable)
  sorted z hz := by
    rcases hz with hz | hz
    · exact T.sorted z hz.2
    · exact U.sorted z hz.2

theorem rvCases_row (T U : ContinuousRVGraphTemplate (M := M) S p r n m)
    (P : Set (Fin r → M)) (hP : S.Definable LRV P) (a : Fin p → M)
    (hT : a ∈ T.good) (hU : a ∈ U.good) (u : Fin r → RVInfinity M) :
    {z : Fin n ⊕ Fin m → M | Sum.elim a (Sum.elim (rvValues u) z) ∈ (T.rvCases U P hP).graph}=
      vfGraph (fun x => if rvValues u ∈ P then T.value a hT u x else U.value a hU u x) := by
  ext z
  change ((rvValues u ∈ P ∧ _ ∈ T.graph) ∨ (rvValues u ∉ P ∧ _ ∈ U.graph)) ↔ _
  by_cases h : rvValues u ∈ P
  · simpa only [h,true_and,not_true_eq_false,false_and,or_false,ite_true,Set.mem_setOf_eq] using
      Set.ext_iff.mp (T.value_graph a hT u) z
  · simpa only [h,false_and,not_false_eq_true,true_and,false_or,ite_false,Set.mem_setOf_eq] using
      Set.ext_iff.mp (U.value_graph a hU u) z

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem reindexRV_good
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : ContinuousRVGraphTemplate (M := M) S p r n m) (σ : Fin r → Fin R)
    (a : Fin p → M) (ha : a ∈ T.good) : a ∈ (T.reindexRV σ).good :=
  (T.reindexRV σ).good_of_graph hv a (fun u => T.value a ha (u ∘ σ))
    (T.reindexRV_row σ a ha) (fun u => T.value_continuous hv a ha (u ∘ σ))

theorem zero_good
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (a : Fin p → M) :
    a ∈ (zero (M := M) (S := S) (p := p) (r := r) (n := n) (m := m)).good :=
  zero.good_of_graph hv a _ (zero_row a) (fun _ => continuous_const)

theorem rvCases_good
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T U : ContinuousRVGraphTemplate (M := M) S p r n m)
    (P : Set (Fin r → M)) (hP : S.Definable LRV P) (a : Fin p → M)
    (hT : a ∈ T.good) (hU : a ∈ U.good) : a ∈ (T.rvCases U P hP).good := by
  apply (T.rvCases U P hP).good_of_graph hv a _ (T.rvCases_row U P hP a hT hU)
  intro u
  by_cases h : rvValues u ∈ P
  · simpa only [h,if_true] using T.value_continuous hv a hT u
  · simpa only [h,if_false] using U.value_continuous hv a hU u

end ContinuousRVGraphTemplate
end DiamondIntegral.Section6
