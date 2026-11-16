import «section 6».FunctionalParameterLoci
import Section3.GammaBaseTools

/-! Actual continuous VF graph templates over the original base.
Admissibility is a definable parameter condition. A graph defined using
one parameter tuple promotes to such a template without adjoining names. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure ContinuousVFGraphTemplate (S : Set M) (p n m : ℕ) where
  graph : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M)
  definable : S.Definable LRV graph
  sorted : ∀ z ∈ graph,(∀ i,iVF (z (.inr (.inl i)))) ∧ ∀ i,iVF (z (.inr (.inr i)))

namespace ContinuousVFGraphTemplate
def good (T : ContinuousVFGraphTemplate (M := M) S p n m) : Set (Fin p → M) :=
  (totalVFGraphParameterLocus T.graph ∩ singleVFGraphParameterLocus T.graph) ∩ continuousParameterLocus T.graph

theorem good_definable (T : ContinuousVFGraphTemplate (M := M) S p n m) : S.Definable LRV T.good :=
  ((totalVFGraphParameterLocus_definable T.graph T.definable).inter
    (singleVFGraphParameterLocus_definable T.graph T.definable)).inter
      (continuousParameterLocus_definable T.graph T.definable)

def value (T : ContinuousVFGraphTemplate (M := M) S p n m) (t : Fin p → M) (ht : t ∈ T.good)
    (x : Fin n → VF M) : Fin m → VF M :=
  let y := (ht.1.1 (vfValues x) (fun i => (x i).property)).choose
  fun i => ⟨y i,(ht.1.1 (vfValues x) (fun i => (x i).property)).choose_spec.1 i⟩

theorem value_mem (T : ContinuousVFGraphTemplate (M := M) S p n m)
    (t : Fin p → M) (ht : t ∈ T.good) (x : Fin n → VF M) :
    Sum.elim t (Sum.elim (vfValues x) (vfValues (T.value t ht x))) ∈ T.graph :=
  (ht.1.1 (vfValues x) (fun i => (x i).property)).choose_spec.2

theorem value_graph (T : ContinuousVFGraphTemplate (M := M) S p n m)
    (t : Fin p → M) (ht : t ∈ T.good) :
    {z : Fin n ⊕ Fin m → M | Sum.elim t z ∈ T.graph}=vfGraph (T.value t ht) := by
  ext z
  constructor
  · intro hz
    have hSort := T.sorted (Sum.elim t z) hz
    let x : Fin n → VF M := fun i => ⟨z (.inl i),hSort.1 i⟩
    have hEta : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)=z := by funext i; cases i <;> rfl
    have hOld : Sum.elim t (Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)) ∈ T.graph := hEta.symm ▸ hz
    have hUnique := ht.1.2 (z ∘ Sum.inl) (z ∘ Sum.inr) (vfValues (T.value t ht x)) hOld (T.value_mem t ht x)
    refine ⟨x,?_⟩
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (congrFun hUnique i).symm
  · rintro ⟨x,rfl⟩
    exact T.value_mem t ht x

theorem value_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : ContinuousVFGraphTemplate (M := M) S p n m) (t : Fin p → M) (ht : t ∈ T.good) :
    Continuous (T.value t ht) :=
  (mem_continuousParameterLocus_iff hv T.graph t (T.value t ht) (T.value_graph t ht)).mp ht.2

theorem good_of_graph
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : ContinuousVFGraphTemplate (M := M) S p n m) (t : Fin p → M)
    (f : (Fin n → VF M) → Fin m → VF M)
    (hSection : {z : Fin n ⊕ Fin m → M | Sum.elim t z ∈ T.graph}=vfGraph f)
    (hCont : Continuous f) : t ∈ T.good := by
  refine ⟨⟨?_,?_⟩,(mem_continuousParameterLocus_iff hv T.graph t f hSection).mpr hCont⟩
  · intro x hx
    let a : Fin n → VF M := fun i => ⟨x i,hx i⟩
    refine ⟨vfValues (f a),(fun i => (f a i).property),?_⟩
    exact (Set.ext_iff.mp hSection _).mpr ⟨a,rfl⟩
  · intro x y z hy hz
    obtain ⟨a,ha⟩ := (Set.ext_iff.mp hSection _).mp hy
    obtain ⟨b,hb⟩ := (Set.ext_iff.mp hSection _).mp hz
    have hInput : a=b := vfValues_injective (by
      funext i
      exact (congrFun ha (.inl i)).trans (congrFun hb (.inl i)).symm)
    subst b
    funext i
    exact (congrFun ha (.inr i)).symm.trans (congrFun hb (.inr i))

end ContinuousVFGraphTemplate

theorem exists_promoted_continuous_vf_graph_template
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin p → M) (f : (Fin n → VF M) → Fin m → VF M)
    (hf : (S ∪ Set.range a).Definable LRV (vfGraph f)) (hCont : Continuous f) :
    ∃ T : ContinuousVFGraphTemplate (M := M) S p n m,a ∈ T.good ∧
      {z : Fin n ⊕ Fin m → M | Sum.elim a z ∈ T.graph}=vfGraph f := by
  obtain ⟨R,hR,hSection⟩ := SpecialTransformations.ModelTheory.promote_definable_tuple_fibre LRV S a (vfGraph f) hf
  let H : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M) := {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R}
  let W := H ∩ {z | (∀ i,iVF (z (.inr (.inl i)))) ∧ ∀ i,iVF (z (.inr (.inr i)))}
  have hW : S.Definable LRV W :=
    hR.inter (((vfRawUniverse_definable S n).preimage_comp (fun i : Fin n => (Sum.inr (Sum.inl i) : Fin p ⊕ (Fin n ⊕ Fin m)))).inter
      ((vfRawUniverse_definable S m).preimage_comp (fun i : Fin m => (Sum.inr (Sum.inr i) : Fin p ⊕ (Fin n ⊕ Fin m)))))
  let T : ContinuousVFGraphTemplate (M := M) S p n m := ⟨W,hW,fun _ h => h.2⟩
  have hT : {z : Fin n ⊕ Fin m → M | Sum.elim a z ∈ T.graph}=vfGraph f := by
    ext z
    have hAt : (a,z) ∈ R ↔ z ∈ vfGraph f := Set.ext_iff.mp hSection z
    constructor
    · intro hz
      exact hAt.mp hz.1
    · intro hz
      refine ⟨hAt.mpr hz,?_⟩
      obtain ⟨x,rfl⟩ := hz
      exact ⟨fun i => (x i).property,fun i => (f x i).property⟩
  exact ⟨T,T.good_of_graph hv a f hT hCont,hT⟩

end DiamondIntegral.Section6
