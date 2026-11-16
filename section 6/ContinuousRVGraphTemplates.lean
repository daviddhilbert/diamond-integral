import «section 6».RVFamilyParameterLoci

/-! Original-base templates for whole RV-indexed families of
continuous VF maps, with a single admissibility condition for all labels. -/

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

structure ContinuousRVGraphTemplate (S : Set M) (p r n m : ℕ) where
  graph : Set (Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M)
  definable : S.Definable LRV graph
  sorted : ∀ z ∈ graph,(∀ i,iVF (z (.inr (.inr (.inl i))))) ∧
    ∀ i,iVF (z (.inr (.inr (.inr i))))

namespace ContinuousRVGraphTemplate
def good (T : ContinuousRVGraphTemplate (M := M) S p r n m) := rvFamilyGoodParameterLocus T.graph

theorem good_definable (T : ContinuousRVGraphTemplate (M := M) S p r n m) : S.Definable LRV T.good :=
  rvFamilyGoodParameterLocus_definable T.graph T.definable

theorem rowGood (T : ContinuousRVGraphTemplate (M := M) S p r n m)
    (a : Fin p → M) (ha : a ∈ T.good) (u : Fin r → RVInfinity M) :
    Sum.elim a (rvValues u) ∈ rvFamilyGoodRows T.graph := ha (rvValues u) ⟨u,rfl⟩

def value (T : ContinuousRVGraphTemplate (M := M) S p r n m)
    (a : Fin p → M) (ha : a ∈ T.good) (u : Fin r → RVInfinity M) (x : Fin n → VF M) : Fin m → VF M :=
  let h := (T.rowGood a ha u).1.1 (vfValues x) (fun i => (x i).property)
  fun i => ⟨h.choose i,h.choose_spec.1 i⟩

theorem value_mem (T : ContinuousRVGraphTemplate (M := M) S p r n m)
    (a : Fin p → M) (ha : a ∈ T.good) (u : Fin r → RVInfinity M) (x : Fin n → VF M) :
    Sum.elim a (Sum.elim (rvValues u) (Sum.elim (vfValues x) (vfValues (T.value a ha u x)))) ∈ T.graph :=
  ((T.rowGood a ha u).1.1 (vfValues x) (fun i => (x i).property)).choose_spec.2

theorem value_graph (T : ContinuousRVGraphTemplate (M := M) S p r n m)
    (a : Fin p → M) (ha : a ∈ T.good) (u : Fin r → RVInfinity M) :
    {z : Fin n ⊕ Fin m → M | Sum.elim a (Sum.elim (rvValues u) z) ∈ T.graph}=vfGraph (T.value a ha u) := by
  ext z
  constructor
  · intro hz
    have hSort := T.sorted _ hz
    let x : Fin n → VF M := fun i => ⟨z (.inl i),hSort.1 i⟩
    have hEta : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)=z := by funext i; cases i <;> rfl
    have hOld : Sum.elim a (Sum.elim (rvValues u) (Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr))) ∈ T.graph := hEta.symm ▸ hz
    have hUnique := (T.rowGood a ha u).1.2 (z ∘ Sum.inl) (z ∘ Sum.inr)
      (vfValues (T.value a ha u x)) hOld (T.value_mem a ha u x)
    refine ⟨x,?_⟩
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (congrFun hUnique i).symm
  · rintro ⟨x,rfl⟩
    exact T.value_mem a ha u x

theorem value_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : ContinuousRVGraphTemplate (M := M) S p r n m) (a : Fin p → M) (ha : a ∈ T.good)
    (u : Fin r → RVInfinity M) : Continuous (T.value a ha u) :=
  (mem_continuousParameterLocus_iff hv (rvFamilyJointGraph T.graph) (Sum.elim a (rvValues u))
    (T.value a ha u) (T.value_graph a ha u)).mp (T.rowGood a ha u).2

theorem good_of_graph
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : ContinuousRVGraphTemplate (M := M) S p r n m) (a : Fin p → M)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hSection : ∀ u,{z : Fin n ⊕ Fin m → M | Sum.elim a (Sum.elim (rvValues u) z) ∈ T.graph}=vfGraph (f u))
    (hCont : ∀ u,Continuous (f u)) : a ∈ T.good := by
  rintro _ ⟨u,rfl⟩
  refine ⟨⟨?_,?_⟩,(mem_continuousParameterLocus_iff hv (rvFamilyJointGraph T.graph)
    (Sum.elim a (rvValues u)) (f u) (hSection u)).mpr (hCont u)⟩
  · intro x hx
    let b : Fin n → VF M := fun i => ⟨x i,hx i⟩
    exact ⟨vfValues (f u b),(fun i => (f u b i).property),
      (Set.ext_iff.mp (hSection u) _).mpr ⟨b,rfl⟩⟩
  · intro x y z hy hz
    obtain ⟨b,hb⟩ := (Set.ext_iff.mp (hSection u) _).mp hy
    obtain ⟨c,hc⟩ := (Set.ext_iff.mp (hSection u) _).mp hz
    have hbc : b=c := vfValues_injective (by
      funext i; exact (congrFun hb (.inl i)).trans (congrFun hc (.inl i)).symm)
    subst c
    funext i
    exact (congrFun hb (.inr i)).symm.trans (congrFun hc (.inr i))

end ContinuousRVGraphTemplate
end DiamondIntegral.Section6
