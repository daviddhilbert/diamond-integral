import «section 2».RawSingletonRows

/-! A finite list of definable partial unique choices gives one definable
choice on its covered domain. The priority is a finite syntactic index,
so it contributes no new model parameter. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

def firstChoiceDomain {X : Type*} {r : ℕ} (D : Fin r → Set X) (i : Fin r) : Set X :=
  D i \ ⋃ j : {j : Fin r // j < i}, D j.val

theorem firstChoiceDomain_cover {X : Type*} {r : ℕ} (D : Fin r → Set X) (x : X)
    (hx : ∃ i, x ∈ D i) : ∃ i, x ∈ firstChoiceDomain D i := by
  classical
  let Q := Finset.univ.filter (fun i : Fin r => x ∈ D i)
  have hQ : Q.Nonempty := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  let i := Q.min' hQ
  refine ⟨i,⟨(Finset.mem_filter.mp (Finset.min'_mem Q hQ)).2,?_⟩⟩
  intro h
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
  have hmin : i ≤ j.val := Finset.min'_le Q j.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  exact (not_le_of_gt j.property) hmin

theorem firstChoiceDomain_disjoint {X : Type*} {r : ℕ} (D : Fin r → Set X)
    {i j : Fin r} (hne : i ≠ j) : Disjoint (firstChoiceDomain D i) (firstChoiceDomain D j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hxj.2 (Set.mem_iUnion.mpr ⟨⟨i,hlt⟩,hxi.1⟩)
  · exact hxi.2 (Set.mem_iUnion.mpr ⟨⟨j,hgt⟩,hxj.1⟩)

variable {M : Type} [LRV.Structure M] {α : Type}

theorem firstChoiceDomain_definable (S : Set M) {r : ℕ}
    (D : Fin r → Set (α → M)) (hD : ∀ i, S.Definable LRV (D i)) (i : Fin r) :
    S.Definable LRV (firstChoiceDomain D i) :=
  (hD i).sdiff (Set.definable_iUnion_of_finite (fun j : {j : Fin r // j < i} => hD j.val))

theorem finite_partial_unique_choice (S : Set M) (J : Set (α → M)) (hJ : S.Definable LRV J)
    {r : ℕ} (R : Fin r → (α → M) → Set M)
    (hR : ∀ i, S.Definable LRV {z : α ⊕ Fin 1 → M | z (.inr 0) ∈ R i (z ∘ Sum.inl)})
    (hcover : ∀ p ∈ J, ∃ i, p ∈ rawSingletonRows (R i))
    (T : (α → M) → Set M) (hT : ∀ i, ∀ p ∈ J, R i p ⊆ T p) :
    ∃ f : (α → M) → M,
      S.Definable LRV {z : α ⊕ Fin 1 → M | z ∘ Sum.inl ∈ J ∧ f (z ∘ Sum.inl) = z (.inr 0)} ∧
      ∀ p ∈ J, f p ∈ T p := by
  let D (i : Fin r) := J ∩ rawSingletonRows (R i)
  have hD (i : Fin r) : S.Definable LRV (D i) := hJ.inter (rawSingletonRows_definable S (R i) (hR i))
  let C (p : α → M) : Set M := ⋃ i : Fin r, {y | p ∈ firstChoiceDomain D i ∧ y ∈ R i p}
  have hC : S.Definable LRV {z : α ⊕ Fin 1 → M | z (.inr 0) ∈ C (z ∘ Sum.inl)} := by
    convert Set.definable_iUnion_of_finite (fun i : Fin r =>
      (((firstChoiceDomain_definable S D hD i).preimage_comp Sum.inl).inter (hR i))) using 1
    ext z
    simp only [C,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_preimage]
  have huniq : J ⊆ rawSingletonRows C := by
    intro p hp
    have hcov : ∃ i, p ∈ D i := by
      obtain ⟨i,hi⟩ := hcover p hp
      exact ⟨i,hp,hi⟩
    obtain ⟨i,hi⟩ := firstChoiceDomain_cover D p hcov
    obtain ⟨y,hy,huy⟩ := hi.1.2
    refine ⟨y,Set.mem_iUnion.mpr ⟨i,hi,hy⟩,?_⟩
    intro z hz
    obtain ⟨j,hjp,hjz⟩ := Set.mem_iUnion.mp hz
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (firstChoiceDomain_disjoint D hne) hjp hi
    subst j
    exact huy z hjz
  refine ⟨rawUniqueChoice C,rawUniqueChoice_graph_definable S J hJ C hC huniq,?_⟩
  intro p hp
  obtain ⟨i,_,hi⟩ := Set.mem_iUnion.mp (rawUniqueChoice_mem C p (huniq hp))
  exact hT i p hp hi

end DiamondIntegral.Section2
