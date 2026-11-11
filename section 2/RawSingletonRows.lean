import «section 2».FiniteChoice

/-! Uniform first-order singleton-row guards and unique definable
inversion. These are logical tools for the representative choice in 2.35. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {α : Type}

def rawSingletonRows (R : (α → M) → Set M) : Set (α → M) :=
  {p | ∃! y, y ∈ R p}

theorem rawSingletonRows_definable (S : Set M) (R : (α → M) → Set M)
    (hR : S.Definable LRV {z : α ⊕ Fin 1 → M | z (.inr 0) ∈ R (z ∘ Sum.inl)}) :
    S.Definable LRV (rawSingletonRows R) := by
  let idx : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hRy := hR.preimage_comp idx
  have heq := (Set.DefinableFun.proj LRV (A := S) (i := (Sum.inr 0 : (α ⊕ Fin 1) ⊕ Fin 1))).ofPred_eq
    (Set.DefinableFun.proj LRV (i := (.inl (.inr 0) : (α ⊕ Fin 1) ⊕ Fin 1)))
  have hall := (hRy.himp heq).forall_of_finite
  convert (hR.inter hall).exists_of_finite using 1
  ext p
  change (∃! y, y ∈ R p) ↔ (∃ x : Fin 1 → M, _)
  constructor
  · rintro ⟨x,hx,huniq⟩
    refine ⟨fun _ => x,hx,?_⟩
    intro y hy
    exact huniq (y 0) hy
  · rintro ⟨x,hx,huniq⟩
    exact ⟨x 0,hx,fun y hy => huniq (fun _ => y) hy⟩

noncomputable def rawUniqueChoice (R : (α → M) → Set M) (p : α → M) : M := by
  classical
  exact if h : ∃! y, y ∈ R p then Classical.choose h else
    Structure.funMap (L := LRV) Fn.vfZero Fin.elim0

theorem rawUniqueChoice_mem (R : (α → M) → Set M) (p : α → M)
    (h : p ∈ rawSingletonRows R) : rawUniqueChoice R p ∈ R p := by
  classical
  change ∃! y, y ∈ R p at h
  rw [rawUniqueChoice,dite_eq_left h]
  exact (Classical.choose_spec h).1

theorem rawUniqueChoice_graph_definable (S : Set M) (J : Set (α → M))
    (hJ : S.Definable LRV J) (R : (α → M) → Set M)
    (hR : S.Definable LRV {z : α ⊕ Fin 1 → M | z (.inr 0) ∈ R (z ∘ Sum.inl)})
    (huniq : J ⊆ rawSingletonRows R) :
    S.Definable LRV {z : α ⊕ Fin 1 → M |
      z ∘ Sum.inl ∈ J ∧ rawUniqueChoice R (z ∘ Sum.inl) = z (.inr 0)} := by
  have hspec (p : α → M) (hp : p ∈ J) (y : M) : y ∈ R p ↔ rawUniqueChoice R p = y := by
    have hf := rawUniqueChoice_mem R p (huniq hp)
    obtain ⟨c,hc,hcuniq⟩ := huniq hp
    exact ⟨fun hy => (hcuniq _ hf).trans (hcuniq y hy).symm,fun hy => hy ▸ hf⟩
  convert (hJ.preimage_comp Sum.inl).inter hR using 1
  ext z
  change (z ∘ Sum.inl ∈ J ∧ rawUniqueChoice R (z ∘ Sum.inl) = z (.inr 0)) ↔
    (z ∘ Sum.inl ∈ J ∧ z (.inr 0) ∈ R (z ∘ Sum.inl))
  exact and_congr_right (fun hp => (hspec _ hp _).symm)

end DiamondIntegral.Section2
