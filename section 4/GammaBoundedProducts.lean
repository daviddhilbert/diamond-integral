import «section 4».GammaProfileProducts

/-! Symmetric-box bounds on actual Gamma domains are preserved by
subsets, finite unions and the explicit coordinate-block product. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedProducts
open GammaProfileProducts FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def DomainBounded {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) : Prop :=
  ∃ β : Values.Gamma (M := M), ∀ z ∈ I, ∀ i, β⁻¹ ≤ z i ∧ z i ≤ β

theorem all_coordinates {A : Type*} (n m : ℕ) (P : A → Prop) (z : Fin (n + m) → A)
    (hh : ∀ i, P (z (headIndex n m i))) (ht : ∀ i, P (z (tailIndex n m i))) : ∀ i, P (z i) := by
  induction m with
  | zero => exact ht
  | succ m ih =>
    intro i
    exact Fin.cases (hh 0) (fun j => ih (Fin.tail z) (fun l => hh l.succ) ht j) i

theorem DomainBounded.subset {n : ℕ} {I J : Set (Fin n → Values.Gamma (M := M))}
    (hI : DomainBounded I) (hJI : J ⊆ I) : DomainBounded J := by
  obtain ⟨β, hβ⟩ := hI
  exact ⟨β, fun z hz => hβ z (hJI hz)⟩

theorem DomainBounded.empty (n : ℕ) : DomainBounded (∅ : Set (Fin n → Values.Gamma (M := M))) :=
  ⟨1, fun _ h => False.elim h⟩

theorem DomainBounded.unit : DomainBounded (Set.univ : Set (Fin 0 → Values.Gamma (M := M))) :=
  ⟨1, fun _ _ i => Fin.elim0 i⟩

theorem DomainBounded.union {n : ℕ} {I J : Set (Fin n → Values.Gamma (M := M))}
    (hI : DomainBounded I) (hJ : DomainBounded J) : DomainBounded (I ∪ J) := by
  obtain ⟨β, hβ⟩ := hI
  obtain ⟨γ, hγ⟩ := hJ
  refine ⟨max β γ, ?_⟩
  intro z hz i
  rcases hz with hz | hz
  · exact ⟨(inv_le_inv_iff.mpr (le_max_left β γ)).trans (hβ z hz i).1,
      (hβ z hz i).2.trans (le_max_left β γ)⟩
  · exact ⟨(inv_le_inv_iff.mpr (le_max_right β γ)).trans (hγ z hz i).1,
      (hγ z hz i).2.trans (le_max_right β γ)⟩

theorem DomainBounded.product {n m : ℕ} {I : Set (Fin m → Values.Gamma (M := M))}
    {J : Set (Fin n → Values.Gamma (M := M))} (hI : DomainBounded I) (hJ : DomainBounded J) :
    DomainBounded (productSet I J) := by
  obtain ⟨β, hβ⟩ := hI
  obtain ⟨γ, hγ⟩ := hJ
  refine ⟨max β γ, ?_⟩
  intro z hz
  apply all_coordinates n m (fun x => (max β γ)⁻¹ ≤ x ∧ x ≤ max β γ) z
  · intro i
    exact ⟨(inv_le_inv_iff.mpr (le_max_left β γ)).trans (hβ _ hz.1 i).1,
      (hβ _ hz.1 i).2.trans (le_max_left β γ)⟩
  · intro i
    exact ⟨(inv_le_inv_iff.mpr (le_max_right β γ)).trans (hγ _ hz.2 i).1,
      (hγ _ hz.2 i).2.trans (le_max_right β γ)⟩

end DiamondIntegral.Section4.GammaBoundedProducts
