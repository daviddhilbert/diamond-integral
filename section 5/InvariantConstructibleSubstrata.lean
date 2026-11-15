import «section 5».SchemeInvariantStrata
import Mathlib.Topology.NoetherianSpace

/-! Invariant locally closed stratification of a constructible locus,
adapted to a finite family of constructible branch images. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Topology TopologicalSpace

theorem locallyClosed_constructible_of_noetherian {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {S : Set X} (hS : IsLocallyClosed S) : IsConstructible S := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hS
  exact ((NoetherianSpace.isCompact U).isConstructible hU).inter
    (isConstructible_compl.mp ((NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl))

theorem finite_invariant_constructible_substrata {X : Type} [TopologicalSpace X]
    {G J : Type} [Group G] [Fintype G] [Fintype J]
    (ρ : G →* (X ≃ₜ X)) (U : Set X) (hU : IsConstructible U)
    (hInv : ∀ g x, ρ g x ∈ U ↔ x ∈ U)
    (D : J → Set X) (hD : ∀ j, IsConstructible (D j)) :
    ∃ (n : ℕ) (S : Fin n → Set X),
      (∀ k, IsLocallyClosed (S k)) ∧ (∀ k, S k ⊆ U) ∧
      (∀ k g x, ρ g x ∈ S k ↔ x ∈ S k) ∧
      (∀ x, x ∈ U ↔ ∃! k, x ∈ S k) ∧
      (∀ k j, IsClopen {x : S k | x.val ∈ D j}) := by
  let E : Option J → Set X := fun j => j.elim U D
  have hE : ∀ j, IsConstructible (E j) := by
    intro j
    cases j with
    | none => exact hU
    | some j => exact hD j
  obtain ⟨n, R, hR, hRInv, hpart, hcl⟩ := finite_invariant_constructible_strata ρ E hE
  refine ⟨n, (fun k => R k ∩ U), ?_, (fun _ => Set.inter_subset_right), ?_, ?_, ?_⟩
  · intro k
    exact clopen_inter_locallyClosed (R k) U (hR k) (hcl k none)
  · intro k g x
    exact and_congr (hRInv k g x) (hInv g x)
  · intro x
    constructor
    · intro hx
      obtain ⟨k, hk, huniq⟩ := hpart x
      exact ⟨k, ⟨hk, hx⟩, fun j hj => huniq j hj.1⟩
    · rintro ⟨k, hk, _⟩
      exact hk.2
  · intro k j
    let f : ↥(R k ∩ U) → R k := fun x => ⟨x.val, x.property.1⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    exact (hcl k (some j)).preimage hf

end DiamondIntegral.Section5
