import «section 5».ClosedFamilyStrata
import «section 5».ConstructibleClosedGenerators
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.Group.Units.Equiv

/-! Finite invariant locally closed strata adapted to any prescribed
finite family of constructible subsets. Each prescribed subset restricts
to a clopen subset of each stratum. No dimension induction is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Set Topology
universe u
variable {X : Type u} [TopologicalSpace X]
variable {G : Type*} [Group G] [Fintype G]

theorem finite_invariant_constructible_strata {ι : Type*} [Fintype ι]
    (ρ : G →* (X ≃ₜ X)) (D : ι → Set X) (hD : ∀ i, IsConstructible (D i)) :
    ∃ (n : ℕ) (S : Fin n → Set X),
      (∀ k, IsLocallyClosed (S k)) ∧
      (∀ k g x, ρ g x ∈ S k ↔ x ∈ S k) ∧
      (∀ x, ∃! k, x ∈ S k) ∧
      (∀ k i, IsClopen {x : S k | x.val ∈ D i}) := by
  obtain ⟨s, hs, hgen⟩ := finite_constructible_closed_generators D hD
  let J := ↥s × G
  let C : J → Set X := fun j => (ρ j.2) ⁻¹' j.1.val
  have hC (j : J) : IsClosed (C j) := (hs j.1.val j.1.property).preimage (ρ j.2).continuous
  refine ⟨Fintype.card J + 1, fun k => closedFamilyStratum C k.val,
    fun k => closedFamilyStratum_isLocallyClosed C hC k.val, ?_,
    closedFamilyStratum_unique C, ?_⟩
  · intro k g x
    let e : J ≃ J := Equiv.prodCongr (Equiv.refl _) (Equiv.mulRight g)
    have he (j : J) : ρ g x ∈ C j ↔ x ∈ C (e j) := by
      change ρ j.2 (ρ g x) ∈ j.1.val ↔ ρ (j.2 * g) x ∈ j.1.val
      rw [map_mul, Homeomorph.mul_apply]
    have hdepth := closedFamilyDepth_permutation C e (ρ g x) x he
    change closedFamilyDepth C (ρ g x) = k.val ↔ closedFamilyDepth C x = k.val
    rw [hdepth]
  · intro k i
    apply hgen i (closedFamilyStratum C k.val) Subtype.val
    intro Z hZ
    have h := closedFamilyStratum_generator_isClopen C hC k.val (⟨Z, hZ⟩, 1)
    have he : {x : closedFamilyStratum C k.val | x.val ∈ C (⟨Z, hZ⟩, 1)} =
        Subtype.val ⁻¹' Z := by
      ext x
      change ρ 1 x.val ∈ Z ↔ x.val ∈ Z
      rw [map_one, Homeomorph.one_apply]
    rw [he] at h
    exact h

end DiamondIntegral.Section5
