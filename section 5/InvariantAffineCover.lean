import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Topology.Compactness.Compact

/-! A good finite action on a quasi-compact separated scheme has a finite
invariant affine open cover. The invariant opens are actual intersections
of translates; no affine stratification hypothesis is accepted as input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical CategoryTheory AlgebraicGeometry

def schemePointAction {X : Scheme} {G : Type} [Group G] (ρ : G →* Aut X) (g : G) (x : X) : X :=
  (ρ g).asIso.hom x

theorem schemePointAction_one {X : Scheme} {G : Type} [Group G] (ρ : G →* Aut X) (x : X) :
    schemePointAction ρ 1 x = x := by rw [schemePointAction, map_one]; rfl

theorem schemePointAction_mul {X : Scheme} {G : Type} [Group G] (ρ : G →* Aut X) (g h : G) (x : X) :
    schemePointAction ρ (g * h) x = schemePointAction ρ g (schemePointAction ρ h x) := by
  rw [schemePointAction, map_mul]
  rfl

theorem finite_invariant_affine_cover {X : Scheme} [X.IsSeparated] [CompactSpace X]
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut X)
    (hgood : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g : G, schemePointAction ρ g x ∈ U) :
    ∃ s : Finset X, ∃ V : X → X.Opens,
      (∀ x, IsAffineOpen (V x)) ∧
      (∀ x g z, schemePointAction ρ g z ∈ V x ↔ z ∈ V x) ∧
      ∀ z, ∃ x ∈ s, z ∈ V x := by
  choose U hU hOrbit using hgood
  let V : X → X.Opens := fun x => ⨅ g : G, ((ρ g).asIso.hom ⁻¹ᵁ U x)
  have hmem (x z : X) : z ∈ V x ↔ ∀ g : G, schemePointAction ρ g z ∈ U x := by
    change z ∈ (↑(⨅ g : G, ((ρ g).asIso.hom ⁻¹ᵁ U x)) : Set X) ↔ _
    rw [TopologicalSpace.Opens.coe_iInf]
    simp only [Set.mem_iInter]
    rfl
  have hV (x : X) : IsAffineOpen (V x) := IsAffineOpen.iInf (fun g => (hU x).preimage (ρ g).asIso.hom)
  have hInv (x : X) (g : G) (z : X) : schemePointAction ρ g z ∈ V x ↔ z ∈ V x := by
    rw [hmem, hmem]
    constructor
    · intro h k
      have he : schemePointAction ρ (k * g⁻¹) (schemePointAction ρ g z) = schemePointAction ρ k z := by
        rw [← schemePointAction_mul]
        simp [mul_assoc]
      exact he ▸ h (k * g⁻¹)
    · intro h k
      rw [← schemePointAction_mul]
      exact h (k * g)
  have hcover : (Set.univ : Set X) ⊆ ⋃ x : X, (V x : Set X) := by
    intro z _
    exact Set.mem_iUnion.mpr ⟨z, (hmem z z).mpr (hOrbit z)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen) hcover
  refine ⟨s, V, hV, hInv, ?_⟩
  intro z
  have hz := hs (Set.mem_univ z)
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hxs, hzx⟩ := Set.mem_iUnion.mp hx
  exact ⟨x, hxs, hzx⟩

end DiamondIntegral.Section5
