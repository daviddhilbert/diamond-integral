import «section 5».MonomialDecomposition

/-! The value-induced monomial decomposition is also a finite disjoint
partition of its literal RV source, including the empty source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem ground_monomial_source_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    ∃ N : ℕ, ∃ P : Fin N → GroundMonomialPiece X,
      (∀ i j, i ≠ j → Disjoint (P i).source.carrier (P j).source.carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (P i).source.carrier := by
  obtain ⟨N, P, hd, hcov⟩ := ground_global_monomial_decomposition hκ hs h00 hr hγ hΓ X
  refine ⟨N, P, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hi' := (P i).source_cut ▸ hi
    have hj' := (P j).source_cut ▸ hj
    exact Set.disjoint_left.mp (hd i j hij) hi'.2 hj'.2
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (hcov (rvUnitTupleValues x)).mp ⟨x, hx, rfl⟩
      exact ⟨i, (P i).source_cut.symm ▸ ⟨hx, hi⟩⟩
    · rintro ⟨i, hi⟩
      exact ((P i).source_cut ▸ hi).1

end DiamondIntegral.Section5
