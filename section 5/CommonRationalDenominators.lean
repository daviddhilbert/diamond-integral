import «section 5».DefinableRationalGraphs

/-! Finite rational tuple covers with one common denominator on each
piece, including empty tuples. These are the data of maps from principal
affine opens. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
open scoped BigOperators
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def rationalTupleDenominator {n m : ℕ}
    (r : Fin m → MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ := ∏ j, (r j).2

def rationalTupleNumerator {n m : ℕ}
    (r : Fin m → MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ) (j : Fin m) :
    MvPolynomial (Fin n) ℂ := (r j).1 * ∏ k ∈ Finset.univ.erase j, (r k).2

theorem rationalTuple_common_denominator {n m : ℕ}
    (r : Fin m → MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) (y : Fin m → ℂ)
    (hr : ∀ j, (r j).2.eval₂ (RingHom.id ℂ) x ≠ 0 ∧
      y j * (r j).2.eval₂ (RingHom.id ℂ) x = (r j).1.eval₂ (RingHom.id ℂ) x) :
    (rationalTupleDenominator r).eval₂ (RingHom.id ℂ) x ≠ 0 ∧
      ∀ j, y j * (rationalTupleDenominator r).eval₂ (RingHom.id ℂ) x =
        (rationalTupleNumerator r j).eval₂ (RingHom.id ℂ) x := by
  constructor
  · simp only [rationalTupleDenominator, MvPolynomial.eval₂_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => (hr j).1)
  · intro j
    have hq : rationalTupleDenominator r = (r j).2 * ∏ k ∈ Finset.univ.erase j, (r k).2 :=
      (Finset.mul_prod_erase Finset.univ (fun k => (r k).2) (Finset.mem_univ j)).symm
    rw [hq, rationalTupleNumerator, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul,
      ← mul_assoc, (hr j).2]

theorem complex_definable_graph_finite_common_denominator_cover {n m : ℕ}
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : (Set.univ : Set ℂ).Definable FirstOrder.Language.ring G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z) :
    ∃ s : Finset ((Fin m → MvPolynomial (Fin n) ℂ) × MvPolynomial (Fin n) ℂ),
      ∀ (x : Fin n → ℂ) (y : Fin m → ℂ), Sum.elim x y ∈ G →
        ∃ r ∈ s, r.2.eval₂ (RingHom.id ℂ) x ≠ 0 ∧
          ∀ j, y j * r.2.eval₂ (RingHom.id ℂ) x = (r.1 j).eval₂ (RingHom.id ℂ) x := by
  obtain ⟨s, hs⟩ := complex_definable_graph_finite_rational_cover G hG hu
  refine ⟨s.image (fun r => (rationalTupleNumerator r, rationalTupleDenominator r)), ?_⟩
  intro x y hxy
  obtain ⟨r, hr, hf⟩ := hs x y hxy
  exact ⟨_, Finset.mem_image.mpr ⟨r, hr, rfl⟩, rationalTuple_common_denominator r x y hf⟩

end DiamondIntegral.Section5
