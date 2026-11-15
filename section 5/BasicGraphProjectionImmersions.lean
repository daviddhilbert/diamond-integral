import «section 5».GraphProjectionImmersions
import «section 5».RationalSpectrumGraphs
import «section 5».BasicConstructibleSchemes
import «section 5».ComplexPointUnits

/-! The coordinate projection of an actual basic rational graph piece
is an immersion. Nonvanishing and polynomial identities are derived
from the prescribed graph locus, using reduced complex-point detection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] basicConstructibleCoordinate_reduced basicConstructibleCoordinate_finiteType
variable {n m : ℕ}
variable (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))

def basicGraphLeft : MvPolynomial (Fin n) ℂ →ₐ[ℂ] BasicConstructibleCoordinateRing D :=
  (basicConstructibleCoordinateMap D).comp (MvPolynomial.rename Sum.inl)

def basicGraphRight : MvPolynomial (Fin m) ℂ →ₐ[ℂ] BasicConstructibleCoordinateRing D :=
  (basicConstructibleCoordinateMap D).comp (MvPolynomial.rename Sum.inr)

theorem basicGraphMap_eq : polynomialGraphMap (basicGraphLeft D) (basicGraphRight D) =
    basicConstructibleCoordinateMap D := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [polynomialGraphMap, basicGraphLeft, basicGraphRight]

theorem basicGraphLeft_rational_relations (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ)
    (hD : D.toSet ⊆ (rationalSpectrumGraphData p q).toSet) :
    IsUnit (basicGraphLeft D q) ∧ ∀ j,
      basicGraphRight D (MvPolynomial.X j) * basicGraphLeft D q = basicGraphLeft D (p j) := by
  constructor
  · apply (complex_points_isUnit _).mpr
    intro φ
    have h := (hD (basicConstructiblePoint_mem D φ)).2
    have hn : (φ.comp (basicConstructibleCoordinateMap D))
        ((rationalSpectrumGraphData p q).f) ≠ 0 := by
      intro hz
      apply h
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hz
    exact hn
  · intro j
    refine complex_points_separate (A := BasicConstructibleCoordinateRing D)
      (basicGraphRight D (MvPolynomial.X j) * basicGraphLeft D q) (basicGraphLeft D (p j)) ?_
    intro φ
    have h : (φ.comp (basicConstructibleCoordinateMap D))
        ((rationalSpectrumGraphData p q).g j) = 0 :=
      (hD (basicConstructiblePoint_mem D φ)).1 (Set.mem_range_self j)
    have h0 : φ (basicGraphRight D (MvPolynomial.X j)) * φ (basicGraphLeft D q) -
        φ (basicGraphLeft D (p j)) = 0 := by
      simpa only [rationalSpectrumGraphData, basicGraphLeft, basicGraphRight, AlgHom.comp_apply, MvPolynomial.rename_X,
        map_sub, map_mul] using h
    simpa only [map_mul] using sub_eq_zero.mp h0

theorem basicGraphLeft_isImmersion (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ)
    (hD : D.toSet ⊆ (rationalSpectrumGraphData p q).toSet) :
    IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphLeft D).toRingHom)) := by
  obtain ⟨hq, hr⟩ := basicGraphLeft_rational_relations D p q hD
  apply rational_graph_projection_isImmersion (basicGraphLeft D) (basicGraphRight D) p q hq hr
  rw [basicGraphMap_eq]
  exact basicConstructibleInclusion_isImmersion D

end DiamondIntegral.Section5
