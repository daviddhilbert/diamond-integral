import «section 5».DiagonalGeometricValues
import «section 5».DiagonalGraphPresentations
import «section 5».ComplexEquivGraphs

/-! Constructible equivariant bijections preserve the actual geometric
class. The proof constructs algebraic common pieces and derives all
partition identities from the geometric ring's closed/open relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology PuiseuxOriginal EquivariantVariety
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def changeRationalPresentationWeights {n : ℕ} {q r : Fin n → ℚ}
    {D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))}
    (c : ImmersedPresentation (rationalAffineObject q) D) (he : q = r) :
    ImmersedPresentation (rationalAffineObject r) D := he ▸ c

theorem changeRationalPresentationWeights_value {n : ℕ} {q r : Fin n → ℚ}
    {D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))}
    (c : ImmersedPresentation (rationalAffineObject q) D) (he : q = r) :
    (changeRationalPresentationWeights c he).value = c.value := by subst r; rfl

theorem diagonalGeometricValue_of_presentation (X : DiagonalConstructible.Object)
    {q : Fin X.arity → ℚ} (hq : X.weights = q)
    (c : ImmersedPresentation (rationalAffineObject q) (complexSpectrumExtension X.domain X.definable)) :
    DiagonalConstructible.geometricValue X = c.value :=
  (constructibleClass_eq_presentation _ _ _ _ (changeRationalPresentationWeights c hq.symm)).trans
    (changeRationalPresentationWeights_value c hq.symm)

theorem diagonalGeometricValue_bijection_at_level
    (X Y : DiagonalConstructible.Object) (f : DiagonalConstructible.Iso X Y)
    (N : ℕ+) (a : Fin X.arity → ℤ) (b : Fin Y.arity → ℤ)
    (hqX : X.weights = fun i => (a i : ℚ) / (N : ℕ))
    (hqY : Y.weights = fun j => (b j : ℚ) / (N : ℕ))
    (hG : FiniteInvariant N (Fin.append a b) (framedEquivGraph X.domain Y.domain f.equiv)) :
    DiagonalConstructible.geometricValue X = DiagonalConstructible.geometricValue Y := by
  obtain ⟨d⟩ := complex_equivariant_bijection_decomposition (complexEquivGraph f.equiv)
    (complexEquivGraph_definable f.equiv f.graph_definable)
    (complexEquivGraph_forward_unique f.equiv) (complexEquivGraph_inverse_unique f.equiv)
    N (fun i => -a i) (fun j => -b j) (complexEquivGraph_finite_invariant f.equiv N a b hG)
  have hsource : d.sourceLocus = complexSpectrumExtension X.domain X.definable := by
    apply constructible_eq_of_complex_points _ _ d.sourceRationalPresentation.constructible
      (complexSpectrumExtension_constructible _ _)
    intro φ
    rw [d.sourceLocus_complex, complexEquivGraph_source,
      ← complexTupleSpectrumPoint_algHom φ, complexSpectrumExtension_point]
  have htarget : d.targetLocus = complexSpectrumExtension Y.domain Y.definable := by
    apply constructible_eq_of_complex_points _ _ d.targetRationalPresentation.constructible
      (complexSpectrumExtension_constructible _ _)
    intro φ
    rw [d.targetLocus_complex, complexEquivGraph_target,
      ← complexTupleSpectrumPoint_algHom φ, complexSpectrumExtension_point]
  have hX : DiagonalConstructible.geometricValue X = d.sourceRationalPresentation.value :=
    (diagonalGeometricValue_of_presentation X hqX (d.sourceRationalPresentation.changeLocus hsource)).trans
      (d.sourceRationalPresentation.changeLocus_value hsource)
  have hY : DiagonalConstructible.geometricValue Y = d.targetRationalPresentation.value :=
    (diagonalGeometricValue_of_presentation Y hqY (d.targetRationalPresentation.changeLocus htarget)).trans
      (d.targetRationalPresentation.changeLocus_value htarget)
  exact hX.trans (d.rationalPresentation_values_eq.trans hY.symm)

theorem PuiseuxOriginal.DiagonalConstructible.geometricValue_iso
    {X Y : DiagonalConstructible.Object} (f : DiagonalConstructible.Iso X Y) :
    geometricValue X = geometricValue Y := by
  obtain ⟨N, w, hw⟩ := rational_tuple_common_level (X.arity + Y.arity) (Fin.append X.weights Y.weights)
  let a := fun i => w (Fin.castAdd Y.arity i)
  let b := fun j => w (Fin.natAdd X.arity j)
  have hqX : X.weights = fun i => (a i : ℚ) / (N : ℕ) := by
    funext i
    simpa only [Fin.append_left] using hw (Fin.castAdd Y.arity i)
  have hqY : Y.weights = fun j => (b j : ℚ) / (N : ℕ) := by
    funext j
    simpa only [Fin.append_right] using hw (Fin.natAdd X.arity j)
  have hF : FiniteInvariant N w (framedEquivGraph X.domain Y.domain f.equiv) :=
    (rationalInvariant_iff_finite N w _).mp (by
      rw [← funext hw]
      exact f.graph_invariant)
  apply diagonalGeometricValue_bijection_at_level X Y f N a b hqX hqY
  have he : Fin.append a b = w := Fin.append_castAdd_natAdd (f := w)
  simpa only [he] using hF

end DiamondIntegral.Section5
