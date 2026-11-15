import «section 5».ConstructibleSpectrumObjects
import «section 5».DiagonalFinitePartitions

/-! A finite immersed presentation of the spectrum extension of an
original diagonal tuple set recovers its original diagonal class exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

theorem diagonalObject_presentation_partition (X : DiagonalConstructible.Object)
    (c : ImmersedPresentation (rationalAffineObject X.weights) (complexSpectrumExtension X.domain X.definable)) :
    letI := c.finite
    letI (i : c.index) := c.immersion i
    DiagonalConstructible.objectClass X = ∑ i, DiagonalConstructible.objectClass
      (DiagonalConstructible.immersedObject X.weights (c.inclusion i)) := by
  letI := c.finite
  letI (i : c.index) := c.immersion i
  let T := fun i => DiagonalConstructible.immersedObject X.weights (c.inclusion i)
  have hpoint (x : Fin X.arity → ℂ) : x ∈ X.domain ↔ ∃! i, x ∈ (T i).domain :=
    (complexSpectrumExtension_point X.domain X.definable x).symm.trans (c.partition (complexTupleSpectrumPoint x))
  have hsub (i : c.index) (x : Fin X.arity → ℂ) (hx : x ∈ (T i).domain) : x ∈ X.domain :=
    (complexSpectrumExtension_point X.domain X.definable x).mp (c.contained i hx)
  have hdisj : Pairwise (fun i j => Disjoint (T i).domain (T j).domain) := by
    intro i j hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨k, hk, huniq⟩ := (hpoint x).mp (hsub i x hxi)
    exact hne ((huniq i hxi).trans (huniq j hxj).symm)
  have hcover (x : Fin X.arity → ℂ) : x ∈ X.domain ↔ ∃ i, x ∈ (T i).domain := by
    constructor
    · intro hx
      exact ((hpoint x).mp hx).exists
    · rintro ⟨i, hi⟩
      exact hsub i x hi
  change DiagonalConstructible.setClass X.weights X.domain X.definable X.invariant =
    ∑ i, DiagonalConstructible.setClass X.weights (T i).domain (T i).definable (T i).invariant
  exact DiagonalConstructible.finite_partition_class X.weights X.domain X.definable X.invariant
    (fun i => (T i).domain) (fun i => (T i).definable) (fun i => (T i).invariant) hdisj hcover

end DiamondIntegral.Section5
