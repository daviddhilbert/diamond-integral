import «section 5».AffineVarietyEmbeddings
import «section 5».FiniteAffineVarietyPresentations
import «section 5».ConstructibleSpectrumObjects

/-! Every good finite-action geometric variety is represented by an actual
finite sum of rational diagonal constructible objects. Hence the forward
comparison is surjective on the geometric ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

structure DiagonalVarietyPresentation (X : EquivariantVariety.Object) where
  presentation : ImmersedPresentation X Set.univ
  arity : presentation.index → ℕ
  weights : ∀ i, Fin (arity i) → ℚ
  embedding : ∀ i, Morphism (presentation.piece i) (rationalAffineObject (weights i))
  immersion : ∀ i, IsImmersion (embedding i).hom

theorem diagonal_variety_presentation (X : EquivariantVariety.Object) : Nonempty (DiagonalVarietyPresentation X) := by
  obtain ⟨c⟩ := finite_affine_variety_presentation X
  letI (i : c.presentation.index) := c.affine i
  choose n q f hf using (fun i => affine_variety_diagonal_closed_embedding (c.presentation.piece i))
  letI (i : c.presentation.index) := hf i
  exact ⟨⟨c.presentation, n, q, f, fun i => inferInstance⟩⟩

def DiagonalVarietyPresentation.preimage {X : EquivariantVariety.Object} (c : DiagonalVarietyPresentation X) :
    DiagonalConstructible.Ring := by
  letI := c.presentation.finite
  letI (i : c.presentation.index) := c.immersion i
  exact ∑ i, DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (c.weights i) (c.embedding i))

theorem DiagonalVarietyPresentation.preimage_value {X : EquivariantVariety.Object}
    (c : DiagonalVarietyPresentation X) :
    DiagonalConstructible.toVarietyRing c.preimage = objectClass X := by
  letI := c.presentation.finite
  letI (i : c.presentation.index) := c.immersion i
  letI (i : c.presentation.index) := c.presentation.immersion i
  change DiagonalConstructible.toVarietyRing (∑ i,
    DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (c.weights i) (c.embedding i))) = _
  simp only [map_sum, DiagonalConstructible.toVarietyRing_objectClass, immersedObject_geometricValue]
  exact (objectClass_finite_immersed_partition X c.presentation.piece c.presentation.inclusion
    (fun x => (c.presentation.partition x).mp (Set.mem_univ x))).symm

theorem geometric_object_class_has_preimage (X : EquivariantVariety.Object) :
    ∃ x : DiagonalConstructible.Ring, DiagonalConstructible.toVarietyRing x = objectClass X := by
  obtain ⟨c⟩ := diagonal_variety_presentation X
  exact ⟨c.preimage, c.preimage_value⟩

theorem PuiseuxOriginal.DiagonalConstructible.toVarietyRing_surjective :
    Function.Surjective DiagonalConstructible.toVarietyRing := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine FreeCommRing.induction_on r ?_ ?_ ?_ ?_
  · exact ⟨-1, by simp⟩
  · intro X
    exact geometric_object_class_has_preimage X
  · intro x y hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]⟩
  · intro x y hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by simp only [map_mul, ha, hb]⟩

end DiamondIntegral.Section5
