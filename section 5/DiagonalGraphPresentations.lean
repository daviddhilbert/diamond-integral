import «section 5».GraphDecompositionClasses
import «section 5».ImmersedPresentationLoci
import «section 5».RationalAffineVarieties

/-! Equivariant graph decompositions give actual immersed presentations
in the intrinsic rational-weight affine spaces, with the correct complex
point action and exact projected constructible loci. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety Topology
attribute [local instance] basicConstructibleCoordinate_finiteType
variable {n m : ℕ} {N : ℕ+} {w : Fin n → ℤ} {v : Fin m → ℤ}
variable {G : Set (Fin n ⊕ Fin m → ℂ)}

def EquivariantGraphDecomposition.sourceLocus (d : EquivariantGraphDecomposition N w v G) :
    Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ)) :=
  ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (d.data j)).toRingHom))

def EquivariantGraphDecomposition.targetLocus (d : EquivariantGraphDecomposition N w v G) :
    Set (PrimeSpectrum (MvPolynomial (Fin m) ℂ)) :=
  ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphRight (d.data j)).toRingHom))

theorem EquivariantGraphDecomposition.graph_cover (d : EquivariantGraphDecomposition N w v G)
    (z : Fin n ⊕ Fin m → ℂ) :
    z ∈ G ↔ ∃ j, complexTupleSpectrumPoint z ∈ (d.data j).toSet := by
  constructor
  · intro hz
    exact ((d.graph_partition z).mp hz).exists
  · rintro ⟨j, hj⟩
    exact d.graph_contained j z hj

theorem EquivariantGraphDecomposition.sourceLocus_complex (d : EquivariantGraphDecomposition N w v G)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :
    complexAlgebraPoint φ ∈ d.sourceLocus ↔
      ∃ y : Fin m → ℂ, Sum.elim (fun i => φ (MvPolynomial.X i)) y ∈ G :=
  basicGraphLeft_complex_image_iff d.data G d.graph_cover φ

theorem EquivariantGraphDecomposition.targetLocus_complex (d : EquivariantGraphDecomposition N w v G)
    (φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ℂ) :
    complexAlgebraPoint φ ∈ d.targetLocus ↔
      ∃ x : Fin n → ℂ, Sum.elim x (fun i => φ (MvPolynomial.X i)) ∈ G :=
  basicGraphRight_complex_image_iff d.data G d.graph_cover φ

variable {a : Fin n → ℤ} {b : Fin m → ℤ}

def EquivariantGraphDecomposition.sourceRationalInclusion
    (d : EquivariantGraphDecomposition N (fun i => -a i) (fun j => -b j) G) (i : d.source.index) :
    Morphism (d.sourceVariety i) (rationalAffineObject (fun i => (a i : ℚ) / (N : ℕ))) where
  hom := d.source.base i
  overC := rfl
  equivariant η := by
    change (d.source_action i (finiteRootProjection N η)).asIso.hom ≫ d.source.base i =
      d.source.base i ≫ ((rationalAffineObject (fun i => (a i : ℚ) / (N : ℕ))).action η).asIso.hom
    rw [rationalAffineObject_common_level]
    exact d.source_input_equivariant i (finiteRootProjection N η)

def EquivariantGraphDecomposition.targetRationalInclusion
    (d : EquivariantGraphDecomposition N (fun i => -a i) (fun j => -b j) G) (j : d.target.index) :
    Morphism (d.targetVariety j) (rationalAffineObject (fun j => (b j : ℚ) / (N : ℕ))) where
  hom := d.target.base j
  overC := rfl
  equivariant η := by
    change (d.target_action j (finiteRootProjection N η)).asIso.hom ≫ d.target.base j =
      d.target.base j ≫ ((rationalAffineObject (fun j => (b j : ℚ) / (N : ℕ))).action η).asIso.hom
    rw [rationalAffineObject_common_level]
    exact d.target_input_equivariant j (finiteRootProjection N η)

def EquivariantGraphDecomposition.sourceRationalPresentation
    (d : EquivariantGraphDecomposition N (fun i => -a i) (fun j => -b j) G) :
    ImmersedPresentation (rationalAffineObject (fun i => (a i : ℚ) / (N : ℕ))) d.sourceLocus where
  index := d.source.index
  finite := d.source.finite
  piece := d.sourceVariety
  inclusion := d.sourceRationalInclusion
  immersion := d.source.immersion
  contained i := by
    rintro _ ⟨x, rfl⟩
    exact affineBranchRelation_mem_left _ _ _ ((d.source.certificate i).point x)
  partition := d.source.partition

def EquivariantGraphDecomposition.targetRationalPresentation
    (d : EquivariantGraphDecomposition N (fun i => -a i) (fun j => -b j) G) :
    ImmersedPresentation (rationalAffineObject (fun j => (b j : ℚ) / (N : ℕ))) d.targetLocus where
  index := d.target.index
  finite := d.target.finite
  piece := d.targetVariety
  inclusion := d.targetRationalInclusion
  immersion := d.target.immersion
  contained j := by
    rintro _ ⟨x, rfl⟩
    exact affineBranchRelation_mem_left _ _ _ ((d.target.certificate j).point x)
  partition := d.target.partition

theorem EquivariantGraphDecomposition.rationalPresentation_values_eq
    (d : EquivariantGraphDecomposition N (fun i => -a i) (fun j => -b j) G) :
    d.sourceRationalPresentation.value = d.targetRationalPresentation.value :=
  d.geometric_classes_eq

end DiamondIntegral.Section5
