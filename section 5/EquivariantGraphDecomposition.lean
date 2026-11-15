import «section 5».InvariantBranchStratifications
import «section 5».InvariantGraphProjectionImages
import «section 5».GraphBranchEquivariance
import «section 5».EquivariantCommonPieces

/-! An actual finite diagonal-equivariant complex definable bijection
has certified invariant regular source and target strata. Their common
pieces are the reduced fibre products with the checked immersion
projections, actual actions and unique point partitions proved earlier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory FirstOrder FirstOrder.Language PuiseuxOriginal
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] basicConstructibleCoordinate_reduced basicConstructibleCoordinate_finiteType

structure EquivariantGraphDecomposition {n m : ℕ} (N : ℕ+)
    (w : Fin n → ℤ) (v : Fin m → ℤ) (G : Set (Fin n ⊕ Fin m → ℂ)) where
  index : Type
  finite : Fintype index
  data : index → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ)
  left_immersion : ∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphLeft (data j)).toRingHom))
  right_immersion : ∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphRight (data j)).toRingHom))
  graph_contained : ∀ j x, complexTupleSpectrumPoint x ∈ (data j).toSet → x ∈ G
  graph_partition : ∀ x, x ∈ G ↔ ∃! j, complexTupleSpectrumPoint x ∈ (data j).toSet
  forward_unique : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
    Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z
  inverse_unique : ∀ (y : Fin m → ℂ) (x z : Fin n → ℂ),
    Sum.elim x y ∈ G → Sum.elim z y ∈ G → x = z
  source : AffineBranchStratification (fun j => BasicConstructibleCoordinateRing (data j))
    (fun j => basicGraphLeft (data j)) (fun j => basicGraphRight (data j))
  target : AffineBranchStratification (fun j => BasicConstructibleCoordinateRing (data j))
    (fun j => basicGraphRight (data j)) (fun j => basicGraphLeft (data j))
  source_action : ∀ i, rootsOfUnity (N : ℕ) ℂ →* Aut (source.scheme i)
  target_action : ∀ i, rootsOfUnity (N : ℕ) ℂ →* Aut (target.scheme i)
  source_input_equivariant : ∀ i h,
    (source_action i h).asIso.hom ≫ source.base i =
      source.base i ≫ (algebraSpecAction (finiteDiagonalAlgebraAction N w) h).asIso.hom
  source_output_equivariant : ∀ i h,
    (source_action i h).asIso.hom ≫ source.output i =
      source.output i ≫ (algebraSpecAction (finiteDiagonalAlgebraAction N v) h).asIso.hom
  target_input_equivariant : ∀ i h,
    (target_action i h).asIso.hom ≫ target.base i =
      target.base i ≫ (algebraSpecAction (finiteDiagonalAlgebraAction N v) h).asIso.hom
  target_output_equivariant : ∀ i h,
    (target_action i h).asIso.hom ≫ target.output i =
      target.output i ≫ (algebraSpecAction (finiteDiagonalAlgebraAction N w) h).asIso.hom

theorem complex_equivariant_bijection_decomposition {n m : ℕ}
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z)
    (hv : ∀ (y : Fin m → ℂ) (x z : Fin n → ℂ),
      Sum.elim x y ∈ G → Sum.elim z y ∈ G → x = z)
    (N : ℕ+) (w : Fin n → ℤ) (v : Fin m → ℤ)
    (hInv : ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) x y,
      Sum.elim (weightedAction w ζ.val x) (weightedAction v ζ.val y) ∈ G ↔ Sum.elim x y ∈ G) :
    Nonempty (EquivariantGraphDecomposition N w v G) := by
  letI : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  letI : Fintype (rootsOfUnity (N : ℕ) ℂ) := Fintype.ofFinite _
  obtain ⟨J, hJ, D, hImm, _, hD, hpart⟩ :=
    complex_constructible_bijection_algebraic_pieces G hG hu hv
  letI := hJ
  letI (j : J) := (hImm j).1
  letI (j : J) := (hImm j).2
  have hcover (x) : x ∈ G ↔ ∃ j, complexTupleSpectrumPoint x ∈ (D j).toSet := by
    constructor
    · intro hx
      exact ((hpart x).mp hx).exists
    · rintro ⟨j, hj⟩
      exact hD j x hj
  have hc := graph_branches_complex_compatible D G hD hu
  have hd := graph_branches_inverse_complex_compatible D G hD hv
  have ht (ζ : rootsOfUnity (N : ℕ) ℂ)
      (x : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (y : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ℂ)
      (hxy : Sum.elim (fun i => x (MvPolynomial.X i)) (fun j => y (MvPolynomial.X j)) ∈ G) :
      Sum.elim (fun i => (x.comp (polynomialDiagonalAction w (ζ⁻¹).val)) (MvPolynomial.X i))
        (fun j => (y.comp (polynomialDiagonalAction v (ζ⁻¹).val)) (MvPolynomial.X j)) ∈ G := by
    rw [polynomialDiagonalAction_point, polynomialDiagonalAction_point]
    exact (hInv ζ⁻¹ _ _).mpr hxy
  obtain ⟨c, σ, hσ, hF⟩ := finite_equivariant_branch_stratification hc
    (finiteDiagonalAlgebraAction N w) (finiteDiagonalAlgebraAction N v)
    (basicGraphLeft_image_invariant D G hcover N w v hInv)
    (fun ζ => graph_branches_transformed_complex_compatible D G hD hu _ _ (ht ζ))
  obtain ⟨d, τ, hτ, hH⟩ := finite_equivariant_branch_stratification hd
    (finiteDiagonalAlgebraAction N v) (finiteDiagonalAlgebraAction N w)
    (basicGraphRight_image_invariant D G hcover N w v hInv)
    (fun ζ => graph_branches_inverse_transformed_complex_compatible D G hD hv _ _ (ht ζ))
  refine ⟨?_⟩
  exact {
    index := J, finite := hJ, data := D,
    left_immersion := fun j => (hImm j).1, right_immersion := fun j => (hImm j).2,
    graph_contained := hD, graph_partition := hpart, forward_unique := hu, inverse_unique := hv,
    source := c, target := d, source_action := σ, target_action := τ,
    source_input_equivariant := hσ, source_output_equivariant := hF,
    target_input_equivariant := hτ, target_output_equivariant := hH }

end DiamondIntegral.Section5
