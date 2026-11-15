import «section 5».GraphBranchCompatibility
import «section 5».ImmersionBranchGluing
import «section 5».LocallyClosedAffineSchemes

/-! A complex definable graph gives an actual regular map on every
locally closed input stratum on which its affine branch images are open.
The morphism and its uniqueness are proved by reduced-scheme gluing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology
attribute [local instance] basicConstructibleCoordinate_reduced basicConstructibleCoordinate_finiteType
attribute [local instance] locallyClosedAffineScheme_isReduced

theorem immersion_preimage_isClopen {Y X : Scheme} (f : X ⟶ Y)
    (S D : Set Y) (hS : Set.range f ⊆ S)
    (hD : IsClopen {x : S | x.val ∈ D}) : IsClopen (f ⁻¹' D) := by
  let g : X → S := fun x => ⟨f x, hS ⟨x, rfl⟩⟩
  have hg : Continuous g := f.continuous.subtype_mk _
  exact hD.preimage hg

theorem complex_graph_stratum_regular_map {n m : ℕ} {J : Type}
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    [hleft : ∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))]
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hD : ∀ j v, complexTupleSpectrumPoint v ∈ (D j).toSet → v ∈ G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z)
    (S : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))) (hS : IsLocallyClosed S)
    (hclopen : ∀ j, IsClopen {x : S | x.val ∈
      Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))})
    (hcover : S ⊆ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))) :
    let A := fun j => BasicConstructibleCoordinateRing (D j)
    let base := locallyClosedAffineInclusion S hS
    ∃ (ho : ∀ j, IsOpen {x : locallyClosedAffineScheme S hS |
        base x ∈ Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))}),
    ∃! F : locallyClosedAffineScheme S hS ⟶ Spec (.of (MvPolynomial (Fin m) ℂ)),
      ∀ j, (immersionBranchOpen A (fun j => basicGraphLeft (D j)) base ho j).ι ≫ F =
        immersionBranchLift A (fun j => basicGraphLeft (D j)) base ho j ≫
          Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom) := by
  letI (j : J) := basicConstructibleCoordinate_reduced (D j)
  letI (j : J) := basicConstructibleCoordinate_finiteType (D j)
  letI (j : J) := hleft j
  letI := locallyClosedAffineScheme_isReduced S hS
  let A := fun j => BasicConstructibleCoordinateRing (D j)
  let f := fun j => basicGraphLeft (D j)
  let a := fun j => basicGraphRight (D j)
  let base := locallyClosedAffineInclusion S hS
  have ho (j : J) : IsOpen {x : locallyClosedAffineScheme S hS |
      base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))} := by
    exact (immersion_preimage_isClopen base S _
      (by rw [locallyClosedAffineInclusion_range]) (hclopen j)).isOpen
  have hc (x : locallyClosedAffineScheme S hS) :
      ∃ j, base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom)) := by
    apply Set.mem_iUnion.mp
    exact hcover ((locallyClosedAffineInclusion_range S hS).subset ⟨x, rfl⟩)
  exact ⟨ho, glue_immersion_branches A f base a
    (graph_branches_complex_compatible D G hD hu) ho hc⟩

end DiamondIntegral.Section5
