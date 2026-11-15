import «section 5».GeometricComparisonSurjectivity
import «section 5».ImmersionCoordinateIsomorphisms
import «section 5».ImmersedObjectPartitions

/-! Actual common reduced pieces make the diagonal preimage of a
geometric variety independent of its finite immersed presentation and
of every chosen rational affine coordinate embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

theorem diagonal_preimage_independent {X : EquivariantVariety.Object}
    (c d : DiagonalVarietyPresentation X) : c.preimage = d.preimage := by
  letI := c.presentation.finite
  letI := d.presentation.finite
  letI (i : c.presentation.index) := c.presentation.immersion i
  letI (j : d.presentation.index) := d.presentation.immersion j
  letI (i : c.presentation.index) := c.immersion i
  letI (j : d.presentation.index) := d.immersion j
  let P := fun i j => commonImmersionObject (c.presentation.inclusion i) (d.presentation.inclusion j)
  let L := fun i j => commonImmersionLeft (c.presentation.inclusion i) (d.presentation.inclusion j)
  let R := fun i j => commonImmersionRight (c.presentation.inclusion i) (d.presentation.inclusion j)
  letI (i : c.presentation.index) (j : d.presentation.index) : IsImmersion (L i j).hom :=
    reducedPullbackFst_immersion _ _
  letI (i : c.presentation.index) (j : d.presentation.index) : IsImmersion (R i j).hom :=
    reducedPullbackSnd_immersion _ _
  have hc (i : c.presentation.index) :
      DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (c.weights i) (c.embedding i)) =
        ∑ j, DiagonalConstructible.objectClass
          (DiagonalConstructible.immersedObject (c.weights i) ((c.embedding i).comp (L i j))) := by
    apply immersedObject_finite_partition (c.weights i) (c.embedding i) (P i) (L i)
    intro x
    have hp := (d.presentation.partition ((c.presentation.inclusion i).hom x)).mp (Set.mem_univ _)
    have he (j : d.presentation.index) : x ∈ Set.range (L i j).hom ↔
        (c.presentation.inclusion i).hom x ∈ Set.range (d.presentation.inclusion j).hom := by
      change x ∈ Set.range (reducedPullbackFst (c.presentation.inclusion i).hom
        (d.presentation.inclusion j).hom) ↔ _
      rw [reducedPullbackFst_range]
      rfl
    obtain ⟨j, hj, huniq⟩ := hp
    exact ⟨j, (he j).mpr hj, fun k hk => huniq k ((he k).mp hk)⟩
  have hd (j : d.presentation.index) :
      DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (d.weights j) (d.embedding j)) =
        ∑ i, DiagonalConstructible.objectClass
          (DiagonalConstructible.immersedObject (d.weights j) ((d.embedding j).comp (R i j))) := by
    apply immersedObject_finite_partition (d.weights j) (d.embedding j) (fun i => P i j) (fun i => R i j)
    intro y
    have hp := (c.presentation.partition ((d.presentation.inclusion j).hom y)).mp (Set.mem_univ _)
    have he (i : c.presentation.index) : y ∈ Set.range (R i j).hom ↔
        (d.presentation.inclusion j).hom y ∈ Set.range (c.presentation.inclusion i).hom := by
      change y ∈ Set.range (reducedPullbackSnd (c.presentation.inclusion i).hom
        (d.presentation.inclusion j).hom) ↔ _
      rw [reducedPullbackSnd_range]
      rfl
    obtain ⟨i, hi, huniq⟩ := hp
    exact ⟨i, (he i).mpr hi, fun k hk => huniq k ((he k).mp hk)⟩
  change (∑ i, DiagonalConstructible.objectClass
    (DiagonalConstructible.immersedObject (c.weights i) (c.embedding i))) =
      ∑ j, DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (d.weights j) (d.embedding j))
  simp_rw [hc, hd]
  calc
    _ = ∑ i, ∑ j, DiagonalConstructible.objectClass
        (DiagonalConstructible.immersedObject (d.weights j) ((d.embedding j).comp (R i j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact immersedObject_class_eq (c.weights i) (d.weights j)
        ((c.embedding i).comp (L i j)) ((d.embedding j).comp (R i j))
    _ = _ := Finset.sum_comm

def geometricPreimage (X : EquivariantVariety.Object) : DiagonalConstructible.Ring :=
  (Classical.choice (diagonal_variety_presentation X)).preimage

theorem geometricPreimage_eq_presentation (X : EquivariantVariety.Object) (c : DiagonalVarietyPresentation X) :
    geometricPreimage X = c.preimage := diagonal_preimage_independent _ c

theorem toVarietyRing_geometricPreimage (X : EquivariantVariety.Object) :
    DiagonalConstructible.toVarietyRing (geometricPreimage X) = objectClass X :=
  (Classical.choice (diagonal_variety_presentation X)).preimage_value

def diagonalSingletonPresentation {n : ℕ} (q : Fin n → ℚ) {Y : EquivariantVariety.Object}
    (f : Morphism Y (rationalAffineObject q)) [IsImmersion f.hom] : DiagonalVarietyPresentation Y where
  presentation := {
    index := PUnit
    finite := inferInstance
    piece := fun _ => Y
    inclusion := fun _ => Morphism.id Y
    immersion := fun _ => inferInstanceAs (IsImmersion (𝟙 Y.scheme))
    contained := fun _ => Set.subset_univ _
    partition := fun y => by
      constructor
      · intro _
        exact ⟨PUnit.unit, ⟨y, rfl⟩, fun _ _ => Subsingleton.elim _ _⟩
      · intro _
        trivial }
  arity := fun _ => n
  weights := fun _ => q
  embedding := fun _ => f
  immersion := fun _ => inferInstance

theorem geometricPreimage_of_immersion {n : ℕ} (q : Fin n → ℚ) {Y : EquivariantVariety.Object}
    (f : Morphism Y (rationalAffineObject q)) [IsImmersion f.hom] :
    geometricPreimage Y = DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject q f) := by
  rw [geometricPreimage_eq_presentation Y (diagonalSingletonPresentation q f)]
  simp [DiagonalVarietyPresentation.preimage, diagonalSingletonPresentation]

end DiamondIntegral.Section5
