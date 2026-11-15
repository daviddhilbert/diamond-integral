import «section 5».GeometricPreimageIndependence
import «section 5».VarietyProductMaps
import «section 5».ImmersedProductCoordinateClasses

/-! Multiplicativity of the inverse geometric value is proved for every
actual reduced equivariant product presentation, using its genuine finite
partition by products of the displayed diagonal pieces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

theorem geometricPreimage_product (P X Y : EquivariantVariety.Object) (hP : ProductPresentation P X Y) :
    geometricPreimage P = geometricPreimage X * geometricPreimage Y := by
  obtain ⟨c⟩ := diagonal_variety_presentation X
  obtain ⟨d⟩ := diagonal_variety_presentation Y
  letI := c.presentation.finite
  letI := d.presentation.finite
  letI (i : c.presentation.index) := c.presentation.immersion i
  letI (j : d.presentation.index) := d.presentation.immersion j
  letI (i : c.presentation.index) := c.immersion i
  letI (j : d.presentation.index) := d.immersion j
  let Q := fun i j => affineImmersedProductObject (c.weights i) (d.weights j) (c.embedding i) (d.embedding j)
  let e := fun i j => affineImmersedProductPresentation (c.weights i) (d.weights j) (c.embedding i) (d.embedding j)
  let p := fun i j => hP.map (e i j) (c.presentation.inclusion i) (d.presentation.inclusion j)
  have hpart (z : P.scheme) : ∃! a : c.presentation.index × d.presentation.index,
      z ∈ Set.range (p a.1 a.2).hom := by
    have he (a : c.presentation.index × d.presentation.index) : z ∈ Set.range (p a.1 a.2).hom ↔
        hP.fst.hom z ∈ Set.range (c.presentation.inclusion a.1).hom ∧
          hP.snd.hom z ∈ Set.range (d.presentation.inclusion a.2).hom := by
      rw [ProductPresentation.map_range]
      rfl
    obtain ⟨i, hi, hui⟩ := (c.presentation.partition (hP.fst.hom z)).mp (Set.mem_univ _)
    obtain ⟨j, hj, huj⟩ := (d.presentation.partition (hP.snd.hom z)).mp (Set.mem_univ _)
    refine ⟨(i,j), (he (i,j)).mpr ⟨hi,hj⟩, ?_⟩
    intro a ha
    have hh := (he a).mp ha
    exact Prod.ext (hui a.1 hh.1) (huj a.2 hh.2)
  let cP : DiagonalVarietyPresentation P := {
    presentation := {
      index := c.presentation.index × d.presentation.index
      finite := inferInstance
      piece := fun a => Q a.1 a.2
      inclusion := fun a => p a.1 a.2
      immersion := fun a => inferInstance
      contained := fun _ => Set.subset_univ _
      partition := fun z => ⟨fun _ => hpart z, fun _ => Set.mem_univ _⟩ }
    arity := fun a => c.arity a.1 + d.arity a.2
    weights := fun a => Fin.append (c.weights a.1) (d.weights a.2)
    embedding := fun a => affineImmersedProductInclusion (c.weights a.1) (d.weights a.2) (c.embedding a.1) (d.embedding a.2)
    immersion := fun a => inferInstance }
  rw [geometricPreimage_eq_presentation P cP, geometricPreimage_eq_presentation X c,
    geometricPreimage_eq_presentation Y d]
  change (∑ a : c.presentation.index × d.presentation.index,
    DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (Fin.append (c.weights a.1) (d.weights a.2))
      (affineImmersedProductInclusion (c.weights a.1) (d.weights a.2) (c.embedding a.1) (d.embedding a.2)))) =
      (∑ i, DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (c.weights i) (c.embedding i))) *
        (∑ j, DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (d.weights j) (d.embedding j)))
  simp_rw [immersedProduct_coordinate_class]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

end DiamondIntegral.Section5
