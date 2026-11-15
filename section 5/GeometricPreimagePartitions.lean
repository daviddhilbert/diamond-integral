import «section 5».GeometricPreimageIndependence

/-! The inverse geometric value is additive for every finite actual
equivariant immersed partition. Common reduced pieces supply coordinate
presentations on each part, without an affine assumption on the parts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

theorem geometricPreimage_finite_partition (X : EquivariantVariety.Object) {ι : Type} [Fintype ι]
    (Y : ι → EquivariantVariety.Object) (p : ∀ i, Morphism (Y i) X) [∀ i, IsImmersion (p i).hom]
    (hpart : ∀ x : X.scheme, ∃! i, x ∈ Set.range (p i).hom) :
    geometricPreimage X = ∑ i, geometricPreimage (Y i) := by
  obtain ⟨c⟩ := diagonal_variety_presentation X
  letI := c.presentation.finite
  letI (j : c.presentation.index) := c.presentation.immersion j
  letI (j : c.presentation.index) := c.immersion j
  let P := fun j i => commonImmersionObject (c.presentation.inclusion j) (p i)
  let L := fun j i => commonImmersionLeft (c.presentation.inclusion j) (p i)
  let R := fun j i => commonImmersionRight (c.presentation.inclusion j) (p i)
  letI (j : c.presentation.index) (i : ι) : IsImmersion (L j i).hom := reducedPullbackFst_immersion _ _
  letI (j : c.presentation.index) (i : ι) : IsImmersion (R j i).hom := reducedPullbackSnd_immersion _ _
  have hLpart (j : c.presentation.index) (x : (c.presentation.piece j).scheme) :
      ∃! i, x ∈ Set.range (L j i).hom := by
    have hp := hpart ((c.presentation.inclusion j).hom x)
    have he (i : ι) : x ∈ Set.range (L j i).hom ↔
        (c.presentation.inclusion j).hom x ∈ Set.range (p i).hom := by
      change x ∈ Set.range (reducedPullbackFst (c.presentation.inclusion j).hom (p i).hom) ↔ _
      rw [reducedPullbackFst_range]
      rfl
    obtain ⟨i, hi, huniq⟩ := hp
    exact ⟨i, (he i).mpr hi, fun k hk => huniq k ((he k).mp hk)⟩
  have hRpart (i : ι) (y : (Y i).scheme) : ∃! j, y ∈ Set.range (R j i).hom := by
    have hp := (c.presentation.partition ((p i).hom y)).mp (Set.mem_univ _)
    have he (j : c.presentation.index) : y ∈ Set.range (R j i).hom ↔
        (p i).hom y ∈ Set.range (c.presentation.inclusion j).hom := by
      change y ∈ Set.range (reducedPullbackSnd (c.presentation.inclusion j).hom (p i).hom) ↔ _
      rw [reducedPullbackSnd_range]
      rfl
    obtain ⟨j, hj, huniq⟩ := hp
    exact ⟨j, (he j).mpr hj, fun k hk => huniq k ((he k).mp hk)⟩
  let d : ∀ i, DiagonalVarietyPresentation (Y i) := fun i => {
    presentation := {
      index := c.presentation.index
      finite := c.presentation.finite
      piece := fun j => P j i
      inclusion := fun j => R j i
      immersion := fun j => inferInstance
      contained := fun _ => Set.subset_univ _
      partition := fun y => ⟨fun _ => hRpart i y, fun _ => Set.mem_univ _⟩ }
    arity := c.arity
    weights := c.weights
    embedding := fun j => (c.embedding j).comp (L j i)
    immersion := fun j => inferInstance }
  have hc (j : c.presentation.index) :
      DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (c.weights j) (c.embedding j)) =
        ∑ i, DiagonalConstructible.objectClass
          (DiagonalConstructible.immersedObject (c.weights j) ((c.embedding j).comp (L j i))) :=
    immersedObject_finite_partition (c.weights j) (c.embedding j) (P j) (L j) (hLpart j)
  rw [geometricPreimage_eq_presentation X c]
  have hd (i : ι) : geometricPreimage (Y i) = ∑ j, DiagonalConstructible.objectClass
      (DiagonalConstructible.immersedObject (c.weights j) ((c.embedding j).comp (L j i))) :=
    geometricPreimage_eq_presentation (Y i) (d i)
  change (∑ j, DiagonalConstructible.objectClass
    (DiagonalConstructible.immersedObject (c.weights j) (c.embedding j))) = _
  simp_rw [hc, hd]
  exact Finset.sum_comm

theorem geometricPreimage_empty (X : EquivariantVariety.Object) (hX : IsEmpty X.scheme) :
    geometricPreimage X = 0 := by
  let Y := fun i : Fin 0 => (Fin.elim0 i : EquivariantVariety.Object)
  let p : ∀ i, Morphism (Y i) X := fun i => Fin.elim0 i
  letI (i : Fin 0) : IsImmersion (p i).hom := Fin.elim0 i
  have hh := geometricPreimage_finite_partition X Y p (fun x => (hX.false x).elim)
  simpa using hh

theorem geometricPreimage_iso {X Y : EquivariantVariety.Object} (f : EquivariantVariety.Iso X Y) :
    geometricPreimage X = geometricPreimage Y := by
  let P := fun _ : Fin 1 => X
  let p : ∀ i : Fin 1, Morphism (P i) Y := fun _ => f.toMorphism
  have hImm : ∀ i : Fin 1, IsImmersion (p i).hom := fun _ => inferInstanceAs (IsImmersion f.iso.hom)
  have hh := @geometricPreimage_finite_partition Y (Fin 1) inferInstance P p hImm (by
    intro y
    exact ⟨0, (Scheme.homeoOfIso f.iso).surjective y, fun _ _ => Subsingleton.elim _ _⟩)
  simpa using hh.symm

end DiamondIntegral.Section5
