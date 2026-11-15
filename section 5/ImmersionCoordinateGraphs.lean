import «section 5».RationalAffinePairMaps
import «section 5».ComplexCoordinateImages

/-! The complete coordinate graph of two equivariant immersions of the
same reduced variety is constructible, equivariant and functional in both
directions. Its graph includes every source and target complex point. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal
attribute [local instance] rationalAffinePair_immersion
variable {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ) {Y : EquivariantVariety.Object}
variable (f : Morphism Y (rationalAffineObject q)) (g : Morphism Y (rationalAffineObject r))
variable [IsImmersion f.hom] [IsImmersion g.hom]

def immersionCoordinateGraph : DiagonalConstructible.Object :=
  DiagonalConstructible.immersedObject (Fin.append q r) (rationalAffinePair q r f g)

theorem immersionCoordinateGraph_scheme_point (z : Fin (n + m) → ℂ)
    (hz : z ∈ (immersionCoordinateGraph q r f g).domain) :
    ∃ p : Y.scheme, (rationalAffinePair q r f g).hom p = complexTupleSpectrumPoint z := hz

theorem immersionCoordinateGraph_point_coordinates (p : Y.scheme) (z : Fin (n + m) → ℂ)
    (hp : (rationalAffinePair q r f g).hom p = complexTupleSpectrumPoint z) :
    f.hom p = complexTupleSpectrumPoint (fun i => z (Fin.castAdd m i)) ∧
      g.hom p = complexTupleSpectrumPoint (fun j => z (Fin.natAdd n j)) := by
  have hL := congrArg (fun h => h p) (rationalAffinePairMap_fst q r f g)
  have hR := congrArg (fun h => h p) (rationalAffinePairMap_snd q r f g)
  change (rationalAffineLeft q r).hom ((rationalAffinePair q r f g).hom p) = f.hom p at hL
  change (rationalAffineRight q r).hom ((rationalAffinePair q r f g).hom p) = g.hom p at hR
  exact ⟨hL.symm.trans ((congrArg (rationalAffineLeft q r).hom hp).trans
      (complexTupleSpectrumPoint_coordinate (Fin.castAdd m) z)),
    hR.symm.trans ((congrArg (rationalAffineRight q r).hom hp).trans
      (complexTupleSpectrumPoint_coordinate (Fin.natAdd n) z))⟩

theorem immersionCoordinateGraph_contained (z : Fin (n + m) → ℂ)
    (hz : z ∈ (immersionCoordinateGraph q r f g).domain) :
    (fun i => z (Fin.castAdd m i)) ∈ (DiagonalConstructible.immersedObject q f).domain ∧
      (fun j => z (Fin.natAdd n j)) ∈ (DiagonalConstructible.immersedObject r g).domain := by
  obtain ⟨p, hp⟩ := immersionCoordinateGraph_scheme_point q r f g z hz
  have hh := immersionCoordinateGraph_point_coordinates q r f g p z hp
  exact ⟨⟨p, hh.1⟩, ⟨p, hh.2⟩⟩

theorem immersionCoordinateGraph_left_unique (x : Fin n → ℂ) (y z : Fin m → ℂ)
    (hy : Fin.append x y ∈ (immersionCoordinateGraph q r f g).domain)
    (hz : Fin.append x z ∈ (immersionCoordinateGraph q r f g).domain) : y = z := by
  obtain ⟨p, hp⟩ := immersionCoordinateGraph_scheme_point q r f g _ hy
  obtain ⟨t, ht⟩ := immersionCoordinateGraph_scheme_point q r f g _ hz
  have hpc : f.hom p = complexTupleSpectrumPoint x ∧ g.hom p = complexTupleSpectrumPoint y := by
    simpa only [Fin.append_left, Fin.append_right] using immersionCoordinateGraph_point_coordinates q r f g p _ hp
  have htc : f.hom t = complexTupleSpectrumPoint x ∧ g.hom t = complexTupleSpectrumPoint z := by
    simpa only [Fin.append_left, Fin.append_right] using immersionCoordinateGraph_point_coordinates q r f g t _ ht
  have hpt : p = t := f.hom.isEmbedding.injective (hpc.1.trans htc.1.symm)
  exact complexTupleSpectrumPoint_injective (hpc.2.symm.trans ((congrArg g.hom hpt).trans htc.2))

theorem immersionCoordinateGraph_right_unique (y : Fin m → ℂ) (x z : Fin n → ℂ)
    (hx : Fin.append x y ∈ (immersionCoordinateGraph q r f g).domain)
    (hz : Fin.append z y ∈ (immersionCoordinateGraph q r f g).domain) : x = z := by
  obtain ⟨p, hp⟩ := immersionCoordinateGraph_scheme_point q r f g _ hx
  obtain ⟨t, ht⟩ := immersionCoordinateGraph_scheme_point q r f g _ hz
  have hpc : f.hom p = complexTupleSpectrumPoint x ∧ g.hom p = complexTupleSpectrumPoint y := by
    simpa only [Fin.append_left, Fin.append_right] using immersionCoordinateGraph_point_coordinates q r f g p _ hp
  have htc : f.hom t = complexTupleSpectrumPoint z ∧ g.hom t = complexTupleSpectrumPoint y := by
    simpa only [Fin.append_left, Fin.append_right] using immersionCoordinateGraph_point_coordinates q r f g t _ ht
  have hpt : p = t := g.hom.isEmbedding.injective (hpc.2.trans htc.2.symm)
  exact complexTupleSpectrumPoint_injective (hpc.1.symm.trans ((congrArg f.hom hpt).trans htc.1))

theorem immersionCoordinateGraph_left_exists (x : Fin n → ℂ)
    (hx : x ∈ (DiagonalConstructible.immersedObject q f).domain) :
    ∃ y : Fin m → ℂ, y ∈ (DiagonalConstructible.immersedObject r g).domain ∧
      Fin.append x y ∈ (immersionCoordinateGraph q r f g).domain := by
  obtain ⟨p, hp⟩ := hx
  let U := Set.range (rationalAffinePair q r f g).hom
  letI := (rationalAffineObject (Fin.append q r)).noetherian
  have hU := locallyClosed_constructible_of_noetherian (rationalAffinePair q r f g).hom.isLocallyClosed_range
  have hImage : complexTupleSpectrumPoint x ∈ Spec.map (CommRingCat.ofHom
      (MvPolynomial.rename (R := ℂ) (Fin.castAdd m : Fin n → Fin (n + m))).toRingHom) '' U := by
    refine ⟨(rationalAffinePair q r f g).hom p, Set.mem_range_self p, ?_⟩
    exact (congrArg (fun h => h p) (rationalAffinePairMap_fst q r f g)).trans hp
  obtain ⟨z, hz, hleft⟩ := complex_coordinate_lift (Fin.castAdd m) U hU x hImage
  have hzG : z ∈ (immersionCoordinateGraph q r f g).domain := hz
  refine ⟨(fun j => z (Fin.natAdd n j)), (immersionCoordinateGraph_contained q r f g z hzG).2, ?_⟩
  have he : Fin.append x (fun j => z (Fin.natAdd n j)) = z := by
    rw [← hleft]
    exact Fin.append_castAdd_natAdd (f := z)
  rw [he]
  exact hzG

theorem immersionCoordinateGraph_right_exists (y : Fin m → ℂ)
    (hy : y ∈ (DiagonalConstructible.immersedObject r g).domain) :
    ∃ x : Fin n → ℂ, x ∈ (DiagonalConstructible.immersedObject q f).domain ∧
      Fin.append x y ∈ (immersionCoordinateGraph q r f g).domain := by
  obtain ⟨p, hp⟩ := hy
  let U := Set.range (rationalAffinePair q r f g).hom
  letI := (rationalAffineObject (Fin.append q r)).noetherian
  have hU := locallyClosed_constructible_of_noetherian (rationalAffinePair q r f g).hom.isLocallyClosed_range
  have hImage : complexTupleSpectrumPoint y ∈ Spec.map (CommRingCat.ofHom
      (MvPolynomial.rename (R := ℂ) (Fin.natAdd n : Fin m → Fin (n + m))).toRingHom) '' U := by
    refine ⟨(rationalAffinePair q r f g).hom p, Set.mem_range_self p, ?_⟩
    exact (congrArg (fun h => h p) (rationalAffinePairMap_snd q r f g)).trans hp
  obtain ⟨z, hz, hright⟩ := complex_coordinate_lift (Fin.natAdd n) U hU y hImage
  have hzG : z ∈ (immersionCoordinateGraph q r f g).domain := hz
  refine ⟨(fun i => z (Fin.castAdd m i)), (immersionCoordinateGraph_contained q r f g z hzG).1, ?_⟩
  have he : Fin.append (fun i => z (Fin.castAdd m i)) y = z := by
    rw [← hright]
    exact Fin.append_castAdd_natAdd (f := z)
  rw [he]
  exact hzG

end DiamondIntegral.Section5
