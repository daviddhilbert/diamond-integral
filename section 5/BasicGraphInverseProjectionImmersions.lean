import «section 5».BasicGraphProjectionImmersions

/-! The inverse rational description makes the other projection an
actual immersion as well. The swap of graph coordinates is an actual
polynomial algebra isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] basicConstructibleCoordinate_reduced basicConstructibleCoordinate_finiteType
variable {n m : ℕ}
variable (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))

theorem basicGraphRight_rational_relations (p : Fin n → MvPolynomial (Fin m) ℂ)
    (q : MvPolynomial (Fin m) ℂ)
    (hD : D.toSet ⊆ (inverseRationalSpectrumGraphData p q).toSet) :
    IsUnit (basicGraphRight D q) ∧ ∀ i,
      basicGraphLeft D (MvPolynomial.X i) * basicGraphRight D q = basicGraphRight D (p i) := by
  constructor
  · apply (complex_points_isUnit _).mpr
    intro φ
    have h := (hD (basicConstructiblePoint_mem D φ)).2
    have hn : (φ.comp (basicConstructibleCoordinateMap D))
        ((inverseRationalSpectrumGraphData p q).f) ≠ 0 := by
      intro hz
      apply h
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hz
    rw [inverseRationalSpectrumGraphData_denominator] at hn
    exact hn
  · intro i
    refine complex_points_separate (A := BasicConstructibleCoordinateRing D)
      (basicGraphLeft D (MvPolynomial.X i) * basicGraphRight D q) (basicGraphRight D (p i)) ?_
    intro φ
    have h := (hD (basicConstructiblePoint_mem D φ)).1 (Set.mem_range_self i)
    change (φ.comp (basicConstructibleCoordinateMap D))
      ((inverseRationalSpectrumGraphData p q).g i) = 0 at h
    rw [inverseRationalSpectrumGraphData_equation] at h
    have h0 : φ (basicGraphLeft D (MvPolynomial.X i)) * φ (basicGraphRight D q) -
        φ (basicGraphRight D (p i)) = 0 := by
      simpa only [basicGraphLeft, basicGraphRight, AlgHom.comp_apply, MvPolynomial.rename_X,
        map_sub, map_mul] using h
    simpa only [map_mul] using sub_eq_zero.mp h0

theorem basicGraphMap_swap_eq : polynomialGraphMap (basicGraphRight D) (basicGraphLeft D) =
    (basicConstructibleCoordinateMap D).comp
      (MvPolynomial.renameEquiv ℂ (Equiv.sumComm (Fin m) (Fin n))).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [polynomialGraphMap, basicGraphLeft, basicGraphRight, MvPolynomial.renameEquiv]

theorem basicGraphRight_isImmersion (p : Fin n → MvPolynomial (Fin m) ℂ)
    (q : MvPolynomial (Fin m) ℂ)
    (hD : D.toSet ⊆ (inverseRationalSpectrumGraphData p q).toSet) :
    IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphRight D).toRingHom)) := by
  obtain ⟨hq, hr⟩ := basicGraphRight_rational_relations D p q hD
  apply rational_graph_projection_isImmersion (basicGraphRight D) (basicGraphLeft D) p q hq hr
  rw [basicGraphMap_swap_eq]
  let e := MvPolynomial.renameEquiv ℂ (Equiv.sumComm (Fin m) (Fin n))
  change IsImmersion (Spec.map (CommRingCat.ofHom
    ((basicConstructibleCoordinateMap D).toRingHom.comp e.toAlgHom.toRingHom)))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  letI : IsImmersion (Spec.map (CommRingCat.ofHom (basicConstructibleCoordinateMap D).toRingHom)) :=
    basicConstructibleInclusion_isImmersion D
  haveI : IsIso (CommRingCat.ofHom e.toAlgHom.toRingHom) :=
    inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
  infer_instance

end DiamondIntegral.Section5
