import «section 6».CentripetalDifferential
import Section9.MixedDifferentiationAE

/-! The same-base exceptional set for definable local shears and their
compositions. Canonicality, genuine saturation, smallness, and finite
fibers are retained exactly where the generic-point argument uses them.
The concrete proper special-bijection constructors are a separate adapter. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n r s t : ℕ}
variable {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S}

def HasMixedUnitDerivativeAt (f : Map A B) (p : A) : Prop :=
  ∃ L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M),
    HasMixedVFDerivativeAt f p L ∧ (LinearMap.toMatrix' L).det = 1

def HasLocalShearCharts (f : Map A B) : Prop :=
  ∀ p : A, ∃ j : Fin n, ∃ focus : (Fin n → VF M) → VF M,
    IsVFChartAt f p (coordinateShear j focus)

theorem mixed_unit_derivative_of_shear_chart (f : Map A B) (p : A)
    (j : Fin n) (focus : (Fin n → VF M) → VF M)
    (hchart : IsVFChartAt f p (coordinateShear j focus))
    (hd : ∃ L, HasMixedVFDerivativeAt f p L) : HasMixedUnitDerivativeAt f p := by
  obtain ⟨L,F,hF,hL⟩ := hd
  have hderiv : HasMixedVFDerivativeAt f p L := ⟨F,hF,hL⟩
  obtain ⟨ρF,hρF⟩ := hF
  obtain ⟨ρT,hρT⟩ := hchart
  have he : Set.EqOn F (coordinateShear j focus) (vfBall p.val.1 (max ρF ρT)) := by
    intro x hx
    obtain ⟨_,hfx⟩ := hρF x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨_,htx⟩ := hρT x (vfBall_anti (le_max_right _ _) hx)
    exact congrArg Prod.fst (hfx.symm.trans htx)
  exact ⟨L,hderiv,coordinateShear_derivative_det_one j focus p.val.1 L
    (hL.congr_on_vfBall he)⟩

theorem HasMixedUnitDerivativeAt.partialJacobian {f : Map A B} {p : A}
    (hf : HasMixedUnitDerivativeAt f p) : HasMixedVFJacobianAt f p 1 := by
  obtain ⟨L,⟨F,hF,hL⟩,hdet⟩ := hf
  refine ⟨F,hF,?_⟩
  rw [← hdet]
  exact hL.hasJacobianAt

theorem HasMixedUnitDerivativeAt.comp {f : Map A B} {g : Map B C} {p : A}
    (hg : HasMixedUnitDerivativeAt g (f p)) (hf : HasMixedUnitDerivativeAt f p) :
    HasMixedUnitDerivativeAt (g.comp f) p := by
  obtain ⟨L,⟨F,hF,hL⟩,hLd⟩ := hf
  obtain ⟨D,⟨G,hG,hD⟩,hDd⟩ := hg
  have hD' : HasVFDerivativeAt G (F p.val.1) D := hF.center.symm ▸ hD
  refine ⟨D.comp L,⟨G ∘ F,hF.comp hG hL,hD'.comp hL⟩,?_⟩
  rw [LinearMap.toMatrix'_comp,Matrix.det_mul,hDd,hLd,mul_one]

/-- An actual original-base definable bad set, with a full derivative
and determinant one at every remaining point. -/
theorem exists_mixed_unit_derivative_exception
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hn : 0 < n) (f : Map A B)
    (hgeneric : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      HasMixedUnitDerivativeAt f p) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p := by
  let P := rawMixedSpace (M := M) n r
  let D := mixedDerivativeLocus f (fun D => D.det = 1)
  let E : DefSet P S := ⟨A.carrier \ D,A.definable.sdiff P (mixedJacobianOneLocus_definable hn f)⟩
  refine ⟨E,Set.sdiff_subset,?_,?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn
    intro p hp
    let q : A := ⟨p.val,p.property.1⟩
    obtain ⟨L,hL,hdet⟩ := hgeneric q hp
    exact p.property.2 ⟨q,rfl,LinearMap.toMatrix' L,hdet,
      by simpa only [Matrix.toLin'_toMatrix'] using hL⟩
  · intro p hp
    have hgood : p.val ∈ D := by
      by_contra h
      exact hp ⟨p.property,h⟩
    obtain ⟨q,hq,L,hdet,hL⟩ := hgood
    have he : q = p := Subtype.ext hq
    subst q
    exact ⟨Matrix.toLin' L,hL,by rwa [LinearMap.toMatrix'_toLin']⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem local_shear_unit_derivative_ae [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (f : Map A B) (hcharts : HasLocalShearCharts f) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p := by
  apply exists_mixed_unit_derivative_exception hc hs hsmall hn f
  intro p hp
  obtain ⟨j,focus,hchart⟩ := hcharts p
  exact mixed_unit_derivative_of_shear_chart f p j focus hchart
    (mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f p hp)

theorem two_shears_unit_derivative_ae [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (f : Map A B) (g : Map B C)
    (hf : f.FiniteFibres) (hfc : HasLocalShearCharts f) (hgc : HasLocalShearCharts g) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt (g.comp f) p := by
  apply exists_mixed_unit_derivative_exception hc hs hsmall hn (g.comp f)
  intro p hp
  obtain ⟨j,focus,hchart⟩ := hfc p
  obtain ⟨k,focus',hchart'⟩ := hgc (f p)
  exact (mixed_unit_derivative_of_shear_chart g (f p) k focus' hchart'
    (mixedDifferentiableAt_of_independent hc hκ hs hsmall hv g (f p)
      (independent_map_of_finiteFibres hc f hf p hp))).comp
    (mixed_unit_derivative_of_shear_chart f p j focus hchart
      (mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f p hp))

end DiamondIntegral.Section6
