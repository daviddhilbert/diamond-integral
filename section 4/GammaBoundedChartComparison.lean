import «section 4».GammaBoundedChartMap
import «section 4».GammaBoundedFamilies

/-! The actual bounded chart specialization is independent of the Euler
choice on its entire generated subring, not only on individual objects. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedChartComparison
open GammaWeightedCharts GammaChartPresentation GammaBoundedProducts GammaBoundedChartMap
open GammaBoundedFamilies GammaIndicators

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem bounded_hom_ext (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : boundedChartSubring B →+* R)
    (h : ∀ n (a : Chart B n) (ha : DomainBounded a.support), f (boundedClass a ha) = g (boundedClass a ha)) : f = g := by
  apply RingHom.ext
  intro p
  refine Subring.closure_induction
    (p := fun x hx => f (⟨x, hx⟩ : boundedChartSubring B) = g ⟨x, hx⟩) ?_ ?_ ?_ ?_ ?_ ?_ p.property
  · rintro x ⟨n, a, ha, rfl⟩
    exact h n a ha
  · change f 0 = g 0
    rw [map_zero, map_zero]
  · change f 1 = g 1
    rw [map_one, map_one]
  · intro x y hx hy hfx hfy
    change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, hfx, hfy]
  · intro x hx hfx
    change f (-⟨x, hx⟩) = g (-⟨x, hx⟩)
    rw [map_neg, map_neg, hfx]
  · intro x y hx hy hfx hfy
    change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, hfx, hfy]

theorem specialize_independent_kind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind)
    {R : Type*} [CommRing R] (T : R) :
    GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k T =
      GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ l T := by
  apply bounded_hom_ext B
  intro n a ha
  rw [specialize_boundedClass, specialize_boundedClass]
  obtain ⟨β, hβ⟩ := ha
  have hb : BoxSupported β⁻¹ β (indicatorFamily B a.support a.support_definable).val := by
    intro z hz i
    have hzI : z ∈ a.support := by
      by_contra hn
      exact hz (by simp [indicatorFamily, hn])
    exact hβ z hzI i
  exact congrArg (fun m : ℤ => (m : R) * T ^ n)
    (integrateAll_bounded_comparison h00 hκ hs B hr hγ k l n
      (indicatorFamily B a.support a.support_definable) β⁻¹ β hb)

end DiamondIntegral.Section4.GammaBoundedChartComparison
