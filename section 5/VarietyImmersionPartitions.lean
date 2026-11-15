import «section 5».VarietySubsetScissors

/-! A finite disjoint partition by actual equivariant reduced immersions
gives an equality in the geometric ring using only its defining scissors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] Object.reduced

theorem Morphism.range_invariant {X Y : Object} (f : Morphism Y X) :
    X.Invariant (Set.range f.hom) := by
  have hforward (h : CompatibleRoots ℂ) (x : X.scheme) (hx : x ∈ Set.range f.hom) :
      schemePointAction X.action h x ∈ Set.range f.hom := by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨schemePointAction Y.action h y, ?_⟩
    exact congrArg (fun m : Y.scheme ⟶ X.scheme => m y) (f.equivariant h)
  intro h x
  constructor
  · intro hx
    have hh := hforward h⁻¹ (schemePointAction X.action h x) hx
    rwa [← schemePointAction_mul, inv_mul_cancel, schemePointAction_one] at hh
  · exact hforward h x

theorem objectClass_eq_subsetClass {X Y : Object} (f : Morphism Y X) [IsImmersion f.hom] :
    objectClass Y = subsetClass X (Set.range f.hom) := by
  let hS := f.hom.isLocallyClosed_range
  let hiS := f.range_invariant
  rw [subsetClass_of_locallyClosed X (Set.range f.hom) hS hiS]
  letI := subsetInclusion_immersion X (Set.range f.hom) hS hiS
  exact objectClass_immersed_presentations f (subsetInclusion X (Set.range f.hom) hS hiS)
    (subsetInclusion_range X (Set.range f.hom) hS hiS).symm

theorem objectClass_finite_immersed_partition (X : Object) {ι : Type} [Fintype ι]
    (Y : ι → Object) (f : ∀ i, Morphism (Y i) X) [∀ i, IsImmersion (f i).hom]
    (hpart : ∀ x : X.scheme, ∃! i, x ∈ Set.range (f i).hom) :
    objectClass X = ∑ i, objectClass (Y i) := by
  have hp := subsetClass_finite_partition X (fun i => Set.range (f i).hom)
    (fun i => (f i).hom.isLocallyClosed_range) (fun i => (f i).range_invariant)
    (by
      intro i j hne
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      obtain ⟨k, hk, huniq⟩ := hpart x
      exact hne ((huniq i hxi).trans (huniq j hxj).symm))
    (fun x => let ⟨i, hi, _⟩ := hpart x; ⟨i, hi⟩)
  rw [hp]
  apply Finset.sum_congr rfl
  intro i _
  exact (objectClass_eq_subsetClass (f i)).symm

end DiamondIntegral.Section5.EquivariantVariety
