import «section 6».UnaryScalarGraphFibres

/-! Paired centered discs on the actual mixed graph fibres. Smallness
is retained after adjoining the two finite tuples of old RV labels. The
target center is the actual image point and its radius is taken from
the image of the chosen source disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem paired_discs_for_unary_graph_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (h : ProperCovariantHomeomorphism f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a : VF M) (ha : a ∈ unaryGraphFibreSource f u v) :
    ∃ ρ : Gamma M ≃o Gamma M, ∃ γ₀ : Gamma M, ∀ γ : Gamma M,γ₀ ≤ γ →
      centeredGammaDisc a γ ⊆ unaryGraphFibreSource f u v ∧
      centeredGammaDisc (unaryGraphFibreMap f u v a) (ρ γ) ⊆ unaryGraphFibreRange f u v ∧
      unaryGraphFibreMap f u v '' centeredGammaDisc a γ=
        centeredGammaDisc (unaryGraphFibreMap f u v a) (ρ γ) := by
  have hSmallU := small_union_finite hκ S hsmall _ (Set.finite_range (rvValues u))
  have hSmall := small_union_finite hκ (S ∪ Set.range (rvValues u)) hSmallU _ (Set.finite_range (rvValues v))
  exact continuous_bijection_paired_centered_discs hc hκ hs hSmall hv
    (unaryGraphFibreSource f u v) (unaryGraphFibreRange f u v)
    (unaryGraphFibreSource_open hv f h.covariant u v) (unaryGraphFibreMap f u v)
    (unaryGraphFibreMap_bijOn f h.bijective.injective u v)
    (unaryGraphFibreMap_graph_definable f u v) (unaryGraphFibreMap_continuous f h.continuous u v)
    (unaryGraphFibreRange_bounded f h.covariant.imageVFBounded u v) a ha

end DiamondIntegral.Section6
