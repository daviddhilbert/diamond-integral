import «section 6».DiamondLift
import «section 7».ChartLifting

/-! Section 4 charts in `μVF^◇`: the lift of a doubly bounded chart without
infinity coordinates is an object of `μVF^◇[k]` (Definition 6.34), and measured
chart isomorphisms lift to isomorphisms there (Corollary 6.37, through
`ChartLifting.chart_iso_lift`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2 DiamondIntegral.Section6

namespace DiamondIntegral.Section7.ChartDiamondLift
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

open DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.MeasuredRVBounds

/-- The object of `μVF^◇[k]` lifted from a doubly bounded chart without
infinity coordinates. -/
def chartObject
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M)) {k : ℕ}
    (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (ha : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded a) (hna : NoInfinity a) :
    VFObject (M := M) S k :=
  liftObject (toMeasured hc a) (measuredRVLift_properInvariant h00 hc hκ hs hv _
    (toMeasured_doublyBounded hc h00 linear hκ.le hs hsmall hΓ a ha hna))

/-- Measured isomorphisms of doubly bounded charts lift to isomorphisms of
`μVF^◇[k]`. -/
theorem chart_isomorphic
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) {k : ℕ} (hn : 0 < k)
    {a b : Chart (⟨(T : Set M), ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b)
    (ha : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded a)
    (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded b)
    (hna : NoInfinity a) (hnb : NoInfinity b) :
    Isomorphic G (chartObject h00 hc linear hκ hs hv hsmall hΓ a ha hna)
      (chartObject h00 hc linear hκ hs hv hsmall hΓ b hb hnb) := by
  obtain ⟨L, _, _, hprop, _⟩ := ChartLifting.chart_iso_lift (G := G) h00 hc linear hκ hs hv T B
    hsmall hΓ hnt hn F ha hb hna hnb
  exact ⟨liftMorphism _ _ L hprop⟩

end DiamondIntegral.Section7.ChartDiamondLift
