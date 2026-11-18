import «section 7».MeasuredRVBounds
import «section 6».MeasuredMorphismsLiftChains

/-! Lifting isomorphisms of bounded charts (Corollary 6.37 and Lemma 7.12,
morphism part).

A measured isomorphism of doubly bounded Section 4 charts over the
VF-generated base, with no infinity coordinates, is transported to Section 6's
measured RV objects and lifted by Section 6's Lemma 6.33: the lift is a finite
chain of relatively unary measured VF maps whose composite is a proper
covariant homeomorphism, and it contracts to the given isomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.ChartLifting
open DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.MeasuredRVBounds

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k : ℕ}

theorem chart_iso_lift
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < k)
    {a b : Chart (⟨(S : Set M), ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b)
    (ha : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded a)
    (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded b)
    (hna : NoInfinity a) (hnb : NoInfinity b) :
    ∃ T : DiamondIntegral.Section6.MeasuredVFUnaryLiftChain (S : Set M) k (toMeasured hc a) (toMeasured hc b),
      T.iso.iso.hom.map = (measuredIso hc F).iso.hom.map ∧ T.doublyBounded ∧ T.properComponents ∧
        DiamondIntegral.Section6.ProperCovariantHomeomorphism T.lift.map :=
  DiamondIntegral.Section6.lemma_6_33_doublyBounded_vfGenerated h00 hc linear hκ hs hv S B hsmall hΓ hnt hn
    (measuredIso hc F)
    (toMeasured_doublyBounded hc h00 linear hκ.le hs hsmall hΓ a ha hna)
    (toMeasured_doublyBounded hc h00 linear hκ.le hs hsmall hΓ b hb hnb)

end DiamondIntegral.Section7.ChartLifting
