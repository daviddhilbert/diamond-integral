import «section 3».GammaNativeRelativeFullAdditive
import «section 3».GammaMeasuredGeometricRelations
import «section 3».GammaNativeFullMeasuredPermutations

/-! Every native one-coordinate full measured comparison has a finite original-base geometric derivation, before passage to the principal quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeRelativeFullMeasured_geometric_relation
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (i : Fin (n+1)) (hi : ∀ q, ∀ j, j ≠ i → (f.map.map q).val.1 j = q.val.1 j) :
    GammaMeasuredGeometricRelation hκ.le hs h00 hr
      (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) := by
  let q : GammaGroundMeasuredRVKPlus hc B (n+1) →+
      (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := n) hκ.le hs h00 hr).Quotient :=
    (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := n) hκ.le hs h00 hr).mk'
  have H := gammaNativeRelativeFullMeasured_additive_comparison
    (W := (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := n) hκ.le hs h00 hr).Quotient) hκ hs h00 hr hg q
    (gammaNativeGeometricQuotient_elementary (hc := hc) (B := B) (n := n) hκ.le hs h00 hr)
    hv C₀ hBC₀ δ hδ hδ1 U V ω η f i hi
  exact gammaMeasuredGeometricRelation_of_additive_derivation
    ((gammaNativeGeometricCongruence hκ.le hs h00 hr).eq.mp H) _ _ rfl rfl

end DiamondIntegral.Section3
