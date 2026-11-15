import «section 5».NativeArbitraryWeakRVPresentation

/-! Bounded values normalized on the genuine Section 3 lifts compute
arbitrary zero strata and RV[<=k] presentations over the exact given base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
variable (V : GammaGroundVFGrothendieckRing hc B →+* RESDimensionFreeReduction.Ring B)
variable (hV : ∀ {k : ℕ} (U : GammaGroundRVObject hc B k),
  V (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ .bounded (ordinaryClass U))

include hV in
theorem normalizedVFBoundedValue_of_lift_bijection (A : GammaGroundFiniteVFObject hc B)
    {k : ℕ} (U : GammaGroundRVObject hc B k) (e : GammaGroundBijection A.domain (gammaGroundObjectLift U)) :
    V (nativeVFClass A) =
      nativeGroundRVEvaluation h00 linear hκ hs hc B
        hr hγ hΓ .bounded (ordinaryClass U) := by
  rw [nativeVFClass_bijection A (gammaGroundObjectLiftFinite U) e]
  exact hV U

include hV in
theorem normalizedVFBoundedValue_pullback (A : GammaGroundFiniteVFObject hc B)
    (hpull : IsRVPullback A.domain.carrier) :
    V (nativeVFClass A) =
      nativeRVSetValue h00 linear hκ hs hc B
        hr hγ hΓ .bounded (nativeMixedFullKeyMap A.domain).image := by
  rw [nativeVFClass_finite_partition A (nativeVFZeroStratum A.domain)
    (nativeVFZeroStratum_disjoint A.domain) (nativeVFZeroStratum_cover A.domain),map_sum]
  refine (Finset.sum_congr rfl (fun I _ => ?_)).trans
    (nativeVFZeroStrata_raw_value_sum h00 linear hκ hs
      hr hγ hΓ .bounded A.domain hpull A.finite)
  let U := nativeVFZeroStratumRVObject hκ hs h00 hr
    A.domain hpull A.finite I
  exact (normalizedVFBoundedValue_of_lift_bijection h00 linear hκ hs hr hγ hΓ V hV _ U
    (nativeVFZeroStratum_lift_bijection hκ hs h00 hr
      A.domain hpull A.finite I)).trans
    (nativeGroundRVEvaluation_class h00 linear hκ hs hc B
      hr hγ hΓ .bounded U)


include hV in
theorem normalizedVFBoundedValue_weak_lift {k : ℕ} (U : NativeWeakRVObject hc B k) :
    V (nativeVFClass (⟨k,U.arity,nativeWeakRVObjectLift U,nativeWeakRVObjectLift_finite U⟩ :
      GammaGroundFiniteVFObject hc B)) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .bounded U.domain :=
  (normalizedVFBoundedValue_pullback h00 linear hκ hs hr hγ hΓ V hV _
    (nativeWeakRVObjectLift_pullback U)).trans
      (nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ .bounded _ _ (nativeWeakLiftKeyBijection U))

include hV in
theorem normalizedVFBoundedValue_of_weak_lift_bijection (A : GammaGroundFiniteVFObject hc B)
    {k : ℕ} (U : NativeWeakRVObject hc B k) (e : GammaGroundBijection A.domain (nativeWeakRVObjectLift U)) :
    V (nativeVFClass A) = nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .bounded U.domain :=
  (congrArg V (nativeVFClass_bijection A
    (⟨k,U.arity,nativeWeakRVObjectLift U,nativeWeakRVObjectLift_finite U⟩ : GammaGroundFiniteVFObject hc B) e)).trans
      (normalizedVFBoundedValue_weak_lift h00 linear hκ hs hr hγ hΓ V hV U)

end DiamondIntegral.Section5
