import «section 3».GammaVFIdentityJacobian
import «section 3».GammaSurjectiveMapDescent
import «section 5».NativePullbackRVPresentation

/-! A nonzero RV-pullback with a polydisc-constant Gamma density is the
actual measured lift of a same-ground RV object. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasuredPullback_class_preimage
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundMeasuredVFData hc B (n+1))
    (hpull : SpecialTransformations.Section5.IsRVPullback U.domain.carrier)
    (hnz : ∀ p : U.domain, ∀ i, p.val.1 i ≠ 0)
    (hconst : ∀ p q : U.domain,
      Section5.nativeMixedFullKeyMap U.domain p = Section5.nativeMixedFullKeyMap U.domain q → U.form p = U.form q) :
    ∃ W : GammaGroundMeasuredRVObject hc B (n+1),
      gammaGroundMeasuredVFClass hκ hs hr hv U =
        gammaGroundMeasuredVFClass hκ hs hr hv (gammaGroundMeasuredObjectLift W) := by
  let K := Section5.nativeMixedFullKeyMap U.domain
  have hK : Function.Surjective K.toImage := by
    rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩
  have hconst' : ∀ p q, K.toImage p = K.toImage q → U.form p = U.form q :=
    fun p q hpq => by
      have hv := congrArg (fun z : K.image => z.val) hpq
      exact hconst p q (Subtype.ext hv)
  let η := gammaGroundSurjectiveDescent K.toImage hK U.form hconst'
  let W : GammaGroundMeasuredRVObject hc B (n+1) :=
    ⟨Section5.nativePullbackRVObject hκ hs h00 hr U.domain hpull U.finite hnz,η⟩
  let e := Section5.nativePullbackRVObject_lift_bijection hκ hs h00 hr U.domain hpull U.finite hnz
  have hlabel (p : U.domain) : gammaGroundObjectLiftLabel W.underlying (e.map p) = K.toImage p :=
    Subtype.ext rfl
  let f := gammaPositiveMeasuredHomOfBijection hκ hs hr hv
    (U := U) (V := gammaGroundMeasuredObjectLift W) e (fun p hp => by
      refine ⟨1,gammaVFFixed_jacobian_one hκ hs hr hv e.map (fun _ => rfl) p hp,?_⟩
      rw [map_one,mul_one]
      change (gammaGroundFormValue U.form p).val =
        (gammaGroundFormValue η (gammaGroundObjectLiftLabel W.underlying (e.map p))).val
      rw [hlabel]
      exact congrArg (fun z => (cast (gammaCarrier hc) z.val).val)
        (gammaGroundSurjectiveDescent_apply K.toImage hK U.form hconst' p).symm)
  exact ⟨W,gammaGroundMeasuredVFClass_iso hκ hs hr hv f⟩

end DiamondIntegral.Section3
