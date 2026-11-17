import «section 3».GammaVFIdentityJacobian
import «section 3».GammaSurjectiveMapDescent
import «section 5».NativePullbackRVPresentation
import «section 3».GammaMeasuredObjectSurjectivity

/-! Every actual measured VF object has an actual measured arrow to a
same-ground RV lift, uniformly in all degrees. These maps strengthen the
previous class surjectivity and supply Cartesian compatibility. -/
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

theorem gammaMeasuredPullback_arrow_preimage
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundMeasuredVFData hc B (n+1))
    (hpull : SpecialTransformations.Section5.IsRVPullback U.domain.carrier)
    (hnz : ∀ p : U.domain, ∀ i, p.val.1 i ≠ 0)
    (hconst : ∀ p q : U.domain,
      Section5.nativeMixedFullKeyMap U.domain p = Section5.nativeMixedFullKeyMap U.domain q → U.form p = U.form q) :
    ∃ W : GammaGroundMeasuredRVObject hc B (n+1),
      Nonempty (GammaGroundMeasuredVFHom hκ hs hr hv U (gammaGroundMeasuredObjectLift W)) := by
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
  exact ⟨W,⟨f⟩⟩

theorem gammaMeasuredVFObject_arrow_preimage
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n : ℕ} (U : GammaGroundMeasuredVFData hc B n) :
    ∃ W : GammaGroundMeasuredRVObject hc B n,
      Nonempty (GammaGroundMeasuredVFHom hκ.le hs hr hv U (gammaGroundMeasuredObjectLift W)) := by
  cases n with
  | zero =>
    exact ⟨gammaZeroRVOfVF U,⟨(gammaZeroVFRepresentationIso U).inv⟩⟩
  | succ n =>
    obtain ⟨l,Y,e,hpull,hJ,hconst⟩ := gammaDensity_preparation hκ hs h00 hr hv U.domain U.form
    let V : GammaGroundMeasuredVFData hc B (n+1) := {
      arity := l+U.arity
      domain := Y
      finite := (gammaGroundFiniteRVFibres_iff e hκ.le hs h00 hr).mp U.finite
      form := U.form.comp e.symm.map }
    have hconstY (p q : Y) (heq : Section5.nativeMixedFullKeyMap Y p = Section5.nativeMixedFullKeyMap Y q) :
        V.form p = V.form q := by
      have heq' : Section5.nativeMixedFullKeyMap Y (e.map (e.symm.map p)) =
          Section5.nativeMixedFullKeyMap Y (e.map (e.symm.map q)) := by
        simpa only [GammaGroundBijection.symm,GammaGroundMap.apply_inverse] using heq
      exact Subtype.ext (hconst (e.symm.map p) (e.symm.map q) heq')
    let f := gammaPositiveMeasuredHomOfBijection hκ.le hs hr hv (U := U) (V := V) e (fun p hp => by
      refine ⟨1,hJ p hp,?_⟩
      rw [map_one,mul_one]
      change (gammaGroundFormValue U.form p).val = (gammaGroundFormValue U.form (e.symm.map (e.map p))).val
      rw [GammaGroundBijection.symm,GammaGroundMap.inverse_apply])
    let E := Section5.nativeVFZeroStratum Y Finset.univ
    have hE : E.carrier ⊆ Y.carrier := Section5.nativeVFZeroStratum_subset Y Finset.univ
    have hsmall : Section2.vfDimension (Y.sdiff E).carrier < ((n+1 : ℕ) : WithBot ℕ) := by
      apply gammaGround_small_complement_of_generic Y E hκ.le hs hr hv (Nat.zero_lt_succ n)
      intro p
      apply (Section5.nativeVFZeroStratum_mem Y Finset.univ p.val.val).mpr
      exact ⟨p.val.property,fun i => ⟨fun _ => p.property.ne_zero i,fun _ => Finset.mem_univ i⟩⟩
    let D := V.restrict E hE
    have hNZ (p : E) (i : Fin (n+1)) : p.val.1 i ≠ 0 :=
      (((Section5.nativeVFZeroStratum_mem Y Finset.univ p.val).mp p.property).2 i).mp (Finset.mem_univ i)
    have hconstE (p q : E) (heq : Section5.nativeMixedFullKeyMap E p = Section5.nativeMixedFullKeyMap E q) :
        D.form p = D.form q := by
      apply hconstY ⟨p.val,hE p.property⟩ ⟨q.val,hE q.property⟩
      exact Subtype.ext (congrArg Subtype.val heq)
    obtain ⟨W,⟨hW⟩⟩ := gammaMeasuredPullback_arrow_preimage hκ.le hs h00 hr hv D
      (Section5.nativeVFZeroStratum_pullback Y hpull Finset.univ) hNZ hconstE
    exact ⟨W,⟨(gammaGroundMeasuredVFGroupoid hκ.le hs hr hv (n+1)).comp f
      ((gammaGroundMeasuredVFGroupoid hκ.le hs hr hv (n+1)).comp
        (gammaMeasuredCofullRestrictionHom hκ.le hs hr hv V E hE hsmall) hW)⟩⟩

end DiamondIntegral.Section3
