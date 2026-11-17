import «section 3».GammaMeasuredHomLift
import «section 3».GammaZeroMeasuredClassLift

/-! Measured lifting sends each actual RV arrow to an actual measured VF
germ, including the exact degree-zero category. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaEssentialOfBijection {n r s : ℕ}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s)}
    (f : GammaGroundBijection A D) : GammaGroundEssentialVFMap A D where
  source := A
  target := D
  source_subset := Set.Subset.refl _
  target_subset := Set.Subset.refl _
  source_small := by rw [show (A.sdiff A).carrier = ∅ from Set.sdiff_self,Section2.vfDimension_empty]; exact WithBot.bot_lt_coe n
  target_small := by rw [show (D.sdiff D).carrier = ∅ from Set.sdiff_self,Section2.vfDimension_empty]; exact WithBot.bot_lt_coe n
  map := f.map
  bijective := f.bijective

def gammaPositiveMeasuredHomOfBijection {n : ℕ}
    {U V : GammaGroundMeasuredVFData hc B (n+1)}
    (f : GammaGroundBijection U.domain V.domain)
    (hf : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      ∃ J : Section2.VF M, HasMixedVFJacobianAt f.map p J ∧
        gammaGroundMeasuredVFWeight U p = gammaGroundMeasuredVFWeight V (f.map p) * Values.vfValueHom J) :
    GammaGroundMeasuredVFHom hκ hs hS hv U V := by
  let F := gammaEssentialOfBijection f
  have hF : F.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V) := hf
  exact (gammaGroundMeasuredGermEquivGeneric hκ hs hS hv (Nat.zero_lt_succ n) U V).symm
    ⟨F.genericEquiv hκ hs hS hv (Nat.zero_lt_succ n),F,hF,rfl⟩

def gammaMeasuredArrowLift
    (h00 : M ⊨ Axioms.ACVF00) (hB : VFGammaGeneratedBase B)
    {n : ℕ} {U V : GammaGroundMeasuredRVObject hc B n} (e : GammaGroundMeasuredRVHom U V) :
    GammaGroundMeasuredVFHom hκ hs hS hv (gammaGroundMeasuredObjectLift U) (gammaGroundMeasuredObjectLift V) := by
  cases n with
  | zero => exact gammaGroundZeroMeasuredRVLiftHom e
  | succ n =>
    let H := gammaMeasuredHom_lift_bijection hκ hs h00 hS hB hv e
    exact gammaPositiveMeasuredHomOfBijection hκ hs hS hv H.choose H.choose_spec.2

def gammaMeasuredHomOfCarrierEq {n : ℕ}
    {U V : GammaGroundMeasuredVFData hc B n} (har : U.arity = V.arity)
    (h : HEq U.domain V.domain)
    (hw : ∀ (p : U.domain) (q : V.domain), HEq p.val q.val →
      gammaGroundMeasuredVFWeight U p = gammaGroundMeasuredVFWeight V q) :
    GammaGroundMeasuredVFHom hκ hs hS hv U V := by
  cases U with
  | mk ar A hfin ω =>
    cases V with
    | mk br D hfin' π =>
      cases har
      have he : A = D := eq_of_heq h
      subst D
      cases n with
      | zero => exact ⟨GammaGroundBijection.id A,fun p => Subtype.ext (hw p p HEq.rfl)⟩
      | succ n =>
        let f := GammaGroundBijection.id A
        apply gammaPositiveMeasuredHomOfBijection hκ hs hS hv f
        intro p hp
        obtain ⟨L,H,⟨ρ,hρ⟩,hder⟩ := gammaGround_differentiable_of_independent hκ hs hS hv f.map p hp
        have hid : IsVFChartAt f.map p (fun x => x) := by
          refine ⟨ρ,fun x hx => ?_⟩
          obtain ⟨ha,_⟩ := hρ x hx
          exact ⟨ha,rfl⟩
        have hId : HasVFDerivativeAt (fun x : Fin (n+1) → Section2.VF M => x) p.val.1 LinearMap.id := by
          simpa only [LinearMap.id_apply,add_zero] using
            hasVFDerivativeAt_affine (LinearMap.id : (Fin (n+1) → Section2.VF M) →ₗ[Section2.VF M] (Fin (n+1) → Section2.VF M)) 0 p.val.1
        refine ⟨1,⟨_,hid,?_⟩,?_⟩
        · simpa only [LinearMap.toMatrix'_id,Matrix.det_one] using hId.hasJacobianAt
        · rw [map_one,mul_one]
          have he : f.map p = p := rfl
          rw [he]
          exact hw p p HEq.rfl

end DiamondIntegral.Section3
