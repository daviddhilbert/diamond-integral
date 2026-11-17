import «section 3».GammaElementaryLiftJacobian
import «section 3».GammaMeasuredArrowLift
import IntegrationSection6.FiniteGammaElementaryAt
import Section7.GammaScissors

/-! The concrete native elementary diagram induces a measured VF arrow
with unit Gamma form, even when its RV presentation contains the zero
stratum. That stratum is removed only in the essential VF category. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaNativeUnitLift (U : GammaRVFiniteObject B n) : GammaGroundMeasuredVFData hc B n where
  arity := rvObjectArity U.object
  domain := Section5.nativeGammaPointDomain U.lift U.lift_definable
  finite := gammaLiftVF_finite U.toGammaRVObject U.finite_volume
  form := gammaGroundOneForm _

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeUnitElementaryHom
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : FiniteRV.GammaObjectAt B Set.univ (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (D : ElementaryLiftDiagram U.toGamma.toGammaRVObject i) :
    GammaGroundMeasuredVFHom hκ hs hr hv (gammaNativeUnitLift (hc := hc) U.toGamma)
      (gammaNativeUnitLift (hc := hc) (FiniteRV.gammaElementaryAt hκ hs h00 hr U i hAd).toGamma) := by
  let V := FiniteRV.gammaElementaryAt hκ hs h00 hr U i hAd
  let ea : U.toGamma.lift ≃ carrier (typedLift U.object.obj) := {
    toFun p := ⟨p.val,(typedLift_carrier U.object.obj).ge p.property⟩
    invFun p := ⟨p.val,(typedLift_carrier U.object.obj).le p.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let eb : carrier (typedLift V.object.obj) ≃ V.toGamma.lift := {
    toFun p := ⟨p.val,(typedLift_carrier V.object.obj).le p.property⟩
    invFun p := ⟨p.val,(typedLift_carrier V.object.obj).ge p.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let E := ea.trans (D.liftIso.equiv.trans eb)
  have hg : GammaGraphDefinable B (fun p q => ∃ a : U.toGamma.lift, a.val=p ∧ (E a).val=q) := by
    apply GammaGraphDefinable.congr D.liftIso.graph
    intro p q
    constructor
    · rintro ⟨a,ha,hb⟩
      refine ⟨ea.symm a,ha,?_⟩
      have he : (E (ea.symm a)).val = (D.liftIso.equiv a).val :=
        congrArg (fun z => (D.liftIso.equiv z).val) (ea.apply_symm_apply a)
      exact he.trans hb
    · rintro ⟨a,ha,hb⟩
      exact ⟨ea a,ha,hb⟩
  let e : GammaIso B U.toGamma.lift V.toGamma.lift := ⟨E,hg⟩
  let F := Section5.nativeGammaPointBijection (hc := hc) U.toGamma.lift_definable V.toGamma.lift_definable e
  have hF (p : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
      (F.map p).val = (D.liftIso.equiv (ea p)).val :=
    Section5.nativeGammaPointBijection_apply _ _ e p
  apply gammaPositiveMeasuredHomOfBijection hκ hs hr hv F
  intro p hp
  have hJ := gammaElementaryLift_jacobian_one hc hκ hs hr hv D (ea p) hp
  have hJF : HasMixedVFJacobianAt F.map p 1 := by
    obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hJ
    refine ⟨H,⟨ρ,fun x hx => ?_⟩,hH⟩
    obtain ⟨ha,hf⟩ := hρ x hx
    have ha' : (x,p.val.2) ∈ U.toGamma.lift := (typedLift_carrier U.object.obj).le ha
    refine ⟨ha',?_⟩
    rw [hF,hF]
    exact hf
  exact ⟨1,hJF,by change (1 : Values.GammaTop (M := M)) = 1 * Values.vfValueHom 1; rw [map_one,mul_one]⟩

end DiamondIntegral.Section3
