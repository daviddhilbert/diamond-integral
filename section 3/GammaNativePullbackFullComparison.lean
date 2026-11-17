import «section 3».GammaFullMeasuredFixedMaps
import «section 3».GammaNativePullbackMeasuredLift

/-! The full-key lift comparison is an actual full Gamma bijection. Its
VF component is the identity and its RV label is precisely the full key. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
variable (hA : GammaSetDefinable B (carrier A)) (hAP : IsRVPullback (carrier A))
variable (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))

def gammaNativePullbackLiftBijection : GammaGroundBijection
    (Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)
    (gammaNativeUnitLift (hc := hc) (gammaPullbackAt (Set.subset_univ _) A hA hAF).toGamma).domain :=
  Section5.nativeGammaPointBijection hA
    (gammaPullbackAt (Set.subset_univ _) A hA hAF).toGamma.lift_definable
    (gammaPullbackLiftIso (B := B) (Set.subset_univ _) A hA hAP)

theorem gammaNativePullbackLiftBijection_vf
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA) :
    ((gammaNativePullbackLiftBijection A hA hAP hAF).map p).val.1 = p.val.1 := by
  dsimp only [gammaNativePullbackLiftBijection]
  rw [Section5.nativeGammaPointBijection_apply]
  dsimp only [gammaPullbackLiftIso]
  rw [gammaIso_congr_value]
  rfl

theorem gammaNativePullbackLiftBijection_label
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA) :
    gammaNativeLiftLabel (gammaPullbackAt (Set.subset_univ _) A hA hAF)
      ((gammaNativePullbackLiftBijection A hA hAP hAF).map p) = gammaNativePullbackKeyMap A hA hAF p := by
  apply Subtype.ext
  dsimp only [gammaNativePullbackLiftBijection]
  rw [gammaNativeLiftLabel_val,Section5.nativeGammaPointBijection_apply]
  dsimp only [gammaPullbackLiftIso]
  rw [gammaIso_congr_value]
  rfl

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativePullbackFullMeasured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaPullbackAt (Set.subset_univ _) A hA hAF)))
    (hπ : ∀ p, π (gammaNativePullbackKeyMap A hA hAF p) = ω p) :
    GammaFullMeasuredBijection (gammaNativeMeasuredPointData A hA hfin ω)
      (gammaNativeMeasuredLift (gammaPullbackAt (Set.subset_univ _) A hA hAF) π) := by
  apply gammaFullMeasuredFixedVF hκ hs hr hv (gammaNativePullbackLiftBijection A hA hAP hAF)
    (gammaNativePullbackLiftBijection_vf A hA hAP hAF)
  intro p
  change (gammaGroundFormValue ω p).val =
    (gammaGroundFormValue π (gammaNativeLiftLabel _ ((gammaNativePullbackLiftBijection A hA hAP hAF).map p))).val
  rw [gammaNativePullbackLiftBijection_label]
  exact congrArg (fun z => (cast (gammaCarrier hc) z.val).val) (hπ p).symm

end DiamondIntegral.Section3
