import «section 3».GammaNativePullbackForms
import «section 3».GammaNativeMeasuredNormalization
import «section 3».GammaVFIdentityJacobian
import IntegrationSection6.GammaPullbackLiftIsomorphisms

/-! The literal native full-key presentation of an RV-pullback transports
its arbitrary Gamma form by a VF-identity measured bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
theorem gammaIso_congr_value {p q r s : ℕ}
    {X X' : Set (Point (M := M) p q)} {Y Y' : Set (Point (M := M) r s)}
    (e : GammaIso B X Y) (hX : X = X') (hY : Y = Y') (x : X') :
    ((e.congr hX hY).equiv x).val = (e.equiv ⟨x.val,hX.ge x.property⟩).val := by
  cases hX
  cases hY
  rfl

variable (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
variable (hA : GammaSetDefinable B (carrier A))

def gammaNativeMeasuredPointData (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA)) :
    GammaGroundMeasuredVFData hc B n :=
  ⟨a,Section5.nativeGammaPointDomain (carrier A) hA,hfin,ω⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

set_option maxHeartbeats 4000000 in
def gammaNativePullbackMeasuredHom
    {n a : ℕ} (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) a)
    (hA : GammaSetDefinable B (carrier A))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hAP : IsRVPullback (carrier A))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (hω : ∀ p q, p.val.2 = q.val.2 → ω p = ω q) :
    GammaGroundMeasuredVFHom hκ hs hr hv (gammaNativeMeasuredPointData A hA hfin ω)
      (gammaNativeMeasuredLift (gammaPullbackAt (Set.subset_univ _) A hA hAF)
        (gammaNativePullbackForm A hA hAF ω hω)) := by
  let P := gammaPullbackAt (Set.subset_univ _) A hA hAF
  let e := gammaPullbackLiftIso (B := B) (Set.subset_univ _) A hA hAP
  let F := Section5.nativeGammaPointBijection (hc := hc) hA P.toGamma.lift_definable e
  have hF (p) : (F.map p).val.1 = p.val.1 := by
    rw [Section5.nativeGammaPointBijection_apply]
    dsimp only [e,gammaPullbackLiftIso]
    rw [gammaIso_congr_value]
    rfl
  have hlabel (p) : gammaNativeLiftLabel P (F.map p) = gammaNativePullbackKeyMap A hA hAF p := by
    apply Subtype.ext
    rw [gammaNativeLiftLabel_val,Section5.nativeGammaPointBijection_apply]
    dsimp only [e,gammaPullbackLiftIso]
    rw [gammaIso_congr_value]
    rfl
  apply gammaPositiveMeasuredHomOfBijection hκ hs hr hv F
  intro p hp
  refine ⟨1,gammaVFFixed_jacobian_one hκ hs hr hv F.map hF p hp,?_⟩
  rw [map_one,mul_one]
  change (gammaGroundFormValue ω p).val =
    (gammaGroundFormValue (gammaNativePullbackForm A hA hAF ω hω) (gammaNativeLiftLabel P (F.map p))).val
  rw [hlabel]
  exact congrArg (fun z => (cast (gammaCarrier hc) z.val).val)
    (gammaNativePullbackForm_apply A hA hAF ω hω p).symm

end DiamondIntegral.Section3
