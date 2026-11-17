import «section 3».GammaHeadRawRowLiftDomains
import «section 3».GammaHeadLiftForms
import «section 3».GammaMixedRVFibres

/-! A raw head RV row with its actual Gamma form lifts identically to
the frozen canonical fibre with the pulled-back contracted form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a}
variable (T : HeadPreparation U) (hTarget : GammaSetDefinable B (carrier T.target))
variable (x : Fin n → VF (M := M))
variable (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x)

def gammaHeadRawRowLabels :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma))
      (gammaMixedRVFibreDomain (Section5.nativeGammaPointDomain (carrier T.contractedSet) (gamma_headImage T.target hTarget)) x) :=
  GammaGroundMap.inclusion (fun r hr => P.domain_eq.le ((Section5.nativeRVGroundDomain_carrier _).le hr))

def gammaHeadRawRowForm
    (σ : GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier T.contractedSet) (gamma_headImage T.target hTarget))) :
    GammaGroundVolumeForm hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
      (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :=
  (gammaMixedRVFibreForm σ x).comp (gammaHeadRawRowLabels T hTarget x P)

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaHeadRawRowFullMeasuredBridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ y z : Section2.VF M, VFValued.predV y z ↔ Valued.v y ≤ Valued.v z)
    (hfinH : ∀ y, {r | (y,r) ∈ carrier T.liftSet}.Finite)
    (σ : GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier T.contractedSet) (gamma_headImage T.target hTarget))) :
    GammaFullMeasuredBijection
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaHeadRawRowForm T hTarget x P σ))
      (gammaHeadMeasuredFibre T.liftSet (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH
        (σ.comp (gammaHeadLiftDrop T hTarget)) x) := by
  let A := gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaHeadRawRowForm T hTarget x P σ)
  let D := gammaHeadMeasuredFibre T.liftSet (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH
    (σ.comp (gammaHeadLiftDrop T hTarget)) x
  let E : GammaGroundBijection A.domain D.domain :=
    GammaGroundBijection.ofCarrierEq (gammaHeadRawRowLift_coordinate_carrier T x P)
  apply gammaFullMeasuredFixedVF (B := ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩)
    hκ hs (small_union_range hκ B.real hr (vfValues x)) hv E (fun _ => rfl)
  intro p
  let r := gammaHeadRawRowLabels T hTarget x P (gammaNativeLiftLabel (gammaUniversalObject P.toGamma) p)
  let u := gammaMixedRVFibreInclusion
    (Section5.nativeGammaPointDomain (hc := hc) (carrier T.contractedSet) (gamma_headImage T.target hTarget)) x r
  let v := gammaHeadLiftDrop (hc := hc) T hTarget
    (gammaHeadFibreInclusion T.liftSet (gamma_coordinateCanonicalImage T.target hTarget 0) x (E.map p))
  change (gammaGroundFormValue σ u).val = (gammaGroundFormValue σ v).val
  have huv : u = v := Subtype.ext rfl
  exact congrArg (fun q => (gammaGroundFormValue σ q).val) huv

end DiamondIntegral.Section3
