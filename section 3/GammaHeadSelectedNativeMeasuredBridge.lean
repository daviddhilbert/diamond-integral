import «section 3».GammaHeadSelectedLiftCarriers
import «section 3».GammaHeadLiftForms
import «section 3».GammaSelectedVFTailMeasuredMaps

/-! The full selected native object of a unary head contraction carries
exactly its original retained Gamma density. Its comparison with the
canonical selected VF-tail realization is coordinatewise identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {a k : ℕ} {A : DefSet (M := M) Set.univ 1 a}
variable (T : HeadPreparation A) (ρ : Fin k → Fin a)
variable (P : GammaFiniteGraphPresentation B (1+T.arity) (1+k)
  {r | (Fin.elim0,r) ∈ carrier T.contractedSet}
  (fun r y => (Fin.elim0,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T ρ = y))
variable (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (hLabels : ∀ p : A, p.val.2 ∈ Q.carrier)

def gammaHeadSelectedNativeOldLabels :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) Q :=
  (gammaGroundRVSelectCoordinates (headSelectedLabelIndex T (id : Fin a → Fin a))
    (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma))).corestrict (fun u => by
      have hm := P.domain_eq.le ((Section5.nativeRVGroundDomain_carrier _).le u.property)
      exact gammaHeadContractedLabels_mem T Q hLabels ⟨(Fin.elim0,u.val),hm⟩)

def gammaHeadSelectedNativeForm (ω : GammaGroundVolumeForm hc B Q) :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :=
  ω.comp (gammaHeadSelectedNativeOldLabels T ρ P Q hLabels)

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaHeadSelectedNativeFullMeasuredBridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hTarget : GammaSetDefinable B (carrier T.target))
    (hfinH : ∀ x t, {r | (x,r) ∈ carrier T.liftSet ∧ r ∘ headSelectedLabelIndex T ρ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B Q) :
    GammaFullMeasuredBijection
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaHeadSelectedNativeForm T ρ P Q hLabels ω))
      (gammaSelectedVFTailMeasuredData T.liftSet (headSelectedLabelIndex T ρ)
        (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH (gammaHeadLiftForm T hTarget Q hLabels ω)) := by
  let U := gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaHeadSelectedNativeForm T ρ P Q hLabels ω)
  let V := gammaSelectedVFTailMeasuredData T.liftSet (headSelectedLabelIndex T ρ)
    (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH (gammaHeadLiftForm T hTarget Q hLabels ω)
  let e : GammaGroundBijection U.domain V.domain := GammaGroundBijection.ofCarrierEq (gammaHeadSelectedLift_carrier T ρ P)
  exact gammaFullMeasuredFixedVF hκ hs hr hv e (fun _ => rfl) (fun _ => rfl)

theorem gammaHeadSelectedNativeFullMeasuredBridge_value
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hTarget : GammaSetDefinable B (carrier T.target))
    (hfinH : ∀ x t, {r | (x,r) ∈ carrier T.liftSet ∧ r ∘ headSelectedLabelIndex T ρ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B Q) (p) :
    ((gammaHeadSelectedNativeFullMeasuredBridge T ρ P Q hLabels hκ hs hr hv hTarget hfinH ω).map.map p).val = p.val := rfl

end DiamondIntegral.Section3
