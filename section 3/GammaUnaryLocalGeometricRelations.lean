import «section 3».GammaMeasuredGeometricRelations
import «section 3».GammaNativeElementaryLocalComparison

/-! Unary geometric proofs may use the literal local measured
elementary operation. Their extraction reuses the checked native unary
proof and the actual comparison of its elementary product charts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

inductive GammaUnaryMeasuredGeometry
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) :
    GammaGroundMeasuredRVObject hc B 1 → GammaGroundMeasuredRVObject hc B 1 → Prop
  | iso {U V} : Nonempty (U ≅ V) → GammaUnaryMeasuredGeometry hκ hs h00 hr U V
  | elementary (U : GammaGroundMeasuredRVObject hc B 1)
      (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject 0) :
      GammaUnaryMeasuredGeometry hκ hs h00 hr U (gammaMeasuredElementaryObject hκ hs h00 hr U 0 hAd)
  | symm {U V} : GammaUnaryMeasuredGeometry hκ hs h00 hr U V → GammaUnaryMeasuredGeometry hκ hs h00 hr V U
  | trans {U V W} : GammaUnaryMeasuredGeometry hκ hs h00 hr U V →
      GammaUnaryMeasuredGeometry hκ hs h00 hr V W → GammaUnaryMeasuredGeometry hκ hs h00 hr U W
  | coprod {U V X Y} : GammaUnaryMeasuredGeometry hκ hs h00 hr U V →
      GammaUnaryMeasuredGeometry hκ hs h00 hr X Y → GammaUnaryMeasuredGeometry hκ hs h00 hr (U.coprod X) (V.coprod Y)

theorem gammaUnaryMeasuredGeometry_of_native
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {h00 : M ⊨ Axioms.ACVF00} {hr : Cardinal.mk B.real < κ}
    {U V : GammaGroundMeasuredRVObject hc B 1} (h : GammaMeasuredGeometricRelation hκ hs h00 hr U V) :
    GammaUnaryMeasuredGeometry hκ hs h00 hr U V := by
  induction h with
  | iso h => exact .iso h
  | elementary A ω i hAd =>
    have hi : i = 0 := by
      apply Fin.ext
      have hiBound := i.isLt
      omega
    subst i
    let hFull := gammaUnaryAdmissible_full A hAd
    let P : GammaGroundMeasuredRVObject hc B 1 := ⟨Section5.nativeRVGroundObject A hFull,ω⟩
    let hAP := gammaNativeGround_admissible (hc := hc) A hFull 0 hAd
    obtain ⟨f⟩ := gammaNativeElementary_local_measured_hom hκ hs h00 hr A hFull ω 0 hAd
    have hSource : GammaUnaryMeasuredGeometry hκ hs h00 hr (gammaNativeMeasuredNormalization A ω) P :=
      .iso ⟨(asIso (show P ⟶ gammaNativeMeasuredNormalization A ω from gammaNativeFullWeightNormalizationHom A hFull ω)).symm⟩
    have hTarget : GammaUnaryMeasuredGeometry hκ hs h00 hr (gammaMeasuredElementaryObject hκ hs h00 hr P 0 hAP)
        (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr A 0 hAd)
          (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr A 0 hAd))) := .iso ⟨(asIso f).symm⟩
    exact hSource.trans ((GammaUnaryMeasuredGeometry.elementary P hAP).trans hTarget)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | coprod h₁ h₂ ih₁ ih₂ => exact ih₁.coprod ih₂

theorem gammaNativeUnaryFullMeasured_local_geometry
    [CharZero (Section2.VF M)]
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (U V : GammaObjectAt B Set.univ 1)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η)) :
    GammaUnaryMeasuredGeometry hκ.le hs h00 hr (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) :=
  gammaUnaryMeasuredGeometry_of_native
    (gammaNativeUnaryFullMeasured_geometric_relation hκ hs h00 hr hv δ hδ hδ1 FBase U V ω η f)

end DiamondIntegral.Section3
