import «section 3».GammaUnaryGeometricDerivations

/-! Finite geometric derivations can be expressed using actual objects,
actual measured isomorphisms, elementary steps, and tagged disjoint unions.
The conversion reuses the checked positive class representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

inductive GammaMeasuredGeometricRelation
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) :
    GammaGroundMeasuredRVObject hc B (n+1) → GammaGroundMeasuredRVObject hc B (n+1) → Prop
  | iso {U V} : Nonempty (U ≅ V) → GammaMeasuredGeometricRelation hκ hs h00 hr U V
  | elementary (U : GammaObjectAt B Set.univ (n+1))
      (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
      (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
      GammaMeasuredGeometricRelation hκ hs h00 hr
        (gammaNativeMeasuredNormalization U ω)
        (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U i hAd)
          (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)))
  | symm {U V} : GammaMeasuredGeometricRelation hκ hs h00 hr U V →
      GammaMeasuredGeometricRelation hκ hs h00 hr V U
  | trans {U V W} : GammaMeasuredGeometricRelation hκ hs h00 hr U V →
      GammaMeasuredGeometricRelation hκ hs h00 hr V W →
      GammaMeasuredGeometricRelation hκ hs h00 hr U W
  | coprod {U V X Y} : GammaMeasuredGeometricRelation hκ hs h00 hr U V →
      GammaMeasuredGeometricRelation hκ hs h00 hr X Y →
      GammaMeasuredGeometricRelation hκ hs h00 hr (U.coprod X) (V.coprod Y)

theorem gammaMeasuredGeometricRelation_of_additive_derivation
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {h00 : M ⊨ Axioms.ACVF00} {hr : Cardinal.mk B.real < κ}
    {x y : GammaGroundMeasuredRVKPlus hc B (n+1)}
    (h : AddConGen.Rel (GammaNativeElementaryStep hκ hs h00 hr) x y) :
    ∀ (U V : GammaGroundMeasuredRVObject hc B (n+1)),
      gammaGroundMeasuredRVClass U = x → gammaGroundMeasuredRVClass V = y →
      GammaMeasuredGeometricRelation hκ hs h00 hr U V := by
  induction h with
  | of x y h =>
    cases h with
    | elementary A ω i hAd =>
      intro U V hU hV
      exact (GammaMeasuredGeometricRelation.iso (gammaGroundMeasuredRVClass_eq_iff_iso.mp hU)).trans
        ((GammaMeasuredGeometricRelation.elementary A ω i hAd).trans (GammaMeasuredGeometricRelation.iso (gammaGroundMeasuredRVClass_eq_iff_iso.mp hV.symm)))
  | refl x =>
    intro U V hU hV
    exact .iso (gammaGroundMeasuredRVClass_eq_iff_iso.mp (hU.trans hV.symm))
  | symm h ih =>
    intro U V hU hV
    exact (ih V U hV hU).symm
  | @trans x y z h₁ h₂ ih₁ ih₂ =>
    intro U V hU hV
    obtain ⟨W,hW⟩ := gammaGroundMeasuredRVClass_surjective y
    exact (ih₁ U W hU hW).trans (ih₂ W V hW hV)
  | @add w x y z h₁ h₂ ih₁ ih₂ =>
    intro U V hU hV
    obtain ⟨A,hA⟩ := gammaGroundMeasuredRVClass_surjective w
    obtain ⟨B,hB⟩ := gammaGroundMeasuredRVClass_surjective x
    obtain ⟨C,hC⟩ := gammaGroundMeasuredRVClass_surjective y
    obtain ⟨D,hD⟩ := gammaGroundMeasuredRVClass_surjective z
    have hAC := (gammaGroundMeasuredRVClass_coprod A C).trans (congrArg₂ (· + ·) hA hC)
    have hBD := (gammaGroundMeasuredRVClass_coprod B D).trans (congrArg₂ (· + ·) hB hD)
    exact (GammaMeasuredGeometricRelation.iso (gammaGroundMeasuredRVClass_eq_iff_iso.mp (hU.trans hAC.symm))).trans
      (((ih₁ A B hA hB).coprod (ih₂ C D hC hD)).trans
        (GammaMeasuredGeometricRelation.iso (gammaGroundMeasuredRVClass_eq_iff_iso.mp (hBD.trans hV.symm))))

theorem gammaNativeUnaryFullMeasured_geometric_relation
    [CharZero (Section2.VF M)]
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase B.real)
    (U V : GammaObjectAt B Set.univ 1)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η)) :
    GammaMeasuredGeometricRelation hκ.le hs h00 hr
      (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) :=
  gammaMeasuredGeometricRelation_of_additive_derivation
    (gammaNativeUnaryFullMeasured_geometric_derivation hκ hs h00 hr hv δ hδ hδ1 FBase U V ω η f) _ _ rfl rfl

end DiamondIntegral.Section3
