import «section 3».GammaMeasuredGeometricRecoding

/-! Exact primitive agreement transports validity through every finite
geometric proof. All operation and chart row transports are reused from
the checked native formula machinery. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem GammaMeasuredRelationSchema.recode_valid
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B p b (k+1) sp}
    (H : GammaMeasuredRelationSchema F G) (C : GammaParameterRecode B p q sp sq)
    (z : Fin p → M) (t : Fin q → M) (ht : ∀ i, sortEval (sq i) (t i))
    (hA : H.RecodeAgreement C z t) (hV : H.valid z) : (H.recode C).valid t := by
  induction H with
  | iso I => exact I.recode_valid C z t ht hA hV
  | agreement F G =>
    have hS := (GammaVolumeParameterRecode.mk C).volumeObject_rows F.toRVTemplate z t hA.1
    have hT := (GammaVolumeParameterRecode.mk C).volumeObject_rows G.toRVTemplate z t hA.2.1
    exact ⟨F.recode_valid C z t ht hA.1 hV.1,G.recode_valid C z t ht hA.2.1 hV.2.1,
      gammaVolumeSameRow_of_agreement ht hS hT hV.2.2⟩
  | elementary F N A =>
    let E := F.elementaryFormula.essential.withBound N
    let D := (F.recode C).elementaryFormula.essential.withBound N
    have hz := hV.1.1.1
    have hSource := (GammaVolumeParameterRecode.mk C).volumeObject_rows F.toRVTemplate z t hA.1
    have hRecoded := (GammaVolumeParameterRecode.mk C).volumeObject_rows E.toRVTemplate z t hA.2.1
    have hCanonical := gammaMeasured_rowAgreement_withBound
      (F := F.elementaryFormula.essential) (G := (F.recode C).elementaryFormula.essential)
      (gammaMeasured_rowAgreement_essential (F := F.elementaryFormula)
        (G := (F.recode C).elementaryFormula) (hSource.elementary hz ht)) N N
    have hD : D.valid t := gammaMeasured_rowAgreement_valid hCanonical ht rfl hV.2.1
    have hE : (E.recode C).valid t := E.recode_valid C z t ht hA.2.1 hV.2.1
    let AD : GammaFiniteAdmissibilitySchema B q _ (k+1) sq := ⟨(F.recode C).object,Fin.last k,A⟩
    have hAD : AD.valid t := (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) A).valid_of_rowAgreement AD
      z t ht rfl rfl rfl hSource.1 hV.2.2
    exact ⟨⟨F.recode_valid C z t ht hA.1 hV.1,hD,hAD⟩,
      ⟨hD,hE,gammaMeasured_sameRow_of_agreements hz ht hCanonical hRecoded⟩⟩
  | symm H ih => exact ih hA.2.2 hV
  | trans E H K ihH ihK => exact ⟨ihH hA.2.2.1 hV.1,ihK hA.2.2.2 hV.2⟩
  | @coprod a b c d F G E D H K N L ihH ihK =>
    let S := (F.coprodFormula E).withBound N
    let T := (G.coprodFormula D).withBound L
    let S' := ((F.recode C).coprodFormula (E.recode C)).withBound N
    let T' := ((G.recode C).coprodFormula (D.recode C)).withBound L
    have hz := hV.2.2.1.1.1
    have hF := (GammaVolumeParameterRecode.mk C).volumeObject_rows F.toRVTemplate z t
      (H.recode_source_agreement C z t hA.2.2.1)
    have hG := (GammaVolumeParameterRecode.mk C).volumeObject_rows G.toRVTemplate z t
      (H.recode_target_agreement C z t hA.2.2.1)
    have hE := (GammaVolumeParameterRecode.mk C).volumeObject_rows E.toRVTemplate z t
      (K.recode_source_agreement C z t hA.2.2.2)
    have hD := (GammaVolumeParameterRecode.mk C).volumeObject_rows D.toRVTemplate z t
      (K.recode_target_agreement C z t hA.2.2.2)
    have hSC := gammaMeasured_rowAgreement_withBound (F := F.coprodFormula E)
      (G := (F.recode C).coprodFormula (E.recode C)) (hF.coprod hE hz ht) N N
    have hTC := gammaMeasured_rowAgreement_withBound (F := G.coprodFormula D)
      (G := (G.recode C).coprodFormula (D.recode C)) (hG.coprod hD hz ht) L L
    have hSR := (GammaVolumeParameterRecode.mk C).volumeObject_rows S.toRVTemplate z t hA.1
    have hTR := (GammaVolumeParameterRecode.mk C).volumeObject_rows T.toRVTemplate z t hA.2.1
    have hS' : S'.valid t := gammaMeasured_rowAgreement_valid hSC ht rfl hV.2.2.1
    have hT' : T'.valid t := gammaMeasured_rowAgreement_valid hTC ht rfl hV.2.2.2
    have hS : (S.recode C).valid t := S.recode_valid C z t ht hA.1 hV.2.2.1
    have hT : (T.recode C).valid t := T.recode_valid C z t ht hA.2.1 hV.2.2.2
    exact ⟨⟨hS,hS',gammaMeasured_sameRow_of_agreements hz ht hSR hSC⟩,
      ⟨⟨ihH hA.2.2.1 hV.1,ihK hA.2.2.2 hV.2.1,hS',hT'⟩,
        ⟨hT',hT,gammaMeasured_sameRow_of_agreements hz ht hTC hTR⟩⟩⟩

end DiamondIntegral.Section3
