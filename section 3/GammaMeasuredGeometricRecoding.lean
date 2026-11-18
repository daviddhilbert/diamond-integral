import «section 3».GammaMeasuredIsomorphismRecoding
import «section 3».GammaMeasuredOperationRowAgreements

/-! Recode a finite geometric proof using the existing formula recoder.
Exact-row comparison steps account for the order of recoding and the
native coproduct, elementary, and essential operations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaMeasuredRelationSchema.recode (C : GammaParameterRecode B p q sp sq) :
    {a b : ℕ} → {F : GammaMeasuredRVSchema hc B p a (k+1) sp} →
      {G : GammaMeasuredRVSchema hc B p b (k+1) sp} → GammaMeasuredRelationSchema F G →
        GammaMeasuredRelationSchema (F.recode C) (G.recode C)
  | _,_,_,_,.iso I => .iso (I.recode C)
  | _,_,_,_,.agreement F G => .agreement (F.recode C) (G.recode C)
  | _,_,_,_,.elementary F N A =>
      .trans ((F.recode C).elementaryFormula.essential.withBound N) (.elementary (F.recode C) N A)
        (.agreement ((F.recode C).elementaryFormula.essential.withBound N)
          ((F.elementaryFormula.essential.withBound N).recode C))
  | _,_,_,_,.symm H => .symm (H.recode C)
  | _,_,_,_,.trans E H K => .trans (E.recode C) (H.recode C) (K.recode C)
  | _,_,_,_,.coprod (F := F) (G := G) (E := E) (D := D) H K N L =>
      .trans (((F.recode C).coprodFormula (E.recode C)).withBound N)
        (.agreement (((F.coprodFormula E).withBound N).recode C)
          (((F.recode C).coprodFormula (E.recode C)).withBound N))
        (.trans (((G.recode C).coprodFormula (D.recode C)).withBound L)
          (.coprod (H.recode C) (K.recode C) N L)
          (.agreement (((G.recode C).coprodFormula (D.recode C)).withBound L)
            (((G.coprodFormula D).withBound L).recode C)))

def GammaMeasuredRelationSchema.RecodeAgreement (C : GammaParameterRecode B p q sp sq) :
    {a b : ℕ} → {F : GammaMeasuredRVSchema hc B p a (k+1) sp} →
      {G : GammaMeasuredRVSchema hc B p b (k+1) sp} → GammaMeasuredRelationSchema F G →
        (Fin p → M) → (Fin q → M) → Prop
  | _,_,_,_,.iso I,z,t =>
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement I.source.toRVTemplate z t ∧
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement I.target.toRVTemplate z t ∧
      C.RelationAgreement ⟨I.chart,I.chart_definable⟩ z t
  | _,_,_,_,.agreement F G,z,t =>
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement F.toRVTemplate z t ∧
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement G.toRVTemplate z t ∧ True
  | _,_,_,_,.elementary F N A,z,t =>
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement F.toRVTemplate z t ∧
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement (F.elementaryFormula.essential.withBound N).toRVTemplate z t ∧ True
  | _,_,_,_,.symm (F := F) (G := G) H,z,t =>
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement G.toRVTemplate z t ∧
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement F.toRVTemplate z t ∧ H.RecodeAgreement C z t
  | _,_,_,_,.trans (F := F) (G := G) _ H K,z,t =>
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement F.toRVTemplate z t ∧
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement G.toRVTemplate z t ∧
        H.RecodeAgreement C z t ∧ K.RecodeAgreement C z t
  | _,_,_,_,.coprod (F := F) (G := G) (E := E) (D := D) H K N L,z,t =>
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement ((F.coprodFormula E).withBound N).toRVTemplate z t ∧
      (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement ((G.coprodFormula D).withBound L).toRVTemplate z t ∧
        H.RecodeAgreement C z t ∧ K.RecodeAgreement C z t

theorem GammaMeasuredRelationSchema.recode_source_agreement
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B p b (k+1) sp}
    (H : GammaMeasuredRelationSchema F G) (C : GammaParameterRecode B p q sp sq)
    (z : Fin p → M) (t : Fin q → M) (h : H.RecodeAgreement C z t) :
    (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement F.toRVTemplate z t := by
  cases H <;> exact h.1

theorem GammaMeasuredRelationSchema.recode_target_agreement
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B p b (k+1) sp}
    (H : GammaMeasuredRelationSchema F G) (C : GammaParameterRecode B p q sp sq)
    (z : Fin p → M) (t : Fin q → M) (h : H.RecodeAgreement C z t) :
    (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement G.toRVTemplate z t := by
  cases H <;> exact h.2.1

theorem GammaMeasuredRelationSchema.valid_endpoints
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B p b (k+1) sp}
    (H : GammaMeasuredRelationSchema F G) {z : Fin p → M} (h : H.valid z) : F.valid z ∧ G.valid z := by
  induction H with
  | iso I => exact ⟨h.1,h.2.1⟩
  | agreement F G => exact ⟨h.1,h.2.1⟩
  | elementary F N A => exact ⟨h.1,h.2.1⟩
  | symm H ih => exact (ih h).symm
  | trans E H K ihH ihK => exact ⟨(ihH h.1).1,(ihK h.2).2⟩
  | coprod H K N L ihH ihK => exact ⟨h.2.2.1,h.2.2.2⟩

end DiamondIntegral.Section3
