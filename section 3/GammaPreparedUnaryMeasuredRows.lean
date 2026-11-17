import «section 3».GammaPartialBaseNormalForm
import «section 3».GammaMeasuredRowAgreements
import «section 3».GammaPreparedIndexAttachments
import «section 5».NativeSpecialBaseBridge
import Integration7.GammaPreparedVolumeRows
import IntegrationSection6.GammaPreparedIndexValues

/-! The unary prepared-family rows used in the RV-density proof,
with complete Gamma density graphs. Only the actual source-row and
density identities are required; the source can be a mixed domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {k l a : ℕ}
variable (F : GammaMeasuredRVSchema hc B 1 a (k+1) (fun _ => .vf))
variable {X : DefSet (M := M) S 1 0} {Z : DefSet (M := M) S 1 l}
variable (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
variable (hAgreement : ∀ c : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement
  F.toRVTemplate (rawVFParameter (T.inverseMap c).val) (rawPreparedKey c.val))
variable (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (1+(k+1)) a))
variable (hP : ∀ q : A,
  ((Section5.nativeMixedCoordinateMap _ (Fin.castAdd (k+1)) (Fin.elim0 : Fin 0 → Fin a)) q).val ∈
    (Section5.nativeGammaPointDomain (hc := hc) (carrier X) (GammaChainDefinable.source B T.chain hT)).carrier)

include hAgreement in
theorem gammaPreparedUnaryMeasured_valid (hF : ∀ x : Fin 1 → VF (M := M), F.valid (vfValues x)) :
    ∀ t ∈ preparedKeyDomain Z, (F.recode (GammaParameterRecode.prepared T hT)).valid (rvValues t) := by
  rintro t ⟨c,rfl⟩
  exact F.recode_valid (GammaParameterRecode.prepared T hT) _ _
    (fun j => ((flatKey c.val).2 j).property) (hAgreement c) (hF (T.inverseMap c).val.1)

include hAgreement in
theorem gammaPreparedUnaryMeasured_rows
    (hSource : ∀ (x : Fin 1 → Section2.VF M) (y : Fin (k+1) → Section2.VF M) (r : Fin a → RV (M := M)),
      (Fin.append x y,r) ∈ A.carrier ↔ F.object.rowVolume (vfValues x) r (Section2.tupleRV M y))
    (c : Z) (y : Fin (k+1) → Section2.VF M) (r : Fin a → RV (M := M)) :
    (Fin.append c.val.1 y,Fin.append c.val.2 r) ∈
        (Section5.nativeVFPrepareBaseMap A (Section5.nativeSpecialBaseBijection T hT) hP).image.carrier ↔
      (F.recode (GammaParameterRecode.prepared T hT)).object.rowVolume
        (rawPreparedKey c.val) r (Section2.tupleRV M y) := by
  let cN : Section5.nativeGammaPointDomain (hc := hc) (carrier Z) (GammaChainDefinable.target B T.chain hT) := ⟨c.val,c.property⟩
  have hNormal := gammaPartialBase_normalForm A (Section5.nativeSpecialBaseBijection T hT) hP cN y r
  rw [Section5.nativeSpecialBaseBijection_inverse] at hNormal
  have hRows := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows F.toRVTemplate _ _ (hAgreement c)
  exact hNormal.trans ((hSource (T.inverseMap c).val.1 y r).trans
    (hRows.1.2 (rvValues r) (rvValues (Section2.tupleRV M y))))

include hAgreement in
theorem gammaPreparedUnaryMeasured_density
    (Ω : GammaGroundVolumeForm hc B A)
    (hDensity : ∀ (p : A) (cΓ : (volumeGammaSpace hc).domain), (volumeGammaSpace hc).decode cΓ = (Ω p).val →
      F.rowDensity (vfValues (p.val.1 ∘ Fin.castAdd (k+1))) p.val.2 cΓ)
    (q : (Section5.nativeVFPrepareBaseMap A (Section5.nativeSpecialBaseBijection T hT) hP).image)
    (cΓ : (volumeGammaSpace hc).domain)
    (hcValue : (volumeGammaSpace hc).decode cΓ =
      ((Ω.comp (Section5.nativeVFPrepareBaseBijection A (Section5.nativeSpecialBaseBijection T hT) hP).symm.map) q).val) :
    (F.recode (GammaParameterRecode.prepared T hT)).rowDensity
      (rvValues (indexedLeft (gammaPreparedIndexAttachment _ q).val.2))
      (indexedRight (gammaPreparedIndexAttachment _ q).val.2) cΓ := by
  let TΓ := Section5.nativeSpecialBaseBijection (hc := hc) T hT
  let W := Section5.nativeVFPrepareBaseBijection A TΓ hP
  let p := W.symm.map q
  let c : Z := ⟨(q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.castAdd a),gammaPartialBase_base_mem A TΓ hP q⟩
  have hBase := gammaPartialBase_inverse_basepoint A TΓ hP q
  change (TΓ.symm.map ⟨c.val,c.property⟩).val.1 = p.val.1 ∘ Fin.castAdd (k+1) at hBase
  rw [Section5.nativeSpecialBaseBijection_inverse] at hBase
  have hOld := gammaPartialBase_inverse_labels A TΓ hP q
  have hSource : F.rowDensity (rawVFParameter (T.inverseMap c).val) (q.val.2 ∘ Fin.natAdd l) cΓ := by
    change F.rowDensity (vfValues (T.inverseMap c).val.1) (q.val.2 ∘ Fin.natAdd l) cΓ
    rw [hBase,← hOld]
    exact hDensity p cΓ hcValue
  have hRows := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows F.toRVTemplate _ _ (hAgreement c)
  have hTarget := (hRows.density (q.val.2 ∘ Fin.natAdd l) (gammaVolumeCodeRV cΓ)).mp hSource
  rw [gammaPreparedIndexAttachment_value]
  simp only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
  exact hTarget

end DiamondIntegral.Section3
