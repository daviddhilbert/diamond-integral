import «section 3».GammaLastMeasuredGeometry
import «section 3».GammaUnaryGeometricFormulaWitnesses
import «section 3».GammaMeasuredElementaryFormulaWitnesses
import «section 3».GammaMeasuredObjectRowCoproducts

/-! Finite geometric proofs in every positive degree promote to finite formula witnesses, reusing the existing row promotion and last-coordinate formula proofs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gammaMeasured_geometry_formula_witness {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    {z : Fin p → M} {U V : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ (k+1)}
    (h : GammaLastMeasuredGeometry hκ hs h00 (small_union_range hκ B.real hr z) U V) :
    ∀ (F : GammaMeasuredRVSchema hc B p U.underlying.arity (k+1) sp)
      (G : GammaMeasuredRVSchema hc B p V.underlying.arity (k+1) sp),
      F.valid z → G.valid z → GammaMeasuredObjectRow z U F → GammaMeasuredObjectRow z V G →
      ∃ H : GammaMeasuredRelationSchema F G, H.valid z := by
  induction h with
  | @iso U V e =>
    intro F G hF hG rF rG
    obtain ⟨e⟩ := e
    exact gammaMeasured_object_rows_isomorphism_witness hκ hs hr hg z U V F G hF hG rF rG e.hom
  | elementary U hAd =>
    intro F G hF hG rF rG
    obtain ⟨L,A,hE,rE⟩ := gammaMeasured_elementary_formula_witness hκ hs h00 hr hg rF hF hAd
    let E := F.elementaryFormula.essential.withBound L
    obtain ⟨H,hH⟩ := gammaMeasured_object_rows_isomorphism_witness hκ hs hr hg z _ _ E G hE.2.1 hG rE rG
      (GammaGroundMeasuredRVHom.id _)
    exact ⟨.trans E (.elementary F L A) H,⟨hE,hH⟩⟩
  | symm h ih =>
    intro F G hF hG rF rG
    obtain ⟨H,hH⟩ := ih G F hG hF rG rF
    exact ⟨.symm H,hH⟩
  | @trans U E V h₁ h₂ ih₁ ih₂ =>
    intro F G hF hG rF rG
    obtain ⟨D,hD,rD⟩ := gammaMeasured_object_row_promotion hκ hs hr hg sp z hF.1.1 E
    obtain ⟨H,hH⟩ := ih₁ F D hF hD rF rD
    obtain ⟨K,hK⟩ := ih₂ D G hD hG rD rG
    exact ⟨.trans D H K,⟨hH,hK⟩⟩
  | @coprod U V X Y h₁ h₂ ih₁ ih₂ =>
    intro F G hF hG rF rG
    obtain ⟨FU,hFU,rFU⟩ := gammaMeasured_object_row_promotion hκ hs hr hg sp z hF.1.1 U
    obtain ⟨GV,hGV,rGV⟩ := gammaMeasured_object_row_promotion hκ hs hr hg sp z hF.1.1 V
    obtain ⟨FX,hFX,rFX⟩ := gammaMeasured_object_row_promotion hκ hs hr hg sp z hF.1.1 X
    obtain ⟨GY,hGY,rGY⟩ := gammaMeasured_object_row_promotion hκ hs hr hg sp z hF.1.1 Y
    obtain ⟨H,hH⟩ := ih₁ FU GV hFU hGV rFU rGV
    obtain ⟨K,hK⟩ := ih₂ FX GY hFX hGY rFX rGY
    obtain ⟨L,hL⟩ := FU.exists_valid_coprod_bound hκ hs hr hg FX z hFU hFX
    obtain ⟨R,hR⟩ := GV.exists_valid_coprod_bound hκ hs hr hg GY z hGV hGY
    let A := (FU.coprodFormula FX).withBound L
    let D := (GV.coprodFormula GY).withBound R
    have rA : GammaMeasuredObjectRow z (U.coprod X) A := rFU.coprod hF.1.1 rFX L
    have rD : GammaMeasuredObjectRow z (V.coprod Y) D := rGV.coprod hF.1.1 rGY R
    obtain ⟨HLeft,hLeft⟩ := gammaMeasured_object_rows_isomorphism_witness hκ hs hr hg z _ _ F A hF hL rF rA
      (GammaGroundMeasuredRVHom.id _)
    obtain ⟨HRight,hRight⟩ := gammaMeasured_object_rows_isomorphism_witness hκ hs hr hg z _ _ D G hR hG rD rG
      (GammaGroundMeasuredRVHom.id _)
    exact ⟨.trans A HLeft (.trans D (.coprod H K L R) HRight),⟨hLeft,⟨⟨hH,hK,hL,hR⟩,hRight⟩⟩⟩

end DiamondIntegral.Section3
