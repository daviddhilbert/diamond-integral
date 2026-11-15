import «section 5».RVRectanglePieceSchemata
import «section 5».RawRVRectangleDecomposition
import «section 5».OriginalGammaRVRowPresentations
import «section 5».OriginalFixedRVBijectionPromotion
import «section 5».NativeSchemaPresentations
import «section 5».NativeUnitRESObjects

/-! Every actual RV rectangle at a mixed parameter promotes to a whole
valid original-base package, including the actual product map graph and
an entire original Euler certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}

theorem rv_rectangle_piece_schema_at_parameter
    (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {X : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) a)}
    (C : RawRVRectangle X) :
    ∃ F : RVRectanglePieceSchema B p a sp, F.Valid hc z ∧
      {v | Fin.append z v ∈ F.source.val} = rawDomain C.source := by
  obtain ⟨D,hD,_⟩ := original_rv_domain_at_parameter hc B sp z hz C.source
  let U := nativeRESObjectOfUnitSet C.residue C.residue_finite
  obtain ⟨R,hR,hRrow,_⟩ := native_res_schema_at_parameter B sp z hz U
  obtain ⟨G,E,hG,hE,_⟩ := original_euler_certificate_exists hc h00 hκ hs B hr hγ sp z hz C.gamma.carrier
    (Section3GammaChartBridge.chart C.gamma).support_definable
  let Z := gammaGroundRVProductDomain U.obj.domain (gammaGroundGammaRVCodeLift C.gamma).domain
  let e : GammaGroundBijection C.source Z :=
    (gammaGroundRVPackBijection _ _).comp
      (((nativeRESUnitSetBijection C.residue C.residue_finite).prodMap
        (gammaGroundRVUnitGammaCodeBijection C.gamma)).comp C.bijection)
  have hZ : {v | Fin.append z v ∈ (originalDomainProduct R.domain G).val} = rawDomain Z :=
    originalDomainProduct_presents_rawProduct R.domain G z U.obj.domain (gammaGroundGammaRVCodeLift C.gamma).domain
      hRrow (originalGammaRVRow_raw G z C.gamma hG)
  obtain ⟨H,hH⟩ := original_fixed_rv_bijection_schema_at_parameter hc B sp z hz D
    (originalDomainProduct R.domain G) C.source Z hD hZ e
  let F : RVRectanglePieceSchema B p a sp := ⟨D,C.residueArity,C.freeArity,R,G,E,H⟩
  exact ⟨F,⟨hR,hE,hH⟩,hD⟩

end DiamondIntegral.Section5
