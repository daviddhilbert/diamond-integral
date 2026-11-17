import «section 3».GammaGroundUnaryOriginalBaseKernel
import «section 3».GammaUnaryGeometricFormulaWitnesses

/-! Full measured comparisons of unary lift rows supply finite original-
base formula proofs. Both real and Gamma smallness are retained explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasured_unary_full_lift_row_witness
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (z : Fin p → M)
    (U V : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ 1)
    (F : GammaMeasuredRVSchema hc B p U.underlying.arity 1 sp)
    (E : GammaMeasuredRVSchema hc B p V.underlying.arity 1 sp)
    (hF : F.valid z) (hE : E.valid z)
    (rF : GammaMeasuredObjectRow z U F) (rE : GammaMeasuredObjectRow z V E)
    (f : GammaFullMeasuredBijection (gammaGroundMeasuredObjectLift U) (gammaGroundMeasuredObjectLift V)) :
    ∃ H : GammaMeasuredRelationSchema F E, H.valid z :=
  gammaUnary_geometry_formula_witness hκ.le hs h00 hr hg
    (gammaGroundUnaryFullMeasured_original_base_geometry (B := ⟨B.real ∪ Set.range z,B.gamma⟩) hκ hs h00
      (small_union_range hκ.le B.real hr z) hv δ hδ hδ1 U V f)
    F E hF hE rF rE

end DiamondIntegral.Section3
