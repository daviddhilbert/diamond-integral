import «section 3».GammaMeasuredNormalizationRows
import «section 3».GammaUnaryOriginalBaseGeometry
import «section 3».GammaUnaryGeometricFormulaWitnesses

/-! Unary full-lift comparisons promote to first-order finite proofs
for their essential measured rows, including native zero strata. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasured_unary_native_lift_row_witness
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (z : Fin p → M)
    (U V : GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ Set.univ 1)
    (ω : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (Section5.nativeRVGroundDomain V))
    (F : GammaMeasuredRVSchema hc B p (rvObjectArity U.object.obj) 1 sp)
    (E : GammaMeasuredRVSchema hc B p (rvObjectArity V.object.obj) 1 sp)
    (hF : F.valid z) (hE : E.valid z)
    (hVF : ∀ x y, F.object.rowVolume z x y ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val = x ∧ (Section5.nativeRVGroundVolume U u).val = y)
    (hVE : ∀ x y, E.object.rowVolume z x y ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) V, u.val = x ∧ (Section5.nativeRVGroundVolume V u).val = y)
    (hDF : ∀ x c, F.rowDensity z x c ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val = x ∧ (ω u).val = (volumeGammaSpace hc).decode c)
    (hDE : ∀ x c, E.rowDensity z x c ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) V, u.val = x ∧ (η u).val = (volumeGammaSpace hc).decode c)
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η)) :
    ∃ H : GammaMeasuredRelationSchema F.essential E.essential, H.valid z := by
  have hGeom := gammaNativeUnaryFullMeasured_original_base_geometry
    (B := ⟨B.real ∪ Set.range z,B.gamma⟩) hκ hs h00 (small_union_range hκ.le B.real hr z)
    hv δ hδ hδ1 U V ω η f
  exact gammaUnary_geometry_formula_witness hκ.le hs h00 hr hg hGeom F.essential E.essential
    (F.essential_valid z hF) (E.essential_valid z hE)
    (gammaMeasured_normalization_row z U ω F hVF hDF)
    (gammaMeasured_normalization_row z V η E hVE hDE)

end DiamondIntegral.Section3
