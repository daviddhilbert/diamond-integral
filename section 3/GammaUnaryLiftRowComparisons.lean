import «section 3».GammaMeasuredRawRowForms
import «section 3».GammaUnaryNativeRowWitnesses

/-! Actual full measured comparisons of raw unary row lifts imply finite
formula witnesses for their essential rows, over the original base. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaUnaryMeasuredRowLiftComparison
    (F : GammaMeasuredRVSchema hc B p a 1 sp) (E : GammaMeasuredRVSchema hc B p b 1 sp) (z : Fin p → M) : Prop :=
  ∃ hF : F.valid z, ∃ hE : E.valid z,
    ∃ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a 1 (F.object.rowDomain z) (F.object.rowVolume z),
    ∃ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b 1 (E.object.rowDomain z) (E.object.rowVolume z),
      Nonempty (GammaFullMeasuredBijection
        (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (F.rawRowForm z hF P))
        (gammaNativeMeasuredLift (gammaUniversalObject Q.toGamma) (E.rawRowForm z hE Q)))

theorem gammaMeasured_unary_raw_row_witness
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (F : GammaMeasuredRVSchema hc B p a 1 sp) (E : GammaMeasuredRVSchema hc B p b 1 sp)
    (z : Fin p → M) (h : gammaUnaryMeasuredRowLiftComparison F E z) :
    ∃ H : GammaMeasuredRelationSchema F.essential E.essential, H.valid z := by
  obtain ⟨hF,hE,P,Q,⟨f⟩⟩ := h
  exact gammaMeasured_unary_native_lift_row_witness hκ hs h00 hr hg hv δ hδ hδ1 z
    (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma)
    (F.rawRowForm z hF P) (E.rawRowForm z hE Q) F E hF hE
    (F.rawRow_volume z hF P) (E.rawRow_volume z hE Q)
    (F.rawRow_density z hF P) (E.rawRow_density z hE Q) f

end DiamondIntegral.Section3
