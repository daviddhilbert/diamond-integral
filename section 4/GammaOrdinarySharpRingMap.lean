import «section 4».GammaOrdinarySharpObjects
import «section 4».GammaOrdinaryGrading
import «section 4».RVOrdinaryGrading
import «section 4».RVSharpRingMap

/-! The actual sharp ring map from ordinary Gamma objects to ordinary
RV objects is graded and commutes with forgetting measured forms on the
whole source ring. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinarySharpRingMap
open GammaOrdinaryCharts GammaOrdinarySharpObjects
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def invariant (B : Base (M := M)) : GammaOrdinaryRing.Invariant B (RVOrdinaryRing.Ring B) where
  value _ a := RVOrdinaryRing.objectClass (sharpChart a)
  unit := sharp_unit B
  product _ _ a b := sharp_product a b
  iso _ _ _ f := RVOrdinaryRing.objectClass_iso (GammaOrdinaryCharts.sharpIso f)
  empty _ a h := sharp_empty a h
  scissor _ a b c d h := sharp_scissor a b c d h

def sharp (B : Base (M := M)) : GammaOrdinaryRing.Ring B →+* RVOrdinaryRing.Ring B := GammaOrdinaryRing.lift B (invariant B)

theorem sharp_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    sharp B (GammaOrdinaryRing.objectClass a) = RVOrdinaryRing.objectClass (sharpChart a) := GammaOrdinaryRing.lift_class B (invariant B) a

theorem forget_square (B : Base (M := M)) :
    (sharp B).comp (GammaOrdinaryRing.forget B) = (RVOrdinaryRing.forget B).comp (RVSharpRingMap.sharp B) := by
  apply GammaRVChartPresentation.hom_ext B
  intro n a
  change sharp B (GammaOrdinaryRing.forget B (GammaRVChartPresentation.objectClass a)) =
    RVOrdinaryRing.forget B (RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass a))
  rw [GammaOrdinaryRing.forget_class, sharp_class]
  have hs : RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass a) = RVChartRing.objectClass (RVSharpCharts.sharpChart a) :=
    RVSharpRingMap.sharp_class B a
  rw [hs, RVOrdinaryRing.forget_objectClass]
  exact RVOrdinaryRing.objectClass_iso (sameSupportIso (toWeighted (ofWeighted a)) a rfl)

theorem sharp_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (sharp B)).comp (GammaOrdinaryGrading.coaction B) = (RVOrdinaryGrading.coaction B).comp (sharp B) := by
  apply GammaOrdinaryRing.hom_ext B
  intro n a
  change (GammaOrdinaryGrading.coaction B (GammaOrdinaryRing.objectClass a)).map (sharp B) =
    RVOrdinaryGrading.coaction B (sharp B (GammaOrdinaryRing.objectClass a))
  rw [GammaOrdinaryGrading.coaction_class, Polynomial.map_monomial, sharp_class, RVOrdinaryGrading.coaction_class]

theorem sharp_mem (B : Base (M := M)) {n : ℕ} {x : GammaOrdinaryRing.Ring B}
    (hx : x ∈ GammaOrdinaryGrading.gradedPiece B n) : sharp B x ∈ RVOrdinaryGrading.gradedPiece B n := by
  change GammaOrdinaryGrading.coaction B x = Polynomial.monomial n x at hx
  change RVOrdinaryGrading.coaction B (sharp B x) = Polynomial.monomial n (sharp B x)
  have h := RingHom.congr_fun (sharp_coaction B) x
  change (GammaOrdinaryGrading.coaction B x).map (sharp B) = RVOrdinaryGrading.coaction B (sharp B x) at h
  rw [← h, hx, Polynomial.map_monomial]

def gradedSharp (B : Base (M := M)) : GradedRingHom (GammaOrdinaryGrading.gradedPiece B) (RVOrdinaryGrading.gradedPiece B) where
  toRingHom := sharp B
  map_mem := fun hx => sharp_mem B hx

end DiamondIntegral.Section4.GammaOrdinarySharpRingMap
