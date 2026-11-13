import «section 4».RESOrdinaryResidueTrace
import «section 4».FieldAffineLocalizationNontrivial
import «section 4».RESAffineNormalization

/-! The geometric point value in the actual dimension-free affine
localization differs from one. A constructed residue trace detects it;
no injectivity of the natural localization comparison is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RESAffineSeparation
open RESAffineLocalization RESOrdinaryResidueTrace
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)] (B : Base (M := M))
include hc

abbrev FieldTarget := Localization.Away (FieldDefinableRing.affineClass (ModelResidue M))

def fieldBaseMap : RESDimensionFreeReduction.Ring B →+* FieldTarget (M := M) :=
  (algebraMap (FieldDefinableRing.Ring (ModelResidue M)) (FieldTarget (M := M))).comp
    (dimensionFreeTrace hc B)

theorem fieldBaseMap_affine_unit : IsUnit (fieldBaseMap hc B (dimensionFreeAffine B)) := by
  change IsUnit (algebraMap (FieldDefinableRing.Ring (ModelResidue M)) (FieldTarget (M := M))
    (dimensionFreeTrace hc B (dimensionFreeAffine B)))
  rw [dimensionFreeTrace_affine]
  exact IsLocalization.Away.algebraMap_isUnit (S := FieldTarget (M := M))
    (FieldDefinableRing.affineClass (ModelResidue M))

def localizationTrace : Target B →+* FieldTarget (M := M) :=
  IsLocalization.Away.lift (dimensionFreeAffine B) (g := fieldBaseMap hc B) (fieldBaseMap_affine_unit hc B)

theorem localizationTrace_algebraMap (x : RESDimensionFreeReduction.Ring B) :
    localizationTrace hc B (algebraMap (RESDimensionFreeReduction.Ring B) (Target B) x) =
      fieldBaseMap hc B x := IsLocalization.Away.lift_eq (dimensionFreeAffine B) _ x

theorem affine_ne_one [IsAlgClosed (ModelResidue M)] [CharZero (ModelResidue M)] :
    algebraMap (RESDimensionFreeReduction.Ring B) (Target B) (dimensionFreeAffine B) ≠ 1 := by
  intro h
  have he := congrArg (localizationTrace hc B) h
  rw [localizationTrace_algebraMap, map_one] at he
  change algebraMap (FieldDefinableRing.Ring (ModelResidue M)) (FieldTarget (M := M))
    (dimensionFreeTrace hc B (dimensionFreeAffine B)) = 1 at he
  rw [dimensionFreeTrace_affine] at he
  exact FieldAffineLocalizationNontrivial.affine_ne_one (ModelResidue M) he

theorem inverse_ne_one [IsAlgClosed (ModelResidue M)] [CharZero (ModelResidue M)] :
    IsLocalization.Away.invSelf (dimensionFreeAffine B) (S := Target B) ≠ 1 := by
  intro h
  have he := IsLocalization.Away.mul_invSelf (dimensionFreeAffine B) (S := Target B)
  rw [h, mul_one] at he
  exact affine_ne_one hc B he

theorem comparison_point_ne_one [IsAlgClosed (ModelResidue M)] [CharZero (ModelResidue M)] :
    comparison B (RESAffineNormalization.normalize B (RESOrdinaryReduction.pointClass B)) ≠ 1 := by
  rw [RESAffineNormalization.comparison_point]
  exact inverse_ne_one hc B

omit [Infinite (ModelResidue M)] in
theorem comparison_point_ne_one_acvf00 (h00 : M ⊨ Axioms.ACVF00) :
    comparison B (RESAffineNormalization.normalize B (RESOrdinaryReduction.pointClass B)) ≠ 1 := by
  letI : IsAlgClosed (SpecialTransformations.Milestone0.Transfer.VFType (M := M)) :=
    VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  letI : CharZero (ModelResidue M) := SpecialTransformations.Section7.residueField_charZero_of_model00
    Values.presentationValuation Values.presentation_compatible h00
  exact comparison_point_ne_one hc B

end DiamondIntegral.Section4.RESAffineSeparation
