import «section 4».RESResidueTrace
import «section 4».RVResidueFibreCodes
import «section 4».FieldAffineDecomposition
import «section 4».FieldAffineQuotientMap
import «section 4».RESMeasuredReduction
import Section7.ResidueCharacteristic
import ProvedResidueClosure
import VFAlgClosed

/-! The actual degree-one point survives the measured RES fibre and
affine-line reduction. The proof uses a constructed residue trace and
finite-field specialization, not an HK nonvanishing theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RESPointNonvanishing
open RESResidueTrace RESMeasuredReduction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem trace_scaled (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.RESChart B k)
    (γ : Values.Gamma (M := M)) (hγ : GammaDefinableClosureAtBase B γ) :
    trace hc B (RESChartRing.objectClass (RVWeightScaling.scaledRES a γ hγ)) =
      trace hc B (RESChartRing.objectClass a) := by
  rw [RVWeightScaling.scaledRES_class, map_mul, trace_weightedUnit, one_mul]

theorem trace_fibre (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    trace hc B (RESChartRing.objectClass (RESFibreObjects.fibre B α β hα hβ)) =
      trace hc B (RESChartRing.objectClass (RESFibreObjects.torus B)) := by
  rw [trace_objectClass, trace_objectClass, RVResidueFibreCodes.value_fibre]
  exact (RVResidueFibreCodes.value_fibre hc B 1 1
    (GammaGroupNames.one_definable_base B) (GammaGroupNames.one_definable_base B)).symm

theorem trace_affine (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : trace hc B (affineClass B) =
      FieldDefinableRing.affineClass (ModelResidue M) := by
  change trace hc B (RESChartRing.objectClass (RESFibreObjects.torus B) +
    RESChartRing.objectClass (RESFibreObjects.point B)) = _
  rw [map_add, trace_point, trace_objectClass]
  rw [show RVResidueIsomorphisms.value hc (RESFibreObjects.torus B) =
    FieldDefinableRing.objectClass (ModelResidue M)
      (FieldAffineDecomposition.puncturedLine (ModelResidue M)) from
    RVResidueFibreCodes.value_fibre hc B 1 1
      (GammaGroupNames.one_definable_base B) (GammaGroupNames.one_definable_base B)]
  exact FieldAffineDecomposition.punctured_plus_one (ModelResidue M)

def rawMap (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : RESChartRing.Ring B →+*
      FieldDefinableRing.AffineQuotient (ModelResidue M) :=
  (FieldAffineQuotientMap.quotient (ModelResidue M)).comp (trace hc B)

theorem fibreIdeal_le_ker (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : fibreIdeal B ≤ RingHom.ker (rawMap hc B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨α, β, hα, hβ, rfl⟩
  change FieldAffineQuotientMap.quotient (ModelResidue M) (trace hc B (_ - _)) = 0
  rw [map_sub, trace_scaled, trace_fibre, sub_self, map_zero]

theorem reductionIdeal_le_ker (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : reductionIdeal B ≤ RingHom.ker (rawMap hc B) := by
  apply sup_le (fibreIdeal_le_ker hc B)
  apply Ideal.span_le.mpr
  rintro x (rfl : x = affineClass B)
  change FieldAffineQuotientMap.quotient (ModelResidue M) (trace hc B (affineClass B)) = 0
  rw [trace_affine, FieldAffineQuotientMap.quotient_affine]

def reducedMap (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : ReducedRing B →+* FieldDefinableRing.AffineQuotient (ModelResidue M) :=
  Ideal.Quotient.lift (reductionIdeal B) (rawMap hc B) (fun _ h => reductionIdeal_le_ker hc B h)

theorem reducedMap_point (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : reducedMap hc B (pointClass B) = 1 := by
  change FieldAffineQuotientMap.quotient (ModelResidue M)
    (trace hc B (RESChartRing.objectClass (RESFibreObjects.point B))) = 1
  rw [trace_point, map_one]

theorem point_ne_zero (hc : CanonicalStructure.IsCanonical (M := M))
    [IsAlgClosed (ModelResidue M)] [CharZero (ModelResidue M)] (B : Base (M := M)) :
    pointClass B ≠ 0 := by
  intro h
  have he := congrArg (reducedMap hc B) h
  rw [reducedMap_point, map_zero] at he
  exact FieldAffineNontrivial.quotient_one_ne_zero (ModelResidue M) he

theorem point_ne_zero_acvf00 (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) : pointClass B ≠ 0 := by
  letI : IsAlgClosed (SpecialTransformations.Milestone0.Transfer.VFType (M := M)) :=
    VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  letI : CharZero (ModelResidue M) := SpecialTransformations.Section7.residueField_charZero_of_model00
    Values.presentationValuation Values.presentation_compatible h00
  exact point_ne_zero hc B

end DiamondIntegral.Section4.RESPointNonvanishing
