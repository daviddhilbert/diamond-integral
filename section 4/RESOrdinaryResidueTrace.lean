import «section 4».RESResidueTrace
import «section 4».RVResidueFibreCodes
import «section 4».RESPointNonvanishing
import «section 4».RESOrdinaryReduction
import «section 4».RESAffineLocalization

/-! The residue trace also descends through ordinary RES fibre
relations and forgetting degree. It retains the affine-line class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RESOrdinaryResidueTrace
open RVResidueIsomorphisms
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)] (B : Base (M := M))

def freeMap : FreeCommRing (RESOrdinaryRing.Generator B) →+* FieldDefinableRing.Ring (ModelResidue M) :=
  FreeCommRing.lift (fun a => value hc a.2)

theorem freeMap_symbol {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    freeMap hc B (RESOrdinaryRing.symbol a) = value hc a := FreeCommRing.lift_of _ _

theorem relation_zero (r : FreeCommRing (RESOrdinaryRing.Generator B)) (h : RESOrdinaryRing.Relation B r) :
    freeMap hc B r = 0 := by
  cases h with
  | unit =>
    rw [map_sub, map_one, freeMap_symbol]
    exact sub_eq_zero.mpr (RVResiduePointValues.value_weightedUnit hc B 1
      (GammaGroupNames.one_definable_base B))
  | product a b => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol,
      RVResidueProductCodes.value_product, sub_self]
  | iso a b F => rw [map_sub, freeMap_symbol, freeMap_symbol, value_iso hc a b F, sub_self]
  | empty a ha => rw [freeMap_symbol, RVResiduePointValues.value_empty hc a ha]
  | scissor a b c d hs =>
    rw [map_sub, map_sub, map_add, freeMap_symbol, freeMap_symbol, freeMap_symbol, freeMap_symbol,
      sub_sub, RVResidueScissors.value_scissor hc a b c d hs, sub_self]

theorem relationIdeal_le : RESOrdinaryRing.relationIdeal B ≤ RingHom.ker (freeMap hc B) :=
  Ideal.span_le.mpr (fun r hr => relation_zero hc B r hr)

def trace : RESOrdinaryRing.Ring B →+* FieldDefinableRing.Ring (ModelResidue M) :=
  Ideal.Quotient.lift (RESOrdinaryRing.relationIdeal B) (freeMap hc B)
    (fun _ h => relationIdeal_le hc B h)

theorem trace_objectClass {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    trace hc B (RESOrdinaryRing.objectClass a) = value hc a := freeMap_symbol hc B a

theorem fibreIdeal_le : RESOrdinaryReduction.fibreIdeal B ≤ RingHom.ker (trace hc B) := by
  apply Ideal.span_le.mpr
  rintro r ⟨α, hα, rfl⟩
  change trace hc B (_ - _) = 0
  rw [map_sub, trace_objectClass, trace_objectClass, RVResidueFibreCodes.value_fibre]
  rw [show value hc (RESFibreObjects.torus B) =
    FieldDefinableRing.objectClass (ModelResidue M) (RVResidueFibreCodes.puncturedLine (ModelResidue M)) from
    RVResidueFibreCodes.value_fibre hc B 1 1
      (GammaGroupNames.one_definable_base B) (GammaGroupNames.one_definable_base B), sub_self]

def reducedTrace : RESOrdinaryReduction.ReducedRing B →+* FieldDefinableRing.Ring (ModelResidue M) :=
  Ideal.Quotient.lift (RESOrdinaryReduction.fibreIdeal B) (trace hc B) (fun _ h => fibreIdeal_le hc B h)

theorem reducedTrace_point : reducedTrace hc B (RESOrdinaryReduction.pointClass B) = 1 := by
  change trace hc B (RESOrdinaryRing.objectClass (RESFibreObjects.point B)) = 1
  rw [trace_objectClass, RVResiduePointValues.value_point]

theorem reducedTrace_affine : reducedTrace hc B (RESAffineLocalization.affineClass B) =
    FieldDefinableRing.affineClass (ModelResidue M) := by
  change reducedTrace hc B (RESOrdinaryReduction.torusClass B + RESOrdinaryReduction.pointClass B) = _
  rw [map_add, reducedTrace_point]
  change trace hc B (RESOrdinaryRing.objectClass (RESFibreObjects.torus B)) + 1 = _
  rw [trace_objectClass, show value hc (RESFibreObjects.torus B) =
    FieldDefinableRing.objectClass (ModelResidue M) (FieldAffineDecomposition.puncturedLine (ModelResidue M)) from
    RVResidueFibreCodes.value_fibre hc B 1 1
      (GammaGroupNames.one_definable_base B) (GammaGroupNames.one_definable_base B)]
  exact FieldAffineDecomposition.punctured_plus_one (ModelResidue M)

theorem pointIdeal_le : RESDimensionFreeReduction.pointIdeal B ≤ RingHom.ker (reducedTrace hc B) := by
  apply Ideal.span_le.mpr
  rintro r (rfl : r = _)
  change reducedTrace hc B (RESOrdinaryReduction.pointClass B - 1) = 0
  rw [map_sub, map_one, reducedTrace_point, sub_self]

def normalizedTrace : RESDimensionFreeReduction.Normalized B →+* FieldDefinableRing.Ring (ModelResidue M) :=
  Ideal.Quotient.lift (RESDimensionFreeReduction.pointIdeal B) (reducedTrace hc B)
    (fun _ h => pointIdeal_le hc B h)

def dimensionFreeTrace : RESDimensionFreeReduction.Ring B →+* FieldDefinableRing.Ring (ModelResidue M) :=
  (normalizedTrace hc B).comp (RESDimensionFreeReduction.normalizationEquiv B).symm.toRingHom

theorem dimensionFreeTrace_fromGraded (x : RESOrdinaryReduction.ReducedRing B) :
    dimensionFreeTrace hc B (RESDimensionFreeReduction.fromGradedReduced B x) = reducedTrace hc B x := by
  change normalizedTrace hc B ((RESDimensionFreeReduction.normalizationEquiv B).symm
    ((RESDimensionFreeReduction.normalizationEquiv B) (Ideal.Quotient.mk _ x))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem dimensionFreeTrace_affine : dimensionFreeTrace hc B (RESAffineLocalization.dimensionFreeAffine B) =
    FieldDefinableRing.affineClass (ModelResidue M) :=
  (dimensionFreeTrace_fromGraded hc B _).trans (reducedTrace_affine hc B)

end DiamondIntegral.Section4.RESOrdinaryResidueTrace
