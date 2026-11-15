import «section 5».RESFibreOnlyWitness
import «section 5».RESFamilyUngradedClasses

/-! The finite stabilized object-bijection criterion in the paper's exact
form: all primitive relation pairs are value-fibre versus torus pairs.
Underlying degree-forgetting bijections have been absorbed into the one
common positive stabilizer, without positive cancellation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

theorem FibreOnlyFamilyWitness.reduced_equality {k l : ℕ} {a : RVMeasuredCharts.RESChart B k}
    {b : RVMeasuredCharts.RESChart B l} (w : FibreOnlyFamilyWitness hc B a b) :
    RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b) := by
  have hu := nativeUngradedClass_bijection hc
    (familyNativeObject hc B (stabilizedFamily hc B a w.stabilizer (relationRightFamily hc B w.terms)))
    (familyNativeObject hc B (stabilizedFamily hc B b w.stabilizer (relationLeftFamily hc B w.terms)))
    w.bijection
  have he := congrArg (RESDimensionFreeReduction.quotient B) hu
  change RESDimensionFreeReduction.quotient B (familyUngradedClass hc B _) =
    RESDimensionFreeReduction.quotient B (familyUngradedClass hc B _) at he
  rw [familyReducedClass_eq,familyReducedClass_eq,stabilizedFamily_class,stabilizedFamily_class,
    map_add,map_add,map_add,map_add,reducedPositiveHom_positiveClass,reducedPositiveHom_positiveClass] at he
  have hrel := positiveRelation_reduced_eq hc B (relationTerms_positive_relation hc B w.terms)
  rw [hrel] at he
  exact add_right_cancel (add_right_cancel he)

theorem res_equality_iff_fibre_only_family_witness {k l : ℕ}
    (a : RVMeasuredCharts.RESChart B k) (b : RVMeasuredCharts.RESChart B l) :
    RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b) ↔
        Nonempty (FibreOnlyFamilyWitness hc B a b) :=
  ⟨res_equality_has_fibre_only_witness hc B a b,fun ⟨w⟩ => w.reduced_equality hc B⟩

theorem FibreOnlyFamilyWitness.stabilizer_finite {k l : ℕ} {a : RVMeasuredCharts.RESChart B k}
    {b : RVMeasuredCharts.RESChart B l} (w : FibreOnlyFamilyWitness hc B a b) :
    GammaRVFiniteValues hc B (familyRVSet hc B w.stabilizer).2 := familyRVSet_finite hc B _

theorem FibreOnlyFamilyWitness.source_finite {k l : ℕ} {a : RVMeasuredCharts.RESChart B k}
    {b : RVMeasuredCharts.RESChart B l} (w : FibreOnlyFamilyWitness hc B a b) :
    GammaRVFiniteValues hc B
      (familyRVSet hc B (stabilizedFamily hc B a w.stabilizer (relationRightFamily hc B w.terms))).2 :=
  familyRVSet_finite hc B _

theorem FibreOnlyFamilyWitness.target_finite {k l : ℕ} {a : RVMeasuredCharts.RESChart B k}
    {b : RVMeasuredCharts.RESChart B l} (w : FibreOnlyFamilyWitness hc B a b) :
    GammaRVFiniteValues hc B
      (familyRVSet hc B (stabilizedFamily hc B b w.stabilizer (relationLeftFamily hc B w.terms))).2 :=
  familyRVSet_finite hc B _

end DiamondIntegral.Section5.RESFiniteWitness
