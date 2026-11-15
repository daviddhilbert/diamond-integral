import «section 4».RESDimensionFreeReduction
import «section 4».Section3RESChartCuts

/-! Actual chart classes in the native ungraded reduced RES ring satisfy
underlying-isomorphism, product, empty-domain and original-base cut laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k l : ℕ}

def nativeRESChartClass (A : RVMeasuredCharts.RESChart B k) : RESDimensionFreeReduction.Ring B :=
  RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass A)

theorem nativeRESChartClass_iso (A : RVMeasuredCharts.RESChart B k) (C : RVMeasuredCharts.RESChart B l)
    (F : RVUnderlyingIsomorphisms.Iso A.toChart C.toChart) : nativeRESChartClass A = nativeRESChartClass C :=
  congrArg (RESDimensionFreeReduction.quotient B) (RESDimensionFreeRing.objectClass_iso A C F)

theorem nativeRESChartClass_product (A : RVMeasuredCharts.RESChart B k) (C : RVMeasuredCharts.RESChart B l) :
    nativeRESChartClass (RVMeasuredProductProperties.resProduct A C) = nativeRESChartClass A * nativeRESChartClass C := by
  exact congrArg (RESDimensionFreeReduction.fromOrdinary B) (RESOrdinaryRing.objectClass_product A C) |>.trans
    (map_mul _ _ _)

theorem nativeRESChartClass_empty (A : RVMeasuredCharts.RESChart B k) (hA : A.domain = ∅) :
    nativeRESChartClass A = 0 := by
  exact congrArg (RESDimensionFreeReduction.fromOrdinary B) (RESOrdinaryRing.objectClass_empty A hA) |>.trans
    (map_zero _)

theorem nativeRESChartClass_cut (A : RVMeasuredCharts.RESChart B k) (I : Set (Fin A.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin A.arity => .rv) I) (hs : I ⊆ A.domain) :
    nativeRESChartClass (Section3RESChartCuts.restrict A I hI hs) +
      nativeRESChartClass (Section3RESChartCuts.outside A I hI) = nativeRESChartClass A := by
  exact (map_add (RESDimensionFreeReduction.fromOrdinary B) _ _).symm.trans
    (congrArg (RESDimensionFreeReduction.fromOrdinary B) (Section3RESChartCuts.ordinary_cut A I hI hs))

end DiamondIntegral.Section5
