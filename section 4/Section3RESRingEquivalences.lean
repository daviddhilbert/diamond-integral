import «section 4».Section3RESNativeRingMaps
import «section 4».Section3RESChartAddMaps
import «section 4».ObjectClassAdditiveGeneration

/-! Actual ordinary and measured RES ring equivalences, proved through
their class formulas and additive inverses. No groupified inclusion is
assumed injective. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RESRingEquivalences
open RVMeasuredCharts Section3RESClassCuts Section3RVRoundtripBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

def ordinaryPresentation : ObjectClassAdditiveGeneration.Presentation (RESOrdinaryRing.Generator B) (RESOrdinaryRing.Ring B) where
  objectClass a := RESOrdinaryRing.objectClass a.2
  unit := ⟨0, RESChartRing.unit B⟩
  class_unit := RESOrdinaryRing.objectClass_unit B
  product a b := ⟨b.1 + a.1, RVMeasuredProductProperties.resProduct a.2 b.2⟩
  class_product a b := RESOrdinaryRing.objectClass_product a.2 b.2
  free := Ideal.Quotient.mk (RESOrdinaryRing.relationIdeal B)
  free_of _ := rfl
  surjective := Ideal.Quotient.mk_surjective

def measuredPresentation : ObjectClassAdditiveGeneration.Presentation (RESChartRing.Generator B) (RESChartRing.Ring B) where
  objectClass a := RESChartRing.objectClass a.2
  unit := ⟨0, RESChartRing.unit B⟩
  class_unit := RESChartRing.objectClass_unit B
  product a b := ⟨b.1 + a.1, RVMeasuredProductProperties.resProduct a.2 b.2⟩
  class_product a b := RESChartRing.objectClass_product a.2 b.2
  free := Ideal.Quotient.mk (RESChartRing.relationIdeal B)
  free_of _ := rfl
  surjective := Ideal.Quotient.mk_surjective

theorem ordinary_addHom_ext {G : Type*} [AddCommGroup G] (f g : OrdinaryRing hc B →+ G)
    (h : ∀ k (U : GammaGroundRESObject hc B k), f (ordinaryClass U) = g (ordinaryClass U)) : f = g := by
  have he : f.comp of = g.comp of := by
    apply DirectSum.addHom_ext
    intro k
    have hh : (f.comp of).comp (DirectSum.of (GammaGroundRESKPlus hc B) k) =
        (g.comp of).comp (DirectSum.of (GammaGroundRESKPlus hc B) k) := by
      apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundRESPresentation hc B k)
      intro U
      exact h k U
    exact DFunLike.congr_fun hh
  exact completionAddHom_ext (DFunLike.congr_fun he)

theorem measured_addHom_ext {G : Type*} [AddCommGroup G] (f g : MeasuredRing hc B →+ G)
    (h : ∀ k (U : GammaGroundMeasuredRESObject hc B k), f (measuredClass U) = g (measuredClass U)) : f = g := by
  have he : f.comp of = g.comp of := by
    apply DirectSum.addHom_ext
    intro k
    have hh : (f.comp of).comp (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) k) =
        (g.comp of).comp (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) k) := by
      apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundMeasuredRESPresentation hc B k)
      intro U
      exact h k U
    exact DFunLike.congr_fun hh
  exact completionAddHom_ext (DFunLike.congr_fun he)

theorem ordinary_chart_native :
    (Section3RESChartAddMaps.ordinary hc B).comp (Section3RESNativeRingMaps.ordinary hc B).toAddMonoidHom = AddMonoidHom.id _ := by
  apply ObjectClassAdditiveGeneration.hom_ext (ordinaryPresentation B)
  rintro ⟨k, a⟩
  change Section3RESChartAddMaps.ordinary hc B (Section3RESNativeRingMaps.ordinary hc B (RESOrdinaryRing.objectClass a)) = RESOrdinaryRing.objectClass a
  rw [Section3RESNativeRingMaps.ordinary_class, Section3RESChartAddMaps.ordinary_class]
  exact RESOrdinaryRing.objectClass_iso (chart_native a.toChart)

theorem measured_chart_native :
    (Section3RESChartAddMaps.measured hc B).comp (Section3RESNativeRingMaps.measured hc B).toAddMonoidHom = AddMonoidHom.id _ := by
  apply ObjectClassAdditiveGeneration.hom_ext (measuredPresentation B)
  rintro ⟨k, a⟩
  change Section3RESChartAddMaps.measured hc B (Section3RESNativeRingMaps.measured hc B (RESChartRing.objectClass a)) = RESChartRing.objectClass a
  rw [Section3RESNativeRingMaps.measured_class, Section3RESChartAddMaps.measured_class]
  exact RESChartRing.objectClass_iso (chart_native_measured a.toChart)

theorem ordinary_native_chart :
    (Section3RESNativeRingMaps.ordinary hc B).toAddMonoidHom.comp (Section3RESChartAddMaps.ordinary hc B) = AddMonoidHom.id _ := by
  apply ordinary_addHom_ext hc B
  intro k U
  change Section3RESNativeRingMaps.ordinary hc B (Section3RESChartAddMaps.ordinary hc B (ordinaryClass U)) = ordinaryClass U
  rw [Section3RESChartAddMaps.ordinary_class, Section3RESNativeRingMaps.ordinary_class]
  exact ordinary_iso (native_chart U.obj)

theorem measured_native_chart :
    (Section3RESNativeRingMaps.measured hc B).toAddMonoidHom.comp (Section3RESChartAddMaps.measured hc B) = AddMonoidHom.id _ := by
  apply measured_addHom_ext hc B
  intro k U
  change Section3RESNativeRingMaps.measured hc B (Section3RESChartAddMaps.measured hc B (measuredClass U)) = measuredClass U
  rw [Section3RESChartAddMaps.measured_class, Section3RESNativeRingMaps.measured_class]
  exact measured_iso (native_chart_measured U.obj)

def ordinary : RESOrdinaryRing.Ring B ≃+* OrdinaryRing hc B :=
  RingEquiv.ofBijective (Section3RESNativeRingMaps.ordinary hc B) ⟨(by
    intro x y h
    have hh := congrArg (Section3RESChartAddMaps.ordinary hc B) h
    exact (DFunLike.congr_fun (ordinary_chart_native hc B) x).symm.trans
      (hh.trans (DFunLike.congr_fun (ordinary_chart_native hc B) y))), (by
    intro y
    exact ⟨Section3RESChartAddMaps.ordinary hc B y, DFunLike.congr_fun (ordinary_native_chart hc B) y⟩)⟩

def measured : RESChartRing.Ring B ≃+* MeasuredRing hc B :=
  RingEquiv.ofBijective (Section3RESNativeRingMaps.measured hc B) ⟨(by
    intro x y h
    have hh := congrArg (Section3RESChartAddMaps.measured hc B) h
    exact (DFunLike.congr_fun (measured_chart_native hc B) x).symm.trans
      (hh.trans (DFunLike.congr_fun (measured_chart_native hc B) y))), (by
    intro y
    exact ⟨Section3RESChartAddMaps.measured hc B y, DFunLike.congr_fun (measured_native_chart hc B) y⟩)⟩

theorem ordinary_class {k : ℕ} (a : RESChart B k) : ordinary hc B (RESOrdinaryRing.objectClass a) =
    ordinaryClass (Section3RVChartBridge.nativeRES hc a) := Section3RESNativeRingMaps.ordinary_class hc B a
theorem measured_class {k : ℕ} (a : RESChart B k) : measured hc B (RESChartRing.objectClass a) =
    measuredClass (Section3MeasuredRVChartBridge.nativeRES hc a) := Section3RESNativeRingMaps.measured_class hc B a

theorem ordinary_symm_class {k : ℕ} (U : GammaGroundRESObject hc B k) :
    (ordinary hc B).symm (ordinaryClass U) = RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES U) := by
  apply (ordinary hc B).injective
  rw [RingEquiv.apply_symm_apply, ordinary_class]
  exact (ordinary_iso (native_chart U.obj)).symm
theorem measured_symm_class {k : ℕ} (U : GammaGroundMeasuredRESObject hc B k) :
    (measured hc B).symm (measuredClass U) = RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES U) := by
  apply (measured hc B).injective
  rw [RingEquiv.apply_symm_apply, measured_class]
  exact (measured_iso (native_chart_measured U.obj)).symm

end DiamondIntegral.Section4.Section3RESRingEquivalences
