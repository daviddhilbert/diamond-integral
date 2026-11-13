import «section 4».GammaFiniteRVPresentation
import «section 4».GammaBoundedRVMaps
import «section 4».RVChartMaps

/-! The intrinsic finite Gamma ring maps to RES, bounded Gamma and full
Gamma rings through actual objects. The product comparison squares
commute; no injectivity of these maps is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteRVMaps
open GammaFiniteRVCharts GammaFiniteRVPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def forgetInvariant (B : Base (M := M)) : Invariant B (GammaRVChartPresentation.ChartRing B) where
  value _ a := GammaRVChartPresentation.objectClass a.toChart
  unit := GammaRVChartPresentation.class_unit B
  product _ _ a b := GammaRVChartPresentation.class_product a.toChart b.toChart
  iso _ _ _ F := GammaRVChartPresentation.class_iso F
  empty n μ hμ := GammaRVChartPresentation.class_empty B n μ hμ
  scissor n I J hI hJ _ _ hU hN μ hμ := GammaRVChartPresentation.class_scissor B n I J hI hJ hU hN μ hμ

def forget (B : Base (M := M)) : ChartRing B →+* GammaRVChartPresentation.ChartRing B := lift B (forgetInvariant B)

theorem forget_class (B : Base (M := M)) {n : ℕ} (a : FiniteChart B n) :
    forget B (objectClass a) = GammaRVChartPresentation.objectClass a.toChart := lift_class B (forgetInvariant B) a

def boundedInvariant (B : Base (M := M)) : Invariant B (GammaBoundedRVPresentation.ChartRing B) where
  value _ a := GammaBoundedRVPresentation.objectClass (GammaFiniteRVCharts.bounded a)
  unit := GammaBoundedRVPresentation.class_unit B
  product _ _ a b := GammaBoundedRVPresentation.class_product (GammaFiniteRVCharts.bounded a) (GammaFiniteRVCharts.bounded b)
  iso _ _ _ F := GammaBoundedRVPresentation.class_iso F
  empty n μ hμ := GammaBoundedRVPresentation.class_empty B n μ hμ
  scissor n I J hI hJ hiI hiJ hU hN μ hμ := GammaBoundedRVPresentation.class_scissor B n I J hI hJ
    (GammaFiniteBounds.finite_domain_bounded I hiI) (GammaFiniteBounds.finite_domain_bounded J hiJ) hU hN μ hμ

def bounded (B : Base (M := M)) : ChartRing B →+* GammaBoundedRVPresentation.ChartRing B := lift B (boundedInvariant B)

theorem bounded_class (B : Base (M := M)) {n : ℕ} (a : FiniteChart B n) :
    bounded B (objectClass a) = GammaBoundedRVPresentation.objectClass (GammaFiniteRVCharts.bounded a) :=
  lift_class B (boundedInvariant B) a

def sharpInvariant (B : Base (M := M)) : Invariant B (RESChartRing.Ring B) where
  value _ a := RESChartRing.objectClass (GammaFiniteRVCharts.sharp a)
  unit := (RESChartRing.objectClass_iso (sharpUnitIso B)).trans (RESChartRing.objectClass_unit B)
  product _ _ a b := (RESChartRing.objectClass_iso (sharpProductIso a b)).trans (RESChartRing.objectClass_product _ _)
  iso _ _ _ F := RESChartRing.objectClass_iso (RVSharpCharts.sharpIso F)
  empty n μ hμ := RESChartRing.objectClass_empty _ (RVSharpScissors.sharp_empty B n μ hμ)
  scissor n I J hI hJ _ _ hU hN μ hμ :=
    RESChartRing.objectClass_scissor _ _ _ _ (RVSharpScissors.sharp_scissor B n I J hI hJ hU hN μ hμ)

def sharp (B : Base (M := M)) : ChartRing B →+* RESChartRing.Ring B := lift B (sharpInvariant B)

theorem sharp_class (B : Base (M := M)) {n : ℕ} (a : FiniteChart B n) :
    sharp B (objectClass a) = RESChartRing.objectClass (GammaFiniteRVCharts.sharp a) := lift_class B (sharpInvariant B) a

theorem forget_bounded (B : Base (M := M)) : (GammaBoundedRVMaps.forget B).comp (bounded B) = forget B := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change GammaBoundedRVMaps.forget B (bounded B (objectClass a)) = forget B (objectClass a)
  rw [bounded_class, GammaBoundedRVMaps.forget_class, forget_class]
  rfl

theorem sharp_full_comparison (B : Base (M := M)) :
    (RVChartMaps.ofRES B).comp (sharp B) = (RVSharpRingMap.sharp B).comp (forget B) := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change RVChartMaps.ofRES B (sharp B (objectClass a)) = RVSharpRingMap.sharp B (forget B (objectClass a))
  rw [sharp_class, RVChartMaps.ofRES_class, forget_class]
  exact (RVSharpRingMap.sharp_class B a.toChart).symm

theorem sharp_bounded_comparison (B : Base (M := M)) :
    (RVBoundedMaps.ofRES B).comp (sharp B) = (GammaBoundedRVMaps.sharp B).comp (bounded B) := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change RVBoundedMaps.ofRES B (sharp B (objectClass a)) = GammaBoundedRVMaps.sharp B (bounded B (objectClass a))
  rw [sharp_class, RVBoundedMaps.ofRES_class, bounded_class, GammaBoundedRVMaps.sharp_class]
  rfl

end DiamondIntegral.Section4.GammaFiniteRVMaps
