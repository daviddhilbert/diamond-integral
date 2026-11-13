import «section 4».GammaBoundedRVPresentation
import «section 4».GammaBoundedChartMap
import «section 4».RVSharpRingMap
import «section 4».RVBoundedMaps

/-! Maps from the intrinsic bounded Gamma presentation to the actual
bounded RV ring and to the auxiliary bounded chart subring used to
construct profiles. The latter is a proved map, not a category identity. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedRVMaps
open GammaBoundedRVCharts GammaBoundedRVPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def forgetInvariant (B : Base (M := M)) : Invariant B (GammaRVChartPresentation.ChartRing B) where
  value _ a := GammaRVChartPresentation.objectClass a.toChart
  unit := GammaRVChartPresentation.class_unit B
  product _ _ a b := GammaRVChartPresentation.class_product a.toChart b.toChart
  iso _ _ _ F := GammaRVChartPresentation.class_iso F
  empty n μ hμ := GammaRVChartPresentation.class_empty B n μ hμ
  scissor n I J hI hJ _ _ hU hN μ hμ := GammaRVChartPresentation.class_scissor B n I J hI hJ hU hN μ hμ

def forget (B : Base (M := M)) : ChartRing B →+* GammaRVChartPresentation.ChartRing B := lift B (forgetInvariant B)

theorem forget_class (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    forget B (objectClass a) = GammaRVChartPresentation.objectClass a.toChart := lift_class B (forgetInvariant B) a

def auxiliaryInvariant (B : Base (M := M)) : Invariant B (GammaBoundedChartMap.boundedChartSubring B) where
  value _ a := GammaBoundedChartMap.boundedClass a.toChart a.domain_bounded
  unit := by
    apply Subtype.ext
    exact (congrArg (GammaRVChartPresentation.forget B) (GammaRVChartPresentation.class_unit B)).trans
      (GammaRVChartPresentation.forget B).map_one
  product _ _ a b := by
    apply Subtype.ext
    exact (congrArg (GammaRVChartPresentation.forget B) (GammaRVChartPresentation.class_product a.toChart b.toChart)).trans
      ((GammaRVChartPresentation.forget B).map_mul _ _)
  iso _ _ _ F := by
    apply Subtype.ext
    exact congrArg (GammaRVChartPresentation.forget B) (GammaRVChartPresentation.class_iso F)
  empty n μ hμ := by
    apply Subtype.ext
    exact (congrArg (GammaRVChartPresentation.forget B) (GammaRVChartPresentation.class_empty B n μ hμ)).trans
      (GammaRVChartPresentation.forget B).map_zero
  scissor n I J hI hJ _ _ hU hN μ hμ := by
    apply Subtype.ext
    exact ((GammaRVChartPresentation.forget B).map_add _ _).symm.trans
      ((congrArg (GammaRVChartPresentation.forget B)
        (GammaRVChartPresentation.class_scissor B n I J hI hJ hU hN μ hμ)).trans
          ((GammaRVChartPresentation.forget B).map_add _ _))

def auxiliary (B : Base (M := M)) : ChartRing B →+* GammaBoundedChartMap.boundedChartSubring B :=
  lift B (auxiliaryInvariant B)

theorem auxiliary_class (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    auxiliary B (objectClass a) = GammaBoundedChartMap.boundedClass a.toChart a.domain_bounded :=
  lift_class B (auxiliaryInvariant B) a

def sharpInvariant (B : Base (M := M)) : Invariant B (RVBoundedRing.Ring B) where
  value _ a := RVBoundedRing.objectClass (GammaBoundedRVCharts.sharp a)
  unit := (RVBoundedRing.objectClass_iso (sharpUnitIso B)).trans (RVBoundedRing.objectClass_unit B)
  product _ _ a b := (RVBoundedRing.objectClass_iso (sharpProductIso a b)).trans (RVBoundedRing.objectClass_product _ _)
  iso _ _ _ F := RVBoundedRing.objectClass_iso (RVSharpCharts.sharpIso F)
  empty n μ hμ := RVBoundedRing.objectClass_empty _ (RVSharpScissors.sharp_empty B n μ hμ)
  scissor n I J hI hJ _ _ hU hN μ hμ :=
    RVBoundedRing.objectClass_scissor _ _ _ _ (RVSharpScissors.sharp_scissor B n I J hI hJ hU hN μ hμ)

def sharp (B : Base (M := M)) : ChartRing B →+* RVBoundedRing.Ring B := lift B (sharpInvariant B)

theorem sharp_class (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    sharp B (objectClass a) = RVBoundedRing.objectClass (GammaBoundedRVCharts.sharp a) :=
  lift_class B (sharpInvariant B) a

theorem forget_sharp (B : Base (M := M)) :
    (RVBoundedMaps.forget B).comp (sharp B) = (RVSharpRingMap.sharp B).comp (forget B) := by
  apply GammaBoundedRVPresentation.hom_ext B
  intro n a
  change RVBoundedMaps.forget B (sharp B (objectClass a)) = RVSharpRingMap.sharp B (forget B (objectClass a))
  rw [sharp_class, RVBoundedMaps.forget_class, forget_class]
  exact (RVSharpRingMap.sharp_class B a.toChart).symm

end DiamondIntegral.Section4.GammaBoundedRVMaps
