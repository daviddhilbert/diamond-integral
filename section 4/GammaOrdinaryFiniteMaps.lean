import «section 4».GammaOrdinaryFiniteRing
import «section 4».GammaOrdinarySharpScissors
import «section 4».GammaOrdinarySharpRingMap
import «section 4».GammaFiniteRVMaps
import «section 4».RESOrdinaryUniversal
import «section 4».RVOrdinaryMaps

/-! The ordinary finite-Gamma coefficient ring maps to ordinary Gamma
and RES through actual objects. Both sharp/forget squares commute on the
whole rings, without chosen RV representatives. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFiniteMaps
open GammaOrdinaryCharts GammaOrdinaryFiniteCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fullInvariant (B : Base (M := M)) : GammaOrdinaryFiniteRing.Invariant B (GammaOrdinaryRing.Ring B) where
  value _ a := GammaOrdinaryRing.objectClass a.toChart
  unit := GammaOrdinaryRing.class_unit B
  product _ _ a b := GammaOrdinaryRing.class_product a.toChart b.toChart
  iso _ _ _ f := GammaOrdinaryRing.class_iso f
  empty _ a h := GammaOrdinaryRing.class_empty a.toChart h
  scissor _ a b c d h := GammaOrdinaryRing.class_scissor a.toChart b.toChart c.toChart d.toChart h

def full (B : Base (M := M)) : GammaOrdinaryFiniteRing.Ring B →+* GammaOrdinaryRing.Ring B := GammaOrdinaryFiniteRing.lift B (fullInvariant B)

theorem full_class (B : Base (M := M)) {n : ℕ} (a : FiniteChart B n) : full B (GammaOrdinaryFiniteRing.objectClass a) = GammaOrdinaryRing.objectClass a.toChart :=
  GammaOrdinaryFiniteRing.lift_class B (fullInvariant B) a

def sharpInvariant (B : Base (M := M)) : GammaOrdinaryFiniteRing.Invariant B (RESOrdinaryRing.Ring B) where
  value _ a := RESOrdinaryRing.objectClass (sharp a)
  unit := sharp_unit B
  product _ _ a b := sharp_product a b
  iso _ _ _ f := RESOrdinaryRing.objectClass_iso (GammaOrdinaryFiniteCharts.sharpIso f)
  empty _ a ha := by
    apply RESOrdinaryRing.objectClass_empty
    change GammaRVChartPresentation.sharp a.support = ∅
    rw [ha]
    ext z
    exact ⟨fun h => h.2.elim, fun h => h.elim⟩
  scissor _ a b c d h := RESOrdinaryRing.objectClass_scissor _ _ _ _
    (GammaOrdinarySharpScissors.sharp_scissor a.toChart b.toChart c.toChart d.toChart h)

def sharp (B : Base (M := M)) : GammaOrdinaryFiniteRing.Ring B →+* RESOrdinaryRing.Ring B := GammaOrdinaryFiniteRing.lift B (sharpInvariant B)

theorem sharp_class (B : Base (M := M)) {n : ℕ} (a : FiniteChart B n) :
    sharp B (GammaOrdinaryFiniteRing.objectClass a) = RESOrdinaryRing.objectClass (GammaOrdinaryFiniteCharts.sharp a) :=
  GammaOrdinaryFiniteRing.lift_class B (sharpInvariant B) a

theorem full_forget_square (B : Base (M := M)) :
    (full B).comp (GammaOrdinaryFiniteRing.forget B) = (GammaOrdinaryRing.forget B).comp (GammaFiniteRVMaps.forget B) := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change full B (GammaOrdinaryFiniteRing.forget B (GammaFiniteRVPresentation.objectClass a)) =
    GammaOrdinaryRing.forget B (GammaFiniteRVMaps.forget B (GammaFiniteRVPresentation.objectClass a))
  rw [GammaOrdinaryFiniteRing.forget_class, full_class, GammaFiniteRVMaps.forget_class, GammaOrdinaryRing.forget_class]
  rfl

theorem sharp_forget_square (B : Base (M := M)) :
    (sharp B).comp (GammaOrdinaryFiniteRing.forget B) = (RESOrdinaryRing.forget B).comp (GammaFiniteRVMaps.sharp B) := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change sharp B (GammaOrdinaryFiniteRing.forget B (GammaFiniteRVPresentation.objectClass a)) =
    RESOrdinaryRing.forget B (GammaFiniteRVMaps.sharp B (GammaFiniteRVPresentation.objectClass a))
  rw [GammaOrdinaryFiniteRing.forget_class, sharp_class, GammaFiniteRVMaps.sharp_class, RESOrdinaryRing.forget_objectClass]
  exact RESOrdinaryRing.objectClass_iso
    (a := GammaOrdinaryFiniteCharts.sharp (GammaOrdinaryFiniteCharts.ofMeasured a)) (b := GammaFiniteRVCharts.sharp a)
    (GammaOrdinarySharpObjects.sameSupportIso (GammaOrdinaryFiniteCharts.toWeighted (GammaOrdinaryFiniteCharts.ofMeasured a)).toChart a.toChart rfl)

theorem sharp_full_square (B : Base (M := M)) :
    (RVOrdinaryMaps.ofRES B).comp (sharp B) = (GammaOrdinarySharpRingMap.sharp B).comp (full B) := by
  apply GammaOrdinaryFiniteRing.hom_ext B
  intro n a
  change RVOrdinaryMaps.ofRES B (sharp B (GammaOrdinaryFiniteRing.objectClass a)) =
    GammaOrdinarySharpRingMap.sharp B (full B (GammaOrdinaryFiniteRing.objectClass a))
  rw [sharp_class, full_class, RVOrdinaryMaps.ofRES_class, GammaOrdinarySharpRingMap.sharp_class]
  rfl

end DiamondIntegral.Section4.GammaOrdinaryFiniteMaps
