import «section 4».GammaOrdinaryFamilyIsomorphisms
import «section 4».GammaOrdinarySharpRingMap
import «section 4».GammaRVFamilySharp

/-! Actual same-degree ordinary RV objects for finite Gamma unions.
The measured tagged-object construction is used only to construct the
underlying object; ordinary class formulas follow by forgetting volume.
Actual ordinary contracted family isomorphisms preserve the sharp class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFamilySharp
open GammaOrdinaryCharts GammaOrdinaryRing GammaOrdinaryFiniteFamilies
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sharpFamily (B : Base (M := M)) (n m : ℕ) (a : Fin m → Chart B n) : RVMeasuredCharts.Chart B n :=
  GammaRVFamilySharp.sharpFamily B n m (fun i => toWeighted (a i))

theorem sharpFamily_class (B : Base (M := M)) (n m : ℕ) (a : Fin m → Chart B n) :
    RVOrdinaryRing.objectClass (sharpFamily B n m a) =
      ∑ i, RVOrdinaryRing.objectClass (GammaOrdinaryCharts.sharpChart (a i)) := by
  have h := congrArg (RVOrdinaryRing.forget B)
    (GammaRVFamilySharp.sharpFamily_class B n m (fun i => toWeighted (a i)))
  simp only [map_sum, RVOrdinaryRing.forget_objectClass] at h
  exact h

theorem sharp_familyClass (B : Base (M := M)) (n m : ℕ) (a : Fin m → Chart B n) :
    GammaOrdinarySharpRingMap.sharp B (familyClass a) = RVOrdinaryRing.objectClass (sharpFamily B n m a) := by
  rw [sharpFamily_class]
  change GammaOrdinarySharpRingMap.sharp B (∑ i, objectClass (a i)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => GammaOrdinarySharpRingMap.sharp_class B (a i))

theorem sharpFamily_iso_class (B : Base (M := M)) {n m l : ℕ}
    {a : Fin m → Chart B n} {b : Fin l → Chart B n} (f : GammaOrdinaryFamilyIsomorphisms.Iso a b) :
    RVOrdinaryRing.objectClass (sharpFamily B n m a) = RVOrdinaryRing.objectClass (sharpFamily B n l b) := by
  rw [← sharp_familyClass, ← sharp_familyClass]
  exact congrArg (GammaOrdinarySharpRingMap.sharp B) (GammaOrdinaryFamilyIsomorphisms.familyClass_iso f)

end DiamondIntegral.Section4.GammaOrdinaryFamilySharp
