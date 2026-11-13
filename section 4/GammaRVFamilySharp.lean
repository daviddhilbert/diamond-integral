import «section 4».GammaRVFamilyIsomorphisms
import «section 4».GammaRVMapGradings
import «section 4».RVTaggedCoproduct

/-! The full proper RV preimage of every finite Gamma union is an actual
same-degree RV chart, built with named degree-zero tags. Its class is the
sharp ring image of the family class and is invariant under the actual
RV-contracted family isomorphisms. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRVFamilySharp
open GammaWeightedCharts GammaRVChartPresentation GammaRVFiniteFamilies
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sharpFamily (B : Base (M := M)) (n : ℕ) : (m : ℕ) → (Fin m → Chart B n) → RVMeasuredCharts.Chart B n
  | 0, _ => (RVChartDisjointUnion.empty B 0 n).toChart
  | m + 1, a => RVTaggedCoproduct.coproduct (RVSharpCharts.sharpChart (a 0)) (sharpFamily B n m (fun i => a i.succ))

theorem sharpFamily_class (B : Base (M := M)) (n m : ℕ) (a : Fin m → Chart B n) :
    RVChartRing.objectClass (sharpFamily B n m a) = ∑ i, RVChartRing.objectClass (RVSharpCharts.sharpChart (a i)) := by
  induction m with
  | zero =>
    simpa only [Fin.sum_univ_zero] using RVChartRing.objectClass_empty (sharpFamily B n 0 a) rfl
  | succ m ih =>
    rw [sharpFamily, RVTaggedCoproduct.class_coproduct, ih, Fin.sum_univ_succ]

theorem sharp_familyClass (B : Base (M := M)) (n m : ℕ) (a : Fin m → Chart B n) :
    RVSharpRingMap.sharp B (familyClass a) = RVChartRing.objectClass (sharpFamily B n m a) := by
  rw [sharpFamily_class]
  change RVSharpRingMap.sharp B (∑ i, objectClass (a i)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => RVSharpRingMap.sharp_class B (a i))

theorem familyClass_mem (B : Base (M := M)) {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Chart B n) :
    familyClass a ∈ GammaRVGrading.gradedPiece B n :=
  (GammaRVGrading.gradedPiece B n).sum_mem (fun i _ => GammaRVGrading.class_mem B (a i))

theorem sharpFamily_iso_class (B : Base (M := M)) {n m l : ℕ}
    {a : Fin m → Chart B n} {b : Fin l → Chart B n} (f : GammaRVFamilyIsomorphisms.Iso a b) :
    RVChartRing.objectClass (sharpFamily B n m a) = RVChartRing.objectClass (sharpFamily B n l b) := by
  rw [← sharp_familyClass, ← sharp_familyClass]
  exact congrArg (RVSharpRingMap.sharp B) (GammaRVFamilyIsomorphisms.familyClass_iso f)

end DiamondIntegral.Section4.GammaRVFamilySharp
