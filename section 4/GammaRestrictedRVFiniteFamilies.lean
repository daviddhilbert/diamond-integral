import «section 4».GammaRVFamilyIsomorphisms
import «section 4».GammaBoundedRVPartitions
import «section 4».GammaFiniteRVPartitions

/-! Actual RV-contracted finite-family bijections preserve class sums in
the intrinsic bounded and finite Gamma rings separately. Restrictions
retain their source bound or finite support. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRestrictedRVFiniteFamilies
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

namespace Bounded
open GammaBoundedRVCharts GammaBoundedRVPresentation GammaBoundedRVPartitions FiniteFamilyBijections

def familyClass {B : Base (M := M)} {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → BoundedChart B n) : ChartRing B :=
  ∑ i, objectClass (a i)

theorem familyClass_iso {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    {a : ι → BoundedChart B n} {b : κ → BoundedChart B n}
    (f : GammaRVFamilyIsomorphisms.Iso (fun i => (a i).toChart) (fun j => (b j).toChart)) : familyClass a = familyClass b := by
  let p := GammaRVFamilyIsomorphisms.partitionIso f
  let ha := fun i j => sourcePiece_subset f.equiv i j
  let hb := fun j i => sourcePiece_subset f.equiv.symm j i
  have hA : ∀ i, objectClass (a i) = ∑ j, objectClass (restrict (a i) (p.sourcePiece i j) (p.source_definable i j) (ha i j)) := by
    intro i
    exact class_partition Finset.univ (a i) (p.sourcePiece i) (p.source_definable i) (ha i)
      (fun j _ j' _ h => p.source_disjoint i j j' h) (p.source_cover i)
  have hB : ∀ j, objectClass (b j) = ∑ i, objectClass (restrict (b j) (p.targetPiece i j) (p.target_definable i j) (hb j i)) := by
    intro j
    exact class_partition Finset.univ (b j) (fun i => p.targetPiece i j) (fun i => p.target_definable i j) (hb j)
      (fun i _ i' _ h => p.target_disjoint j i i' h) (p.target_cover j)
  calc
    familyClass a = ∑ i, ∑ j, objectClass (restrict (a i) (p.sourcePiece i j) (p.source_definable i j) (ha i j)) :=
      Finset.sum_congr rfl (fun i _ => hA i)
    _ = ∑ i, ∑ j, objectClass (restrict (b j) (p.targetPiece i j) (p.target_definable i j) (hb j i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => class_iso (p.pieceIso i j))
    _ = ∑ j, ∑ i, objectClass (restrict (b j) (p.targetPiece i j) (p.target_definable i j) (hb j i)) := Finset.sum_comm
    _ = familyClass b := Finset.sum_congr rfl (fun j _ => (hB j).symm)

end Bounded

namespace Finite
open GammaFiniteRVCharts GammaFiniteRVPresentation GammaFiniteRVPartitions FiniteFamilyBijections

def familyClass {B : Base (M := M)} {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → FiniteChart B n) : ChartRing B :=
  ∑ i, objectClass (a i)

theorem familyClass_iso {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    {a : ι → FiniteChart B n} {b : κ → FiniteChart B n}
    (f : GammaRVFamilyIsomorphisms.Iso (fun i => (a i).toChart) (fun j => (b j).toChart)) : familyClass a = familyClass b := by
  let p := GammaRVFamilyIsomorphisms.partitionIso f
  let ha := fun i j => sourcePiece_subset f.equiv i j
  let hb := fun j i => sourcePiece_subset f.equiv.symm j i
  have hA : ∀ i, objectClass (a i) = ∑ j, objectClass (restrict (a i) (p.sourcePiece i j) (p.source_definable i j) (ha i j)) := by
    intro i
    exact class_partition Finset.univ (a i) (p.sourcePiece i) (p.source_definable i) (ha i)
      (fun j _ j' _ h => p.source_disjoint i j j' h) (p.source_cover i)
  have hB : ∀ j, objectClass (b j) = ∑ i, objectClass (restrict (b j) (p.targetPiece i j) (p.target_definable i j) (hb j i)) := by
    intro j
    exact class_partition Finset.univ (b j) (fun i => p.targetPiece i j) (fun i => p.target_definable i j) (hb j)
      (fun i _ i' _ h => p.target_disjoint j i i' h) (p.target_cover j)
  calc
    familyClass a = ∑ i, ∑ j, objectClass (restrict (a i) (p.sourcePiece i j) (p.source_definable i j) (ha i j)) :=
      Finset.sum_congr rfl (fun i _ => hA i)
    _ = ∑ i, ∑ j, objectClass (restrict (b j) (p.targetPiece i j) (p.target_definable i j) (hb j i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => class_iso (p.pieceIso i j))
    _ = ∑ j, ∑ i, objectClass (restrict (b j) (p.targetPiece i j) (p.target_definable i j) (hb j i)) := Finset.sum_comm
    _ = familyClass b := Finset.sum_congr rfl (fun j _ => (hB j).symm)

end Finite

end DiamondIntegral.Section4.GammaRestrictedRVFiniteFamilies
