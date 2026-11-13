import «section 4».GammaOrdinaryFinitePartitions

/-! Finite formally tagged Gamma objects and their ring classes. Actual
ordinary RV-lifted isomorphisms between finite matching partitions preserve these
classes; products of families agree with the ring product. Labels carry
no Gamma coordinate and add no degree. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFiniteFamilies
open GammaOrdinaryCharts GammaOrdinaryRing GammaOrdinaryFinitePartitions GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def familyClass {B : Base (M := M)} {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Chart B n) : Ring B :=
  ∑ i, objectClass (a i)

theorem familyClass_empty {B : Base (M := M)} {ι : Type*} [Fintype ι] [IsEmpty ι]
    {n : ℕ} (a : ι → Chart B n) : familyClass a = 0 := by simp [familyClass]

theorem familyClass_singleton {B : Base (M := M)} {n : ℕ} (a : Chart B n) :
    familyClass (fun _ : Unit => a) = objectClass a := by simp [familyClass]

theorem familyClass_sum {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (a : ι → Chart B n) (b : κ → Chart B n) :
    familyClass (Sum.elim a b) = familyClass a + familyClass b := by
  simp only [familyClass, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem familyClass_product {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n m : ℕ} (a : ι → Chart B m) (b : κ → Chart B n) :
    familyClass (fun p : ι × κ => GammaOrdinaryCharts.product (a p.1) (b p.2)) = familyClass a * familyClass b := by
  simp only [familyClass, Fintype.sum_prod_type, class_product, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

structure PartitionIso {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (a : ι → Chart B n) (b : κ → Chart B n) where
  sourcePiece : ι → κ → Set (Fin n → Values.Gamma (M := M))
  targetPiece : ι → κ → Set (Fin n → Values.Gamma (M := M))
  source_definable : ∀ i j, GammaDefinable B (sourcePiece i j)
  target_definable : ∀ i j, GammaDefinable B (targetPiece i j)
  source_disjoint : ∀ i j j', j ≠ j' → Disjoint (sourcePiece i j) (sourcePiece i j')
  target_disjoint : ∀ j i i', i ≠ i' → Disjoint (targetPiece i j) (targetPiece i' j)
  source_cover : ∀ i, support Finset.univ (sourcePiece i) = (a i).support
  target_cover : ∀ j, support Finset.univ (fun i => targetPiece i j) = (b j).support
  pieceIso : ∀ i j, GammaOrdinaryCharts.Iso (restrict (a i) (sourcePiece i j) (source_definable i j))
    (restrict (b j) (targetPiece i j) (target_definable i j))

theorem familyClass_partitionIso {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} {a : ι → Chart B n} {b : κ → Chart B n} (f : PartitionIso a b) : familyClass a = familyClass b := by
  have ha : ∀ i, objectClass (a i) = ∑ j, objectClass (restrict (a i) (f.sourcePiece i j) (f.source_definable i j)) := by
    intro i
    exact class_partition Finset.univ (a i) (f.sourcePiece i) (f.source_definable i)
      (fun j _ j' _ h => f.source_disjoint i j j' h) (f.source_cover i)
  have hb : ∀ j, objectClass (b j) = ∑ i, objectClass (restrict (b j) (f.targetPiece i j) (f.target_definable i j)) := by
    intro j
    exact class_partition Finset.univ (b j) (fun i => f.targetPiece i j) (fun i => f.target_definable i j)
      (fun i _ i' _ h => f.target_disjoint j i i' h) (f.target_cover j)
  calc
    familyClass a = ∑ i, ∑ j, objectClass (restrict (a i) (f.sourcePiece i j) (f.source_definable i j)) :=
      Finset.sum_congr rfl (fun i _ => ha i)
    _ = ∑ i, ∑ j, objectClass (restrict (b j) (f.targetPiece i j) (f.target_definable i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => class_iso (f.pieceIso i j))
    _ = ∑ j, ∑ i, objectClass (restrict (b j) (f.targetPiece i j) (f.target_definable i j)) := Finset.sum_comm
    _ = familyClass b := Finset.sum_congr rfl (fun j _ => (hb j).symm)

theorem map_familyClass {B : Base (M := M)} {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Chart B n) {R : Type*} [CommRing R] (f : Ring B →+* R) :
    f (familyClass a) = ∑ i, f (objectClass (a i)) := map_sum f _ _

end DiamondIntegral.Section4.GammaOrdinaryFiniteFamilies
