import «section 4».RVAdmissibleFamilies
import «section 4».RVDisjointInvariants

/-! Disjoint-union additivity implies all weighted scissor relations
inside any of the verified object families. Only closure of the actual
objects used in the partition is required. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVAdmissibleFamilies
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem Family.outside_good {B : Base (M := M)} (F : Family B) {n k : ℕ} (a : Data B n k)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (ha : F.good k a.toChart) :
    F.good k (outside a I hI).toChart :=
  F.restrict n k a (a.domain \ I) (difference_definable B a.domain I a.domain_definable hI) (fun _ h => h.1) ha

theorem Family.inside_good {B : Base (M := M)} (F : Family B) {n k : ℕ} (a : Data B n k)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (ha : F.good k a.toChart) :
    F.good k (inside a I hI).toChart := F.restrict n k a (a.domain ∩ I) (a.domain_definable.inter hI) (fun _ h => h.1) ha

end DiamondIntegral.Section4.RVAdmissibleFamilies

namespace DiamondIntegral.Section4.RVAdmissibleDisjointInvariants
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions RVAdmissibleFamilies
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure AdditiveInvariant {B : Base (M := M)} (F : Family B) (R : Type*) [AddCommGroup R] where
  value : ∀ k (a : Chart B k), F.good k a → R
  iso : ∀ k (a b : Chart B k) (ha : F.good k a) (hb : F.good k b),
    Iso a b → value k a ha = value k b hb
  coproduct : ∀ k (a b : Chart B k) (ha : F.good k a) (hb : F.good k b),
    value k (RVTaggedCoproduct.coproduct a b) (F.coproduct k a b ha hb) = value k a ha + value k b hb

theorem partition_value {B : Base (M := M)} (F : Family B) {R : Type*} [AddCommGroup R]
    (f : AdditiveInvariant F R) {n k : ℕ} (a : Data B n k) (ha : F.good k a.toChart)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    f.value k a.toChart ha = f.value k (outside a I hI).toChart (F.outside_good a I hI ha) +
      f.value k (inside a I hI).toChart (F.inside_good a I hI ha) := by
  let hO := F.outside_good a I hI ha
  let hN := F.inside_good a I hI ha
  exact (f.iso k _ _ (F.coproduct k _ _ hO hN) ha
    (RVTaggedPartitionIsomorphisms.partitionTaggedIso a I hI)).symm.trans (f.coproduct k _ _ hO hN)

theorem scissor_data {B : Base (M := M)} (F : Family B) {R : Type*} [AddCommGroup R]
    (f : AdditiveInvariant F R) {n k : ℕ} (a b c d : Data B n k)
    (ha : F.good k a.toChart) (hb : F.good k b.toChart) (hc : F.good k c.toChart) (hd : F.good k d.toChart)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart)
    (hD : RVMeasuredGroup.packed d.toChart = RVMeasuredGroup.packed a.toChart ∩ RVMeasuredGroup.packed b.toChart) :
    f.value k c.toChart hc + f.value k d.toChart hd = f.value k a.toChart ha + f.value k b.toChart hb := by
  have hA := partition_value F f a ha b.domain b.domain_definable
  have hU := partition_value F f c hc b.domain b.domain_definable
  have hO := f.iso k _ _ (F.outside_good a b.domain b.domain_definable ha)
    (F.outside_good c b.domain b.domain_definable hc) (RVScissorComponents.outsideIso a b c hC)
  have hI := f.iso k _ _ (F.inside_good a b.domain b.domain_definable ha) hd (RVScissorComponents.insideLeftIso a b c d hC hD)
  have hJ := f.iso k _ _ (F.inside_good c b.domain b.domain_definable hc) hb (RVScissorComponents.insideUnionIso a b c hC)
  rw [hU, hA, hI, hJ, ← hO]
  abel

theorem scissor {B : Base (M := M)} (F : Family B) {R : Type*} [AddCommGroup R]
    (f : AdditiveInvariant F R) {k : ℕ} (a b c d : Chart B k)
    (ha : F.good k a) (hb : F.good k b) (hc : F.good k c) (hd : F.good k d) (h : RVMeasuredGroup.Scissor a b c d) :
    f.value k c hc + f.value k d hd = f.value k a ha + f.value k b hb := by
  rcases a with ⟨aN, aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
  rcases b with ⟨bN, bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
  rcases c with ⟨cN, cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
  rcases d with ⟨dN, dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩
  rcases h with ⟨hab, hac, had, hU, hI⟩
  change aN = bN at hab
  subst bN
  change aN = cN at hac
  subst cN
  change aN = dN at had
  subst dN
  exact scissor_data F f
    ⟨aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
    ⟨bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
    ⟨cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
    ⟨dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩ ha hb hc hd hU hI

end DiamondIntegral.Section4.RVAdmissibleDisjointInvariants
