import «section 4».RVScissorComponents
import «section 4».RVTaggedPartitionIsomorphisms
import Mathlib.Tactic.Abel

/-! Isomorphism invariance and additivity for actual tagged disjoint
unions imply every weighted RV scissor relation. The proof uses actual
original-base piece isomorphisms, including different tuple arities. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDisjointInvariants
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure AdditiveInvariant (B : Base (M := M)) (R : Type*) [AddCommGroup R] where
  value : ∀ k, Chart B k → R
  iso : ∀ k (a b : Chart B k), Iso a b → value k a = value k b
  coproduct : ∀ k (a b : Chart B k), value k (RVTaggedCoproduct.coproduct a b) = value k a + value k b

theorem partition_value {B : Base (M := M)} {R : Type*} [AddCommGroup R] (f : AdditiveInvariant B R)
    {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    f.value k a.toChart = f.value k (outside a I hI).toChart + f.value k (inside a I hI).toChart :=
  (f.iso k _ _ (RVTaggedPartitionIsomorphisms.partitionTaggedIso a I hI)).symm.trans (f.coproduct k _ _)

theorem scissor_data {B : Base (M := M)} {R : Type*} [AddCommGroup R] (f : AdditiveInvariant B R)
    {n k : ℕ} (a b c d : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart)
    (hD : RVMeasuredGroup.packed d.toChart = RVMeasuredGroup.packed a.toChart ∩ RVMeasuredGroup.packed b.toChart) :
    f.value k c.toChart + f.value k d.toChart = f.value k a.toChart + f.value k b.toChart := by
  have hA := partition_value f a b.domain b.domain_definable
  have hU := partition_value f c b.domain b.domain_definable
  have hO := f.iso k _ _ (RVScissorComponents.outsideIso a b c hC)
  have hI := f.iso k _ _ (RVScissorComponents.insideLeftIso a b c d hC hD)
  have hJ := f.iso k _ _ (RVScissorComponents.insideUnionIso a b c hC)
  rw [hU, hA, hI, hJ, ← hO]
  abel

theorem scissor {B : Base (M := M)} {R : Type*} [AddCommGroup R] (f : AdditiveInvariant B R)
    {k : ℕ} (a b c d : Chart B k) (h : RVMeasuredGroup.Scissor a b c d) :
    f.value k c + f.value k d = f.value k a + f.value k b := by
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
  exact scissor_data f
    ⟨aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
    ⟨bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
    ⟨cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
    ⟨dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩ hU hI

end DiamondIntegral.Section4.RVDisjointInvariants
