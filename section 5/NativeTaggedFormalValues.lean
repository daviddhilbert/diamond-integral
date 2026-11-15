import «section 5».NativeDomainPresentations
import «section 5».RESFormalExpressions

/-! The actual old tagged layout has the formal sum of its component
expressions. Partition by fixed old degrees is a finite algebraic identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

theorem NativeDomainPresentationAt.taggedFinFamily_formal
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    ∀ (N : ℕ) (A : Fin N → GammaRVSet hc ⟨B.real ∪ Set.range z, B.gamma⟩)
      (P : ∀ i, NativeDomainPresentationAt B sp z (A i).2),
      (NativeDomainPresentationAt.taggedFinFamily B sp z hz N A P).expression.formalValue =
        ∑ i, (P i).expression.formalValue := by
  intro N
  induction N with
  | zero => intro A P; simp [NativeDomainPresentationAt.taggedFinFamily, RESExpressionSchema.formalValue,
      NativeDomainPresentationAt.empty]
  | succ N ih =>
    intro A P
    change (P 0).expression.formalValue +
      (NativeDomainPresentationAt.taggedFinFamily B sp z hz N (fun i => A i.succ) (fun i => P i.succ)).expression.formalValue = _
    rw [Fin.sum_univ_succ, ih]

theorem finite_degree_partition_sum {ι R : Type*} [AddCommMonoid R]
    (N : ℕ) (L : List ι) (degree : ι → ℕ) (weight : ι → R)
    (hdegree : ∀ x ∈ L, degree x < N) :
    (∑ k : Fin N, (L.map (fun x => if degree x = k.val then weight x else 0)).sum) =
      (L.map weight).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := hdegree x List.mem_cons_self
    have hL : ∀ y ∈ L, degree y < N := fun y hy => hdegree y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih hL]
    have heq (k : Fin N) : degree x = k.val ↔ k = ⟨degree x, hx⟩ := by
      rw [Fin.ext_iff]
      exact eq_comm
    simp_rw [heq]
    simp

end DiamondIntegral.Section5
