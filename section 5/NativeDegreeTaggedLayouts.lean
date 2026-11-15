import «section 5».NativeDegreePresentations
import «section 5».NativeTaggedFormalValues

/-! The old finite degree-grouped total has an original-base expression
presentation with the formal sum of every original component exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RESFiniteWitness
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {p : ℕ}

theorem presented_degree_tagged_expression_exists (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) (N : ℕ)
    (hdegree : ∀ U ∈ L, U.1.1 < N) :
    ∃ P : NativeDomainPresentationAt B sp z
      (taggedRVFinFamily hc ⟨B.real ∪ Set.range z, B.gamma⟩ N
        (fun i => ⟨(positiveFamilyAtDegree hc _ i.val (presentedOldObjects L)).obj.arity,
          (positiveFamilyAtDegree hc _ i.val (presentedOldObjects L)).obj.domain⟩)).2,
      P.expression.formalValue = (L.map (fun U => U.2.expression.formalValue)).sum := by
  have hpoint (i : Fin N) := presented_degree_expression_exists B sp z hz L i.val
  choose P hP using hpoint
  let A : Fin N → GammaRVSet hc ⟨B.real ∪ Set.range z, B.gamma⟩ := fun i =>
    ⟨(positiveFamilyAtDegree hc _ i.val (presentedOldObjects L)).obj.arity,
      (positiveFamilyAtDegree hc _ i.val (presentedOldObjects L)).obj.domain⟩
  let T := NativeDomainPresentationAt.taggedFinFamily B sp z hz N A P
  refine ⟨T, ?_⟩
  calc
    T.expression.formalValue = ∑ i, (P i).expression.formalValue :=
      NativeDomainPresentationAt.taggedFinFamily_formal B sp z hz N A P
    _ = ∑ i : Fin N, presentedDegreeFormal i.val L := Finset.sum_congr rfl (fun i _ => hP i)
    _ = (L.map (fun U => U.2.expression.formalValue)).sum :=
      finite_degree_partition_sum N L (fun U => U.1.1) (fun U => U.2.expression.formalValue) hdegree

end DiamondIntegral.Section5
