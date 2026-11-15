import «section 5».RESBijectionRealization

/-! Canonical row labels preserve every actual native chart class through
an actual original-base underlying isomorphism, in arbitrary degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

def RESSetSchema.chartIso_of_row_eq (hc : CanonicalStructure.IsCanonical (M := M))
    (z : Fin p → M) (A : RVMeasuredCharts.RESChart ⟨B.real ∪ Set.range z, B.gamma⟩ k)
    (F : RESSetSchema B p A.arity sp) (hF : F.Valid hc z) (hrow : F.rowDomain z = A.domain) :
    RVUnderlyingIsomorphisms.Iso (F.chart hc z hF).toChart A.toChart := by
  let S := F.chart hc z hF
  have he : S.domain = A.domain := (F.chart_domain hc z hF).trans hrow
  refine RVUnderlyingIsomorphisms.ofMap S.toChart A.toChart
    (id : (Fin A.arity → M) → (Fin A.arity → M)) ?_ ?_
  · exact RVSharpCharts.identity_graph_definable _ _ S.domain_definable
  · change Set.BijOn id S.domain A.domain
    rw [he]
    exact Set.bijOn_id _

theorem RESSetSchema.native_class_of_row_eq (hc : CanonicalStructure.IsCanonical (M := M))
    (z : Fin p → M) (A : RVMeasuredCharts.RESChart ⟨B.real ∪ Set.range z, B.gamma⟩ k)
    (F : RESSetSchema B p A.arity sp) (hF : F.Valid hc z) (hrow : F.rowDomain z = A.domain) :
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass (F.chart hc z hF)) =
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass A) :=
  congrArg (RESDimensionFreeReduction.quotient _)
    (RESDimensionFreeRing.objectClass_iso _ _ (F.chartIso_of_row_eq hc z A hF hrow))

end DiamondIntegral.Section5
