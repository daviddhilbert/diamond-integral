import «section 5».RESRelationTermSchemata

/-! The complete primitive predicate list of a native ideal term includes
every coefficient object and the entire generator graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def RESRelationTermSchema.domainPredicates (T : RESRelationTermSchema B p sp) :
    List ((a : ℕ) × GammaDomainFormula B p a sp) :=
  T.primitive.domainPredicates ++ T.coefficients.map (fun A => ⟨A.1, A.2.domain⟩)

def RESRelationTermSchema.graphPredicates (T : RESRelationTermSchema B p sp) :
    List ((a : ℕ) × (b : ℕ) × GammaRelationFormula B p a b sp) := T.primitive.graphPredicates

theorem RESRelationTermSchema.rowAgreement_iff_predicates
    (R : GammaParameterRecode B p q sp sq) (T : RESRelationTermSchema B p sp)
    (z : Fin p → M) (t : Fin q → M) : T.RowAgreement R z t ↔
      (∀ D ∈ T.domainPredicates, R.DomainAgreement D.2 z t) ∧
      (∀ H ∈ T.graphPredicates, R.RelationAgreement H.2.2 z t) := by
  rw [RowAgreement, T.primitive.rowAgreement_iff_predicates]
  simp only [domainPredicates, graphPredicates, List.forall_mem_append, List.forall_mem_map]
  tauto

end DiamondIntegral.Section5
