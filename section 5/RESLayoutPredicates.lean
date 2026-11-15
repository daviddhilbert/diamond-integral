import «section 5».RESLayoutRecoding

/-! The primitive list of a complete layout witness includes every source,
target, stabilizer, coefficient and relation predicate, and the total graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem forall_mem_flatMap_iff {ι η : Type*} (L : List ι) (f : ι → List η) (P : η → Prop) :
    (∀ y ∈ L.flatMap f, P y) ↔ ∀ i ∈ L, ∀ y ∈ f i, P y := by
  constructor
  · exact fun h i hi y hy => h y (List.mem_flatMap.mpr ⟨i, hi, hy⟩)
  · intro h y hy
    obtain ⟨i, hi, hy⟩ := List.mem_flatMap.mp hy
    exact h i hi y hy

def RESLayoutStabilizationSchema.domainPredicates {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) : List ((a : ℕ) × GammaDomainFormula B p a sp) :=
  [⟨a, F.domain⟩, ⟨b, G.domain⟩] ++ W.stabilizer.domainPredicates ++
    W.source.domainPredicates ++ W.target.domainPredicates ++
      W.relations.flatMap (fun I => I.2.2.domainPredicates)

def RESLayoutStabilizationSchema.graphPredicates {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) : List ((a : ℕ) × (b : ℕ) × GammaRelationFormula B p a b sp) :=
  [⟨W.sourceArity, W.targetArity, W.graph⟩] ++ W.relations.flatMap (fun I => I.2.2.graphPredicates)

theorem RESLayoutStabilizationSchema.rowAgreement_iff_predicates
    (R : GammaParameterRecode B p q sp sq) {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) (z : Fin p → M) (t : Fin q → M) : W.RowAgreement R z t ↔
      (∀ D ∈ W.domainPredicates, R.DomainAgreement D.2 z t) ∧
      (∀ H ∈ W.graphPredicates, R.RelationAgreement H.2.2 z t) := by
  simp only [RowAgreement, domainPredicates, graphPredicates, List.forall_mem_append,
    forall_mem_flatMap_iff]
  simp_rw [RESExpressionSchema.rowAgreement_iff_predicates,
    RESExpressionRelationSchema.rowAgreement_iff_predicates]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [forall_and]
  tauto

end DiamondIntegral.Section5
