import «section 5».RVEvaluationEqualityRecoding
import «section 5».RVRectanglePredicateLists

/-! One finite original predicate list retains both rectangle packages,
all Euler witnesses, whole relation graphs and the stabilized total graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag} {kind : EulerKind}

theorem original_forall_ofFn_iff {α : Type*} {n : ℕ} (f : Fin n → α) (P : α → Prop) :
    (∀ x ∈ List.ofFn f, P x) ↔ ∀ i, P (f i) := by
  constructor
  · exact fun h i => h (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro h x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact h i

def RVEvaluationEqualitySchema.domainPredicates
    {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) : List ((a : ℕ) × GammaDomainFormula B p a sp) :=
  [⟨a,D⟩,⟨b,E⟩,⟨1,W.torus.domain⟩] ++
    (List.ofFn (fun i : Fin W.leftRectangles.size => (W.leftRectangles.cells i).domainPredicates)).flatten ++
    (List.ofFn (fun i : Fin W.rightRectangles.size => (W.rightRectangles.cells i).domainPredicates)).flatten ++
    W.stabilizer.domainPredicates ++ W.source.domainPredicates ++ W.target.domainPredicates ++
    W.relations.flatMap RESWholeRelationCertificate.domainPredicates

def RVEvaluationEqualitySchema.graphPredicates
    {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) :
    List ((a : ℕ) × (b : ℕ) × GammaRelationFormula B p a b sp) :=
  [⟨W.sourceArity,W.targetArity,W.graph⟩] ++
    List.ofFn (fun i : Fin W.leftRectangles.size =>
      ⟨a,(W.leftRectangles.cells i).residueArity+(W.leftRectangles.cells i).freeArity,(W.leftRectangles.cells i).graph⟩) ++
    List.ofFn (fun i : Fin W.rightRectangles.size =>
      ⟨b,(W.rightRectangles.cells i).residueArity+(W.rightRectangles.cells i).freeArity,(W.rightRectangles.cells i).graph⟩) ++
    W.relations.flatMap RESWholeRelationCertificate.graphPredicates

theorem RVEvaluationEqualitySchema.rowAgreement_iff_predicates
    (R : GammaParameterRecode B p q sp sq)
    {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) (z : Fin p → M) (t : Fin q → M) :
    W.RowAgreement R z t ↔
      (∀ D ∈ W.domainPredicates, R.DomainAgreement D.2 z t) ∧
      (∀ H ∈ W.graphPredicates, R.RelationAgreement H.2.2 z t) := by
  simp only [RowAgreement,domainPredicates,graphPredicates,List.forall_mem_append,
    List.flatten_eq_flatMap,forall_mem_flatMap_iff,original_forall_ofFn_iff]
  simp_rw [RVRectanglePieceSchema.rowAgreement_iff_predicates,
    RESExpressionSchema.rowAgreement_iff_predicates,RESWholeRelationCertificate.rowAgreement_iff_predicates]
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,forall_and]
  tauto

end DiamondIntegral.Section5
