import «section 5».RESExpressionRelations

/-! Complete relation certificates recode functorially, including both
value-fibre rows, coefficient expressions and all orientation choices. -/
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

def RESExpressionRelationSchema.recode (R : GammaParameterRecode B p q sp sq) :
    {a b : ℕ} → RESExpressionRelationSchema B p sp a b → RESExpressionRelationSchema B q sq a b
  | _, _, .underlying F G H => .underlying (F.recode R) (G.recode R) (H.recode R)
  | _, _, .fibre F G => .fibre (F.recode R) (G.recode R)
  | _, _, .reverse I => .reverse (I.recode R)
  | _, _, .multiplyLeft C I => .multiplyLeft (C.recode R) (I.recode R)

def RESExpressionRelationSchema.RowAgreement (R : GammaParameterRecode B p q sp sq) :
    {a b : ℕ} → RESExpressionRelationSchema B p sp a b → (Fin p → M) → (Fin q → M) → Prop
  | _, _, .underlying F G H, z, t => R.DomainAgreement F.domain z t ∧
      R.DomainAgreement G.domain z t ∧ R.RelationAgreement H.graph z t
  | _, _, .fibre F G, z, t => R.DomainAgreement F.domain z t ∧ R.DomainAgreement G.domain z t
  | _, _, .reverse I, z, t => I.RowAgreement R z t
  | _, _, .multiplyLeft C I, z, t => C.RowAgreement R z t ∧ I.RowAgreement R z t

theorem RESExpressionRelationSchema.expressions_recode (R : GammaParameterRecode B p q sp sq)
    (I : RESExpressionRelationSchema B p sp a b) :
    (I.recode R).leftExpression = I.leftExpression.recode R ∧
      (I.recode R).rightExpression = I.rightExpression.recode R := by
  induction I with
  | underlying F G H => exact ⟨rfl, rfl⟩
  | fibre F G => exact ⟨rfl, rfl⟩
  | reverse I ih => exact ⟨ih.2, ih.1⟩
  | multiplyLeft C I ih =>
    exact ⟨congrArg (RESExpressionSchema.product (C.recode R)) ih.1,
      congrArg (RESExpressionSchema.product (C.recode R)) ih.2⟩

theorem RESExpressionRelationSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (I : RESExpressionRelationSchema B p sp a b)
    (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hrow : I.RowAgreement R z t) : I.Valid hc z ↔ (I.recode R).Valid hc t := by
  induction I with
  | underlying F G H => exact H.recode_valid_iff hc R z t hz ht hrow.1 hrow.2.1 hrow.2.2
  | fibre F G =>
    exact and_congr (F.recode_valid_iff hc R z t hz ht hrow.1)
      (G.recode_valid_iff hc R z t hz ht hrow.2)
  | reverse I ih => exact ih hrow
  | multiplyLeft C I ih => exact and_congr (C.recode_valid_iff hc R z t hz ht hrow.1) (ih hrow.2)

def RESExpressionRelationSchema.domainPredicates : {a b : ℕ} → RESExpressionRelationSchema B p sp a b →
    List ((a : ℕ) × GammaDomainFormula B p a sp)
  | _, _, .underlying F G _ => [⟨_, F.domain⟩, ⟨_, G.domain⟩]
  | _, _, .fibre F G => [⟨1, F.domain⟩, ⟨1, G.domain⟩]
  | _, _, .reverse I => I.domainPredicates
  | _, _, .multiplyLeft C I => C.domainPredicates ++ I.domainPredicates

def RESExpressionRelationSchema.graphPredicates : {a b : ℕ} → RESExpressionRelationSchema B p sp a b →
    List ((a : ℕ) × (b : ℕ) × GammaRelationFormula B p a b sp)
  | _, _, .underlying _ _ H => [⟨_, _, H.graph⟩]
  | _, _, .fibre _ _ => []
  | _, _, .reverse I => I.graphPredicates
  | _, _, .multiplyLeft _ I => I.graphPredicates

theorem RESExpressionRelationSchema.rowAgreement_iff_predicates
    (R : GammaParameterRecode B p q sp sq) (I : RESExpressionRelationSchema B p sp a b)
    (z : Fin p → M) (t : Fin q → M) : I.RowAgreement R z t ↔
      (∀ D ∈ I.domainPredicates, R.DomainAgreement D.2 z t) ∧
      (∀ H ∈ I.graphPredicates, R.RelationAgreement H.2.2 z t) := by
  induction I with
  | underlying F G H => simp [RowAgreement, domainPredicates, graphPredicates, and_assoc]
  | fibre F G => simp [RowAgreement, domainPredicates, graphPredicates]
  | reverse I ih => exact ih
  | multiplyLeft C I ih =>
    change (_ ∧ _) ↔ (∀ D ∈ C.domainPredicates ++ I.domainPredicates, R.DomainAgreement D.2 z t) ∧ _
    rw [List.forall_mem_append, C.rowAgreement_iff_predicates, ih]
    tauto

end DiamondIntegral.Section5
