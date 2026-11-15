import «section 5».RESLayoutPredicates

/-! Finite certificates may also retain an actual bijection between
whole positive expressions. This preserves literal nested layouts while
transporting a finite native quotient witness through preparation. -/
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
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

inductive RESWholeRelationCertificate (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) where
  | original {a b : ℕ} (relation : RESExpressionRelationSchema B p sp a b)
  | whole {a b : ℕ} (left : RESExpressionSchema B p sp a) (right : RESExpressionSchema B p sp b)
      (bijection : RESExpressionBijectionSchema left right)

def RESWholeRelationCertificate.leftExpression : RESWholeRelationCertificate B p sp →
    (a : ℕ) × RESExpressionSchema B p sp a
  | .original R => ⟨_,R.leftExpression⟩
  | .whole E _ _ => ⟨_,E⟩

def RESWholeRelationCertificate.rightExpression : RESWholeRelationCertificate B p sp →
    (a : ℕ) × RESExpressionSchema B p sp a
  | .original R => ⟨_,R.rightExpression⟩
  | .whole _ F _ => ⟨_,F⟩

def RESWholeRelationCertificate.Valid (hc : CanonicalStructure.IsCanonical (M := M)) :
    RESWholeRelationCertificate B p sp → (Fin p → M) → Prop
  | .original R,z => R.Valid hc z
  | .whole _ _ H,z => H.Valid hc z

theorem RESWholeRelationCertificate.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : RESWholeRelationCertificate B p sp) : DefinableOverBase B sp {z | C.Valid hc z} := by
  cases C with
  | original R => exact R.valid_definable hc
  | whole E F H => exact H.valid_definable hc

theorem RESWholeRelationCertificate.expressions_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (C : RESWholeRelationCertificate B p sp) (z : Fin p → M) (hv : C.Valid hc z) :
    C.leftExpression.2.Valid hc z ∧ C.rightExpression.2.Valid hc z := by
  cases C with
  | original R => exact R.expressions_valid hc z hv
  | whole E F H => exact ⟨hv.1,hv.2.1⟩

theorem RESWholeRelationCertificate.native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (C : RESWholeRelationCertificate B p sp) (z : Fin p → M) (hv : C.Valid hc z) :
    C.leftExpression.2.nativeValue hc z (C.expressions_valid hc z hv).1 =
      C.rightExpression.2.nativeValue hc z (C.expressions_valid hc z hv).2 := by
  cases C with
  | original R => exact R.native_equality hc z hv
  | whole E F H => exact H.native_equality hc z hv

def RESWholeRelationCertificate.recode (R : GammaParameterRecode B p q sp sq) :
    RESWholeRelationCertificate B p sp → RESWholeRelationCertificate B q sq
  | .original C => .original (C.recode R)
  | .whole E F H => .whole (E.recode R) (F.recode R) (H.recode R)

def RESWholeRelationCertificate.RowAgreement (R : GammaParameterRecode B p q sp sq) :
    RESWholeRelationCertificate B p sp → (Fin p → M) → (Fin q → M) → Prop
  | .original C,z,t => C.RowAgreement R z t
  | .whole E F H,z,t => E.RowAgreement R z t ∧ F.RowAgreement R z t ∧ R.RelationAgreement H.graph z t

theorem RESWholeRelationCertificate.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (C : RESWholeRelationCertificate B p sp)
    (z : Fin p → M) (t : Fin q → M) (hz : ∀ i, sortEval (sp i) (z i))
    (ht : ∀ i, sortEval (sq i) (t i)) (hr : C.RowAgreement R z t) :
    C.Valid hc z ↔ (C.recode R).Valid hc t := by
  cases C with
  | original C => exact C.recode_valid_iff hc R z t hz ht hr
  | whole E F H => exact H.recode_valid_iff hc R z t hz ht hr.1 hr.2.1 hr.2.2

theorem RESWholeRelationCertificate.left_formal_recode
    (R : GammaParameterRecode B p q sp sq) (C : RESWholeRelationCertificate B p sp) :
    (C.recode R).leftExpression.2.formalValue = formalSchemaRecode R C.leftExpression.2.formalValue := by
  cases C with
  | original C =>
    exact (congrArg RESExpressionSchema.formalValue (C.expressions_recode R).1).trans
      (C.leftExpression.formalValue_recode R)
  | whole E F H => exact E.formalValue_recode R

theorem RESWholeRelationCertificate.right_formal_recode
    (R : GammaParameterRecode B p q sp sq) (C : RESWholeRelationCertificate B p sp) :
    (C.recode R).rightExpression.2.formalValue = formalSchemaRecode R C.rightExpression.2.formalValue := by
  cases C with
  | original C =>
    exact (congrArg RESExpressionSchema.formalValue (C.expressions_recode R).2).trans
      (C.rightExpression.formalValue_recode R)
  | whole E F H => exact F.formalValue_recode R

def RESWholeRelationCertificate.domainPredicates : RESWholeRelationCertificate B p sp →
    List ((a : ℕ) × GammaDomainFormula B p a sp)
  | .original C => C.domainPredicates
  | .whole E F _ => E.domainPredicates ++ F.domainPredicates

def RESWholeRelationCertificate.graphPredicates : RESWholeRelationCertificate B p sp →
    List ((a : ℕ) × (b : ℕ) × GammaRelationFormula B p a b sp)
  | .original C => C.graphPredicates
  | .whole E F H => [⟨_,_,H.graph⟩]

theorem RESWholeRelationCertificate.rowAgreement_iff_predicates
    (R : GammaParameterRecode B p q sp sq) (C : RESWholeRelationCertificate B p sp)
    (z : Fin p → M) (t : Fin q → M) : C.RowAgreement R z t ↔
    (∀ D ∈ C.domainPredicates, R.DomainAgreement D.2 z t) ∧
      (∀ H ∈ C.graphPredicates, R.RelationAgreement H.2.2 z t) := by
  cases C with
  | original C => exact C.rowAgreement_iff_predicates R z t
  | whole E F H =>
    simp only [RowAgreement,domainPredicates,graphPredicates,List.forall_mem_append,
      List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,
      ←RESExpressionSchema.rowAgreement_iff_predicates]
    tauto

end DiamondIntegral.Section5
