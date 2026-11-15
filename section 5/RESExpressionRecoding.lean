import «section 5».RESExpressionSchemata

/-! Exact agreement of the finitely many leaf rows preserves the full
literal native RES expression and its validity, including all tags. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 DiamondIntegral.Section4.FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def RESExpressionSchema.recode (R : GammaParameterRecode B p q sp sq) :
    {a : ℕ} → RESExpressionSchema B p sp a → RESExpressionSchema B q sq a
  | _, .atom F => .atom (F.recode R)
  | _, .empty => .empty
  | _, .sum F G => .sum (F.recode R) (G.recode R)
  | _, .product F G => .product (F.recode R) (G.recode R)

def RESExpressionSchema.RowAgreement (R : GammaParameterRecode B p q sp sq) :
    {a : ℕ} → RESExpressionSchema B p sp a → (Fin p → M) → (Fin q → M) → Prop
  | _, .atom F, z, t => R.DomainAgreement F.domain z t
  | _, .empty, _, _ => True
  | _, .sum F G, z, t => F.RowAgreement R z t ∧ G.RowAgreement R z t
  | _, .product F G, z, t => F.RowAgreement R z t ∧ G.RowAgreement R z t

def RESExpressionSchema.domainPredicates : {a : ℕ} → RESExpressionSchema B p sp a →
    List ((a : ℕ) × GammaDomainFormula B p a sp)
  | _, .atom F => [⟨_, F.domain⟩]
  | _, .empty => []
  | _, .sum F G => F.domainPredicates ++ G.domainPredicates
  | _, .product F G => F.domainPredicates ++ G.domainPredicates

theorem RESExpressionSchema.rowAgreement_iff_predicates
    (R : GammaParameterRecode B p q sp sq) {a : ℕ} (E : RESExpressionSchema B p sp a)
    (z : Fin p → M) (t : Fin q → M) : E.RowAgreement R z t ↔
      ∀ D ∈ E.domainPredicates, R.DomainAgreement D.2 z t := by
  induction E with
  | atom F => simp [RowAgreement, domainPredicates]
  | empty => simp [RowAgreement, domainPredicates]
  | sum F G ihF ihG =>
    change (_ ∧ _) ↔ ∀ D ∈ F.domainPredicates ++ G.domainPredicates, R.DomainAgreement D.2 z t
    rw [List.forall_mem_append]
    exact and_congr ihF ihG
  | product F G ihF ihG =>
    change (_ ∧ _) ↔ ∀ D ∈ F.domainPredicates ++ G.domainPredicates, R.DomainAgreement D.2 z t
    rw [List.forall_mem_append]
    exact and_congr ihF ihG

theorem RESExpressionSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) {a : ℕ} (E : RESExpressionSchema B p sp a)
    (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hrow : E.RowAgreement R z t) : E.Valid hc z ↔ (E.recode R).Valid hc t := by
  induction E with
  | atom F => exact F.recode_valid_iff hc R z t hz ht hrow
  | empty => exact iff_of_true hz ht
  | sum F G ihF ihG => exact and_congr (ihF hrow.1) (ihG hrow.2)
  | product F G ihF ihG => exact and_congr (ihF hrow.1) (ihG hrow.2)

theorem RESExpressionSchema.recode_row_iff
    (R : GammaParameterRecode B p q sp sq) {a : ℕ} (E : RESExpressionSchema B p sp a)
    (z : Fin p → M) (t : Fin q → M) (hrow : E.RowAgreement R z t) (w : Fin a → M) :
    w ∈ E.setSchema.rowDomain z ↔ w ∈ (E.recode R).setSchema.rowDomain t := by
  induction E with
  | atom F => exact hrow w
  | empty => rfl
  | sum F G ihF ihG =>
    rw [show (RESExpressionSchema.sum F G).setSchema = F.setSchema.sum G.setSchema from rfl,
      show ((RESExpressionSchema.sum F G).recode R).setSchema =
        (F.recode R).setSchema.sum (G.recode R).setSchema from rfl,
      RESSetSchema.sum_row, RESSetSchema.sum_row]
    exact or_congr (exists_congr (fun x => and_congr (ihF hrow.1 x) Iff.rfl))
      (exists_congr (fun y => and_congr (ihG hrow.2 y) Iff.rfl))
  | product F G ihF ihG =>
    rw [show (RESExpressionSchema.product F G).setSchema = F.setSchema.product G.setSchema from rfl,
      show ((RESExpressionSchema.product F G).recode R).setSchema =
        (F.recode R).setSchema.product (G.recode R).setSchema from rfl,
      RESSetSchema.product_row, RESSetSchema.product_row]
    exact and_congr (ihF hrow.1 _) (ihG hrow.2 _)

end DiamondIntegral.Section5
