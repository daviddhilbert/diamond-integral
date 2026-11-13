import «section 4».FieldPositiveExpressions
import «section 4».DefinableBiUniqueRelation

/-! A uniform first-order formula expressing that a relation is a
bijection between two definable field sets. All parameters remain free,
so an entire finite diagram can be specialized by the Lefschetz theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.BiUniqueFormula

theorem sumElim_assoc {P : Type*} {α : Type*} {β : Type*} {F : Type*}
    (v : P → F) (x : α → F) (y : β → F) :
    Sum.elim (Sum.elim v x) y ∘ (Equiv.sumAssoc P α β).symm =
      Sum.elim v (Sum.elim x y) := by
  funext i
  cases i with
  | inl p => rfl
  | inr i => cases i <;> rfl

theorem sumElim_swap {α : Type*} {β : Type*} {F : Type*} (x : α → F) (y : β → F) :
    Sum.elim y x ∘ (Equiv.sumComm α β) = Sum.elim x y := by
  funext i
  cases i <;> rfl

def rightUnique {P : Type*} {α : Type*} {β : Type*} [Finite β]
    (B : Language.ring.Formula (P ⊕ β)) (R : Language.ring.Formula (P ⊕ (α ⊕ β))) :
    Language.ring.Formula (P ⊕ α) :=
  ((B.relabel (Sum.map id Sum.inr) ⊓ R).relabel
    (Equiv.sumAssoc P α β).symm).iExsUnique β

theorem rightUnique_realize {P : Type*} {α : Type*} {β : Type*} {F : Type*}
    [Field F] [FirstOrder.Ring.CompatibleRing F] [Finite β]
    (B : Language.ring.Formula (P ⊕ β)) (R : Language.ring.Formula (P ⊕ (α ⊕ β)))
    (v : P → F) (x : α → F) :
    (rightUnique B R).Realize (Sum.elim v x) ↔
      ∃! y : β → F, B.Realize (Sum.elim v y) ∧ R.Realize (Sum.elim v (Sum.elim x y)) := by
  simp only [rightUnique, Formula.realize_iExsUnique, Formula.realize_relabel, Formula.realize_inf]
  have ha (y : β → F) : Sum.elim (Sum.elim v x) y ∘ (Equiv.sumAssoc P α β).symm =
      Sum.elim v (Sum.elim x y) := sumElim_assoc v x y
  simp only [ha]
  have hb (y : β → F) : Sum.elim v (Sum.elim x y) ∘ Sum.map id Sum.inr = Sum.elim v y := by
    funext i
    cases i <;> rfl
  simp only [hb]

def formula {P : Type*} {α : Type*} {β : Type*} [Finite α] [Finite β]
    (A : Language.ring.Formula (P ⊕ α)) (B : Language.ring.Formula (P ⊕ β))
    (R : Language.ring.Formula (P ⊕ (α ⊕ β))) : Language.ring.Formula P :=
  (A.imp (rightUnique B R)).iAlls α ⊓
    (B.imp (rightUnique A (R.relabel (Sum.map id (Equiv.sumComm α β))))).iAlls β

theorem formula_realize {P : Type*} {α : Type*} {β : Type*} {F : Type*}
    [Field F] [FirstOrder.Ring.CompatibleRing F] [Finite α] [Finite β]
    (A : Language.ring.Formula (P ⊕ α)) (B : Language.ring.Formula (P ⊕ β))
    (R : Language.ring.Formula (P ⊕ (α ⊕ β))) (v : P → F) :
    (formula A B R).Realize v ↔
      DefinableBiUniqueRelation.BiUnique {x | A.Realize (Sum.elim v x)}
        {y | B.Realize (Sum.elim v y)} {w | R.Realize (Sum.elim v w)} := by
  simp only [formula, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    rightUnique_realize, Formula.realize_relabel]
  have he (y : β → F) (x : α → F) :
      Sum.elim v (Sum.elim y x) ∘ Sum.map id (Equiv.sumComm α β) =
        Sum.elim v (Sum.elim x y) := by
    funext i
    cases i with
    | inl p => rfl
    | inr i => cases i <;> rfl
  simp only [he]
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · intro h
    exact ⟨h.left, h.right⟩

end DiamondIntegral.Section4.BiUniqueFormula
