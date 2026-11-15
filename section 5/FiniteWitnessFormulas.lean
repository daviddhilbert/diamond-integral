import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Set.Function

/-! First-order validity formulas for the actual bijection graphs in a
finite witness package, uniformly in every structure of the language. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

def witnessRightUnique {P α β : Type*} [Finite β]
    (B : L.Formula (P ⊕ β)) (R : L.Formula (P ⊕ (α ⊕ β))) : L.Formula (P ⊕ α) :=
  ((B.relabel (Sum.map id Sum.inr) ⊓ R).relabel (Equiv.sumAssoc P α β).symm).iExsUnique β

theorem witnessRightUnique_realize {P α β M : Type*} [L.Structure M] [Finite β]
    (B : L.Formula (P ⊕ β)) (R : L.Formula (P ⊕ (α ⊕ β))) (v : P → M) (x : α → M) :
    (witnessRightUnique B R).Realize (Sum.elim v x) ↔
      ∃! y : β → M, B.Realize (Sum.elim v y) ∧ R.Realize (Sum.elim v (Sum.elim x y)) := by
  simp only [witnessRightUnique, Formula.realize_iExsUnique, Formula.realize_relabel, Formula.realize_inf]
  have ha (y : β → M) : Sum.elim (Sum.elim v x) y ∘ (Equiv.sumAssoc P α β).symm =
      Sum.elim v (Sum.elim x y) := by
    funext i
    cases i with
    | inl p => rfl
    | inr i => cases i <;> rfl
  have hb (y : β → M) : Sum.elim v (Sum.elim x y) ∘ Sum.map id Sum.inr = Sum.elim v y := by
    funext i
    cases i <;> rfl
  simp only [ha, hb]

def bijectionValidityFormula {P α β : Type*} [Finite α] [Finite β]
    (A : L.Formula (P ⊕ α)) (B : L.Formula (P ⊕ β))
    (R : L.Formula (P ⊕ (α ⊕ β))) : L.Formula P :=
  (A.imp (witnessRightUnique B R)).iAlls α ⊓
    (B.imp (witnessRightUnique A (R.relabel (Sum.map id (Equiv.sumComm α β))))).iAlls β

theorem bijectionValidityFormula_realize {P α β M : Type*} [L.Structure M] [Finite α] [Finite β]
    (A : L.Formula (P ⊕ α)) (B : L.Formula (P ⊕ β))
    (R : L.Formula (P ⊕ (α ⊕ β))) (v : P → M) :
    (bijectionValidityFormula A B R).Realize v ↔
      (∀ x : α → M, A.Realize (Sum.elim v x) →
        ∃! y : β → M, B.Realize (Sum.elim v y) ∧ R.Realize (Sum.elim v (Sum.elim x y))) ∧
      (∀ y : β → M, B.Realize (Sum.elim v y) →
        ∃! x : α → M, A.Realize (Sum.elim v x) ∧ R.Realize (Sum.elim v (Sum.elim x y))) := by
  simp only [bijectionValidityFormula, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    witnessRightUnique_realize, Formula.realize_relabel]
  have he (y : β → M) (x : α → M) :
      Sum.elim v (Sum.elim y x) ∘ Sum.map id (Equiv.sumComm α β) =
        Sum.elim v (Sum.elim x y) := by
    funext i
    cases i with
    | inl p => rfl
    | inr i => cases i <;> rfl
  simp only [he]

def setEqualityValidityFormula {P α : Type*} [Finite α]
    (A B : L.Formula (P ⊕ α)) : L.Formula P :=
  (A.imp B ⊓ B.imp A).iAlls α

theorem setEqualityValidityFormula_realize {P α M : Type*} [L.Structure M] [Finite α]
    (A B : L.Formula (P ⊕ α)) (v : P → M) :
    (setEqualityValidityFormula A B).Realize v ↔
      {x : α → M | A.Realize (Sum.elim v x)} = {x : α → M | B.Realize (Sum.elim v x)} := by
  simp only [setEqualityValidityFormula, Formula.realize_iAlls, Formula.realize_inf, Formula.realize_imp]
  constructor
  · intro h
    ext x
    exact ⟨(h x).1, (h x).2⟩
  · intro h x
    have hh := Set.ext_iff.mp h x
    exact ⟨hh.mp, hh.mpr⟩

def finiteWitnessValidityFormula {P ι : Type*} [Finite ι] (clauses : ι → L.Formula P) : L.Formula P :=
  Formula.iInf clauses

theorem finiteWitnessValidityFormula_realize {P ι M : Type*} [L.Structure M] [Finite ι]
    (clauses : ι → L.Formula P) (v : P → M) :
    (finiteWitnessValidityFormula clauses).Realize v ↔ ∀ i, (clauses i).Realize v := by
  simp only [finiteWitnessValidityFormula, Formula.realize_iInf]

end DiamondIntegral.Section5
