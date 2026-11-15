import «section 5».FiniteFibreValidity

/-! A finite first-order certificate for the number of distinct quotient
values on a definable set. Equal-value codes need no selected representatives;
this applies in particular to full RV value patterns, including zero. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

def valueCollisionFormula {P α : Type*} [Finite α] (N : ℕ)
    (A : L.Formula (P ⊕ α)) (E : L.Formula (P ⊕ (α ⊕ α))) :
    L.Formula (P ⊕ (Fin (N + 1) × α)) :=
  Formula.iInf (fun i : Fin (N + 1) => A.relabel (Sum.map id (fun a => (i, a)))) ⊓
    Formula.iInf (fun i : Fin (N + 1) => Formula.iInf (fun j : Fin (N + 1) =>
      if i = j then ⊤ else
        (E.relabel (Sum.map id (Sum.elim (fun a => (i, a)) (fun a => (j, a))))).not))

theorem valueCollisionFormula_realize {P α M Q : Type*} [Finite α] [L.Structure M]
    (N : ℕ) (A : L.Formula (P ⊕ α)) (E : L.Formula (P ⊕ (α ⊕ α)))
    (v : P → M) (q : (α → M) → Q)
    (hE : ∀ x y, E.Realize (Sum.elim v (Sum.elim x y)) ↔ q x = q y)
    (z : Fin (N + 1) × α → M) :
    (valueCollisionFormula N A E).Realize (Sum.elim v z) ↔
      (∀ i, A.Realize (Sum.elim v (fun a => z (i, a)))) ∧
        Function.Injective (fun i => q (fun a => z (i, a))) := by
  simp only [valueCollisionFormula, Formula.realize_inf, Formula.realize_iInf,
    Formula.realize_relabel]
  have hA (i : Fin (N + 1)) : Sum.elim v z ∘ Sum.map id (fun a => (i, a)) =
      Sum.elim v (fun a => z (i, a)) := by funext t; cases t <;> rfl
  have hR (i j : Fin (N + 1)) :
      Sum.elim v z ∘ Sum.map id (Sum.elim (fun a => (i, a)) (fun a => (j, a))) =
        Sum.elim v (Sum.elim (fun a => z (i, a)) (fun a => z (j, a))) := by
    funext t
    cases t with
    | inl p => rfl
    | inr t => cases t <;> rfl
  simp only [hA]
  apply and_congr_right
  intro _
  constructor
  · intro h i j hij
    by_contra hn
    have hh := h i j
    rw [if_neg hn, Formula.realize_not, Formula.realize_relabel, hR, hE] at hh
    exact hh hij
  · intro h i j
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, Formula.realize_not, Formula.realize_relabel, hR, hE]
      exact fun he => hij (h he)

def finiteValueValidityFormula {P α : Type*} [Finite α] (N : ℕ)
    (A : L.Formula (P ⊕ α)) (E : L.Formula (P ⊕ (α ⊕ α))) : L.Formula P :=
  (valueCollisionFormula N A E).not.iAlls (Fin (N + 1) × α)

theorem finiteValueValidityFormula_card {P α M Q : Type*} [Finite α] [L.Structure M]
    (N : ℕ) (A : L.Formula (P ⊕ α)) (E : L.Formula (P ⊕ (α ⊕ α)))
    (v : P → M) (q : (α → M) → Q)
    (hE : ∀ x y, E.Realize (Sum.elim v (Sum.elim x y)) ↔ q x = q y) :
    (finiteValueValidityFormula N A E).Realize v ↔
      (q '' {x | A.Realize (Sum.elim v x)}).Finite ∧
        (q '' {x | A.Realize (Sum.elim v x)}).ncard ≤ N := by
  simp only [finiteValueValidityFormula, Formula.realize_iAlls, Formula.realize_not,
    valueCollisionFormula_realize N A E v q hE]
  rw [← no_injective_fin_iff_card_bound]
  constructor
  · intro h f hf
    have hx (i : Fin (N + 1)) : ∃ x, A.Realize (Sum.elim v x) ∧ q x = (f i).val := (f i).property
    choose x hxA hxq using hx
    apply h (fun p => x p.1 p.2)
    refine ⟨hxA, ?_⟩
    intro i j hij
    apply hf
    apply Subtype.ext
    exact (hxq i).symm.trans (hij.trans (hxq j))
  · intro h z hz
    let f : Fin (N + 1) → q '' {x | A.Realize (Sum.elim v x)} :=
      fun i => ⟨q (fun a => z (i, a)), (fun a => z (i, a)), hz.1 i, rfl⟩
    exact h f (fun i j hij => hz.2 (congrArg Subtype.val hij))

end DiamondIntegral.Section5
