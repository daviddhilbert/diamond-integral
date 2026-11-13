import «section 4».GammaFormulaLogic

/-! First-order descriptions of constant left/right germs and far-left
tails of Gamma fibres. Endpoints are quantified over actual Gamma, and
every formula retains the original parameter base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaGermLogic
open GammaOrderLogic GammaFormulaLogic

def germFormula (right : Bool) (n : ℕ) :
    GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 1) :=
  let π : Fin (n + 1) → Fin (n + 3) := Fin.cases 0 (fun j => j.succ.succ.succ)
  let lt (i j : Fin (n + 3)) : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 3) := .lt i j
  let atom : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 3) := .pred () π
  let near := if right then
      ((lt (0 : Fin (n + 1)).succ.succ 0).and (lt 0 (0 : Fin (n + 2)).succ)).imp atom
    else ((lt (0 : Fin (n + 2)).succ 0).and (lt 0 (0 : Fin (n + 1)).succ.succ)).imp atom
  let bound : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 2) :=
    if right then .lt (0 : Fin (n + 1)).succ 0 else .lt 0 (0 : Fin (n + 1)).succ
  (bound.and near.all).ex

def tailFormula (n : ℕ) : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) n :=
  let π : Fin (n + 1) → Fin (n + 2) := Fin.cases 0 (fun j => j.succ.succ)
  let atom : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 2) := .pred () π
  let lt : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 2) :=
    .lt 0 (0 : Fin (n + 1)).succ
  (lt.imp atom).all.ex

def LeftGerm {α : Type} [LT α] {n : ℕ} (R : Set (Fin (n + 1) → α)) :
    Set (Fin (n + 1) → α) :=
  {z | ∃ l, l < z 0 ∧ ∀ x, l < x → x < z 0 → Fin.cons x (fun j => z j.succ) ∈ R}

def RightGerm {α : Type} [LT α] {n : ℕ} (R : Set (Fin (n + 1) → α)) :
    Set (Fin (n + 1) → α) :=
  {z | ∃ u, z 0 < u ∧ ∀ x, z 0 < x → x < u → Fin.cons x (fun j => z j.succ) ∈ R}

def Tail {α : Type} [LT α] {n : ℕ} (R : Set (Fin (n + 1) → α)) : Set (Fin n → α) :=
  {y | ∃ l, ∀ x, x < l → Fin.cons x y ∈ R}

theorem germFormula_realize {α : Type} [LT α] (right : Bool) (n : ℕ)
    (R : Set (Fin (n + 1) → α)) (z : Fin (n + 1) → α) :
    (germFormula right n).Realize (fun _ => R) z ↔ z ∈ if right then RightGerm R else LeftGerm R := by
  have he (l x : α) : (Fin.cons x (Fin.cons l z) ∘ Fin.cases 0 (fun j => j.succ.succ.succ)) =
      (Fin.cons x (fun j => z j.succ) : Fin (n + 1) → α) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  cases right <;>
    simp only [germFormula, Bool.false_eq_true, ite_false, ite_true,
      GammaFormulaLogic.Formula.Realize, GammaFormulaLogic.Formula.all_realize,
      GammaFormulaLogic.Formula.imp_realize, Fin.cons_zero, Fin.cons_succ] <;>
    simp_rw [he] <;>
    simp only [RightGerm, LeftGerm, Set.mem_ofPred_eq, and_imp]

theorem tailFormula_realize {α : Type} [LT α] (n : ℕ)
    (R : Set (Fin (n + 1) → α)) (y : Fin n → α) :
    (tailFormula n).Realize (fun _ => R) y ↔ y ∈ Tail R := by
  simp only [tailFormula, GammaFormulaLogic.Formula.Realize,
    GammaFormulaLogic.Formula.all_realize, GammaFormulaLogic.Formula.imp_realize,
    Fin.cons_zero, Fin.cons_succ]
  have he (l x : α) : (Fin.cons x (Fin.cons l y) ∘ Fin.cases 0 (fun j => j.succ.succ)) =
      (Fin.cons x y : Fin (n + 1) → α) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp_rw [he]
  rfl

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem leftGerm_definable (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    GammaDefinable B (LeftGerm R) := by
  have h := GammaFormulaLogic.formula_definable_base B (fun _ : Unit => R) (fun _ => hR)
    (germFormula false n)
  convert h using 1
  ext z
  exact (germFormula_realize false n R z).symm

theorem rightGerm_definable (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    GammaDefinable B (RightGerm R) := by
  have h := GammaFormulaLogic.formula_definable_base B (fun _ : Unit => R) (fun _ => hR)
    (germFormula true n)
  convert h using 1
  ext z
  exact (germFormula_realize true n R z).symm

theorem tail_definable (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    GammaDefinable B (Tail R) := by
  have h := GammaFormulaLogic.formula_definable_base B (fun _ : Unit => R) (fun _ => hR)
    (tailFormula n)
  convert h using 1
  ext y
  exact (tailFormula_realize n R y).symm

end DiamondIntegral.Section4.GammaGermLogic
