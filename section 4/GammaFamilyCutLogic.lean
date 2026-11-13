import «section 4».GammaFamilyEuler

/-! First-order Euler level sets for a fixed finite cut bound. Occupancy
of every cut pattern is a Gamma formula over the original base, and a
finite Boolean mask records its endpoint-independent Euler weight. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFamilyCutLogic
open GammaFormulaLogic GammaOrderLogic EulerFunction

def codeFormula {ι : Type} {arity : ι → ℕ} {n : ℕ} (i j : Fin n) (v : Fin 3) :
    GammaFormulaLogic.Formula arity n :=
  if v = 0 then .lt j i else if v = 1 then .and (.not (.lt j i)) (.not (.lt i j)) else .lt i j

theorem codeFormula_realize {ι α : Type} [LinearOrder α] {arity : ι → ℕ}
    (A : (a : ι) → Set (Fin (arity a) → α)) {n : ℕ} (i j : Fin n) (v : Fin 3) (z : Fin n → α) :
    (codeFormula (arity := arity) i j v).Realize A z ↔ cutCode (z i) (z j) = v := by
  fin_cases v
  · change (codeFormula (arity := arity) i j 0).Realize A z ↔ cutCode (z i) (z j) = 0
    simp [codeFormula, GammaFormulaLogic.Formula.Realize, cutCode_zero_iff]
  · change (codeFormula (arity := arity) i j 1).Realize A z ↔ cutCode (z i) (z j) = 1
    simp only [codeFormula, show (1 : Fin 3) ≠ 0 by decide,
      ite_false, ite_true, GammaFormulaLogic.Formula.Realize, cutCode_one_iff]
    constructor
    · intro h
      exact le_antisymm (le_of_not_gt h.2) (le_of_not_gt h.1)
    · intro h
      rw [h]
      exact ⟨lt_irrefl _, lt_irrefl _⟩
  · change (codeFormula (arity := arity) i j 2).Realize A z ↔ cutCode (z i) (z j) = 2
    simp [codeFormula, GammaFormulaLogic.Formula.Realize, cutCode_two_iff]

def occupiedFormula (N n : ℕ) (σ : Fin N → Fin 3) :
    GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (N + n) :=
  let π : Fin (n + 1) → Fin (N + n + 1) := Fin.cases 0 (fun j => (Fin.natAdd N j).succ)
  let atom : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (N + n + 1) := .pred () π
  (atom.and (GammaFormulaLogic.Formula.allOf (List.ofFn
    (fun i => codeFormula (Fin.castAdd n i).succ 0 (σ i))))).ex

def Occupied {α : Type} [LinearOrder α] {N n : ℕ}
    (R : Set (Fin (n + 1) → α)) (σ : Fin N → Fin 3) (z : Fin (N + n) → α) : Prop :=
  ∃ x, Fin.cons x (fun j => z (Fin.natAdd N j)) ∈ R ∧
    ∀ i, cutCode (z (Fin.castAdd n i)) x = σ i

theorem occupiedFormula_realize {α : Type} [LinearOrder α] (N n : ℕ)
    (R : Set (Fin (n + 1) → α)) (σ : Fin N → Fin 3) (z : Fin (N + n) → α) :
    (occupiedFormula N n σ).Realize (fun _ => R) z ↔ Occupied R σ z := by
  simp only [occupiedFormula, GammaFormulaLogic.Formula.Realize,
    GammaFormulaLogic.Formula.allOf_realize, List.forall_mem_ofFn_iff, codeFormula_realize,
    Fin.cons_zero, Fin.cons_succ]
  have he (x : α) :
      (Fin.cons x z ∘ Fin.cases 0 (fun j => (Fin.natAdd N j).succ)) =
        (Fin.cons x (fun j => z (Fin.natAdd N j)) : Fin (n + 1) → α) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp_rw [he]
  rfl

def maskValue {N : ℕ} (k : EulerKind) (b : (Fin N → Fin 3) → Bool) : ℤ :=
  ∑ σ : Fin N → Fin 3, if b σ then cutPatternValue k σ else 0

def cutSum {α : Type} [LinearOrder α] {N n : ℕ} (k : EulerKind)
    (R : Set (Fin (n + 1) → α)) (z : Fin (N + n) → α) : ℤ :=
  ∑ σ : Fin N → Fin 3, if Occupied R σ z then cutPatternValue k σ else 0

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem occupied_definable_base (B : Base (M := M)) {N n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (σ : Fin N → Fin 3) : GammaDefinable B {z | Occupied R σ z} := by
  have h := GammaFormulaLogic.formula_definable_base B (fun _ : Unit => R) (fun _ => hR)
    (occupiedFormula N n σ)
  simpa only [occupiedFormula_realize] using h

theorem mask_definable_base (B : Base (M := M)) {N n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (b : (Fin N → Fin 3) → Bool) : GammaDefinable B {z | ∀ σ, Occupied R σ z ↔ b σ = true} := by
  let P (σ : Fin N → Fin 3) : Set (Fin (N + n) → Values.Gamma (M := M)) :=
    if b σ then {z | Occupied R σ z} else {z | Occupied R σ z}ᶜ
  have hP (σ : Fin N → Fin 3) : GammaDefinable B (P σ) := by
    by_cases h : b σ = true
    · simpa [P, h] using occupied_definable_base B R hR σ
    · simpa [P, h] using
        GammaRelationLogic.complement_definable_base B _ (occupied_definable_base B R hR σ)
  have h := GammaQuantifierLogic.finite_iInter_definable_base B P hP
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  apply forall_congr'
  intro σ
  by_cases hb : b σ = true <;> simp [P, hb]

theorem cutSum_level_definable_base (B : Base (M := M)) {N n : ℕ} (k : EulerKind)
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) (m : ℤ) :
    GammaDefinable B {z : Fin (N + n) → Values.Gamma (M := M) | cutSum k R z = m} := by
  let Masks := {b : (Fin N → Fin 3) → Bool // maskValue k b = m}
  have h := GammaQuantifierLogic.finite_iUnion_definable_base B
    (fun b : Masks => {z | ∀ σ, Occupied R σ z ↔ b.val σ = true})
    (fun b => mask_definable_base B R hR b.val)
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  change cutSum k R z = m ↔ ∃ b : Masks, ∀ σ, Occupied R σ z ↔ b.val σ = true
  constructor
  · intro hz
    let b : (Fin N → Fin 3) → Bool := fun σ => decide (Occupied R σ z)
    have hb : maskValue k b = m := by
      simpa only [maskValue, b, decide_eq_true_eq, cutSum] using hz
    exact ⟨⟨b, hb⟩, fun σ => by simp only [b, decide_eq_true_eq]⟩
  · rintro ⟨b, hb⟩
    calc
      cutSum k R z = maskValue k b.val := by
        unfold cutSum maskValue
        apply Finset.sum_congr rfl
        intro σ _
        simp only [← hb σ]
      _ = m := b.property

end DiamondIntegral.Section4.GammaFamilyCutLogic
