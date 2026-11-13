import «section 4».GammaQuantifierLogic

/-! A finite Gamma formula calculus with arbitrary definable relation
atoms. All Boolean operations and Gamma quantifiers preserve the original
base through full proper RV-code preimages. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFormulaLogic

inductive Formula {ι : Type} (arity : ι → ℕ) : ℕ → Type where
  | top {n : ℕ} : Formula arity n
  | lt {n : ℕ} (i j : Fin n) : Formula arity n
  | pred {n : ℕ} (a : ι) (π : Fin (arity a) → Fin n) : Formula arity n
  | and {n : ℕ} (φ ψ : Formula arity n) : Formula arity n
  | not {n : ℕ} (φ : Formula arity n) : Formula arity n
  | ex {n : ℕ} (φ : Formula arity (n + 1)) : Formula arity n

def Formula.Realize {ι α : Type} [LT α] {arity : ι → ℕ}
    (A : (a : ι) → Set (Fin (arity a) → α)) :
    {n : ℕ} → Formula arity n → (Fin n → α) → Prop
  | _, .top, _ => True
  | _, .lt i j, z => z i < z j
  | _, .pred a π, z => z ∘ π ∈ A a
  | _, .and φ ψ, z => φ.Realize A z ∧ ψ.Realize A z
  | _, .not φ, z => ¬ φ.Realize A z
  | _, .ex φ, z => ∃ x, φ.Realize A (Fin.cons x z)

def Formula.imp {ι : Type} {arity : ι → ℕ} {n : ℕ}
    (φ ψ : Formula arity n) : Formula arity n := .not (.and φ (.not ψ))

def Formula.iff {ι : Type} {arity : ι → ℕ} {n : ℕ}
    (φ ψ : Formula arity n) : Formula arity n := .and (φ.imp ψ) (ψ.imp φ)

def Formula.all {ι : Type} {arity : ι → ℕ} {n : ℕ}
    (φ : Formula arity (n + 1)) : Formula arity n := .not (.ex (.not φ))

def Formula.allOf {ι : Type} {arity : ι → ℕ} {n : ℕ}
    (l : List (Formula arity n)) : Formula arity n := l.foldr .and .top

def Formula.anyOf {ι : Type} {arity : ι → ℕ} {n : ℕ}
    (l : List (Formula arity n)) : Formula arity n := .not (Formula.allOf (l.map .not))

theorem Formula.imp_realize {ι α : Type} [LT α] {arity : ι → ℕ}
    (A : (a : ι) → Set (Fin (arity a) → α)) {n : ℕ}
    (φ ψ : Formula arity n) (z : Fin n → α) :
    (φ.imp ψ).Realize A z ↔ (φ.Realize A z → ψ.Realize A z) := by
  simp only [imp, Realize, not_and_or, not_not, imp_iff_not_or]

theorem Formula.iff_realize {ι α : Type} [LT α] {arity : ι → ℕ}
    (A : (a : ι) → Set (Fin (arity a) → α)) {n : ℕ}
    (φ ψ : Formula arity n) (z : Fin n → α) :
    (φ.iff ψ).Realize A z ↔ (φ.Realize A z ↔ ψ.Realize A z) := by
  simp only [iff, Realize, imp_realize, iff_def]

theorem Formula.all_realize {ι α : Type} [LT α] {arity : ι → ℕ}
    (A : (a : ι) → Set (Fin (arity a) → α)) {n : ℕ}
    (φ : Formula arity (n + 1)) (z : Fin n → α) :
    φ.all.Realize A z ↔ ∀ x, φ.Realize A (Fin.cons x z) := by
  simp only [all, Realize, not_exists, not_not]

theorem Formula.allOf_realize {ι α : Type} [LT α] {arity : ι → ℕ}
    (A : (a : ι) → Set (Fin (arity a) → α)) {n : ℕ}
    (l : List (Formula arity n)) (z : Fin n → α) :
    (Formula.allOf l).Realize A z ↔ ∀ φ ∈ l, φ.Realize A z := by
  induction l with
  | nil => simp only [allOf, List.foldr_nil, Realize, List.not_mem_nil, false_implies, implies_true]
  | cons φ l ih =>
    change (φ.Realize A z ∧ (Formula.allOf l).Realize A z) ↔
      ∀ ψ ∈ φ :: l, ψ.Realize A z
    simp only [ih, List.mem_cons, forall_eq_or_imp]

theorem Formula.anyOf_realize {ι α : Type} [LT α] {arity : ι → ℕ}
    (A : (a : ι) → Set (Fin (arity a) → α)) {n : ℕ}
    (l : List (Formula arity n)) (z : Fin n → α) :
    (Formula.anyOf l).Realize A z ↔ ∃ φ ∈ l, φ.Realize A z := by
  rw [anyOf, Realize, allOf_realize]
  constructor
  · intro h
    by_contra hn
    apply h
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hψ
    intro hr
    exact hn ⟨φ, hφ, hr⟩
  · rintro ⟨φ, hφ, hr⟩ hn
    exact (hn (.not φ) (List.mem_map.mpr ⟨φ, hφ, rfl⟩)) hr

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem formula_definable_base {ι : Type} {arity : ι → ℕ} (B : Base (M := M))
    (A : (a : ι) → Set (Fin (arity a) → Values.Gamma (M := M)))
    (hA : ∀ a, GammaOrderLogic.GammaDefinable B (A a)) {n : ℕ} (φ : Formula arity n) :
    GammaOrderLogic.GammaDefinable B {z | φ.Realize A z} := by
  induction φ with
  | @top n =>
    simpa only [Formula.Realize, Set.ofPred_true, GammaOrderLogic.GammaDefinable,
      Set.mem_univ, and_true] using GammaOrderLogic.proper_definable_base B n
  | lt i j =>
    exact GammaOrderLogic.formula_definable_base B (fun a : Empty => nomatch a)
      (fun a => nomatch a) (.lt i j)
  | pred a π => exact GammaRelationLogic.preimage_definable_base B (A a) (hA a) π
  | and φ ψ hφ hψ => exact GammaRelationLogic.inter_definable_base B _ _ hφ hψ
  | not φ hφ => exact GammaRelationLogic.complement_definable_base B _ hφ
  | ex φ hφ => exact GammaRelationLogic.exists_definable_base B _ hφ

end DiamondIntegral.Section4.GammaFormulaLogic
