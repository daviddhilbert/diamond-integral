import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.RingTheory.FreeCommRing
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

/-! Finite positive expressions in definable field sets. Addition is
encoded by disjoint tags 0 and 1, and multiplication by Cartesian
products. Their domains have uniform ring-language formulas over any
field, with the parameter tuple left free for specialization. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldPositiveExpressions

theorem sumElim_comp_map {P : Type*} {α : Type*} {β : Type*} {F : Type*}
    (v : P → F) (x : β → F) (f : α → β) :
    Sum.elim v x ∘ Sum.map id f = Sum.elim v (x ∘ f) := by
  funext i
  cases i <;> rfl

inductive Expr (ι : Type*) where
  | zero : Expr ι
  | one : Expr ι
  | atom : ι → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | mul : Expr ι → Expr ι → Expr ι

variable {ι : Type*}

def Expr.vars : Expr ι → Finset ι
  | .zero | .one => ∅
  | .atom i => {i}
  | .add a b | .mul a b => a.vars ∪ b.vars

def Expr.eval {R : Type*} [Semiring R] (v : ι → R) : Expr ι → R
  | .zero => 0
  | .one => 1
  | .atom i => v i
  | .add a b => a.eval v + b.eval v
  | .mul a b => a.eval v * b.eval v

def Expr.variables (arity : ι → ℕ) : Expr ι → Type
  | .zero | .one => Fin 0
  | .atom i => Fin (arity i)
  | .add a b => Option (a.variables arity ⊕ b.variables arity)
  | .mul a b => a.variables arity ⊕ b.variables arity

instance Expr.finiteVariables (arity : ι → ℕ) (e : Expr ι) : Finite (e.variables arity) := by
  induction e with
  | zero => exact inferInstanceAs (Finite (Fin 0))
  | one => exact inferInstanceAs (Finite (Fin 0))
  | atom i => exact inferInstanceAs (Finite (Fin (arity i)))
  | add a b ha hb =>
    letI : Finite (a.variables arity) := ha
    letI : Finite (b.variables arity) := hb
    letI := Fintype.ofFinite (a.variables arity)
    letI := Fintype.ofFinite (b.variables arity)
    exact inferInstanceAs (Finite (Option (a.variables arity ⊕ b.variables arity)))
  | mul a b ha hb =>
    letI : Finite (a.variables arity) := ha
    letI : Finite (b.variables arity) := hb
    letI := Fintype.ofFinite (a.variables arity)
    letI := Fintype.ofFinite (b.variables arity)
    exact inferInstanceAs (Finite (a.variables arity ⊕ b.variables arity))

def Expr.domain {F : Type*} [Field F] (arity : ι → ℕ)
    (D : ∀ i, Set (Fin (arity i) → F)) : (e : Expr ι) → Set (e.variables arity → F)
  | .zero => ∅
  | .one => Set.univ
  | .atom i => D i
  | .add a b => {x |
      (x none = 0 ∧ (fun i => x (some (.inl i))) ∈ a.domain arity D ∧ ∀ j, x (some (.inr j)) = 0) ∨
      (x none = 1 ∧ (fun j => x (some (.inr j))) ∈ b.domain arity D ∧ ∀ i, x (some (.inl i)) = 0)}
  | .mul a b => {x | x ∘ Sum.inl ∈ a.domain arity D ∧ x ∘ Sum.inr ∈ b.domain arity D}

def allZero {α β : Type*} [Finite β] (f : β → α) : Language.ring.Formula α := by
  letI := Fintype.ofFinite β
  exact Formula.iInf (fun i => (Term.var (f i)).equal 0)

theorem realize_allZero {F α β : Type*} [Field F] [FirstOrder.Ring.CompatibleRing F]
    [Finite β] (f : β → α) (x : α → F) : (allZero f).Realize x ↔ ∀ i, x (f i) = 0 := by
  simp [allZero]

def Expr.formula {P : Type*} (arity : ι → ℕ)
    (D : ∀ i, Language.ring.Formula (P ⊕ Fin (arity i))) :
    (e : Expr ι) → Language.ring.Formula (P ⊕ e.variables arity)
  | .zero => ⊥
  | .one => ⊤
  | .atom i => D i
  | .add a b =>
      (((Term.var (.inr none)).equal 0 ⊓
          (a.formula arity D).relabel (Sum.map id (fun i => some (.inl i)))) ⊓
          allZero (fun j => .inr (some (.inr j)))) ⊔
      (((Term.var (.inr none)).equal 1 ⊓
          (b.formula arity D).relabel (Sum.map id (fun j => some (.inr j)))) ⊓
          allZero (fun i => .inr (some (.inl i))))
  | .mul a b =>
      (a.formula arity D).relabel (Sum.map id Sum.inl) ⊓
        (b.formula arity D).relabel (Sum.map id Sum.inr)

theorem formula_realize {F P : Type*} [Field F] [FirstOrder.Ring.CompatibleRing F]
    (arity : ι → ℕ) (D : ∀ i, Language.ring.Formula (P ⊕ Fin (arity i)))
    (v : P → F) (e : Expr ι) (x : e.variables arity → F) :
    (e.formula arity D).Realize (Sum.elim v x) ↔
      x ∈ e.domain arity (fun i => {y | (D i).Realize (Sum.elim v y)}) := by
  induction e with
  | zero => simp [Expr.formula, Expr.domain]
  | one => simp [Expr.formula, Expr.domain]
  | atom i => rfl
  | add a b ha hb =>
    simp only [Expr.formula, Formula.realize_sup, Formula.realize_inf, Formula.realize_equal,
      Term.realize_var, FirstOrder.Ring.realize_zero, FirstOrder.Ring.realize_one,
      Formula.realize_relabel, realize_allZero]
    have hA : Sum.elim v x ∘ Sum.map id (fun i => some (.inl i)) =
        Sum.elim v (fun i => x (some (.inl i))) := sumElim_comp_map v x _
    have hB : Sum.elim v x ∘ Sum.map id (fun j => some (.inr j)) =
        Sum.elim v (fun j => x (some (.inr j))) := sumElim_comp_map v x _
    rw [hA, hB]
    change (((x none = 0 ∧ (a.formula arity D).Realize (Sum.elim v (fun i => x (some (.inl i))))) ∧
        (∀ j, x (some (.inr j)) = 0)) ∨
        ((x none = 1 ∧ (b.formula arity D).Realize (Sum.elim v (fun j => x (some (.inr j))))) ∧
        (∀ i, x (some (.inl i)) = 0))) ↔ _
    rw [ha, hb]
    simp only [Expr.domain, Set.mem_setOf_eq]
    tauto
  | mul a b ha hb =>
    simp only [Expr.formula, Formula.realize_inf, Formula.realize_relabel]
    have hA : Sum.elim v x ∘ Sum.map id Sum.inl = Sum.elim v (x ∘ Sum.inl) := sumElim_comp_map v x _
    have hB : Sum.elim v x ∘ Sum.map id Sum.inr = Sum.elim v (x ∘ Sum.inr) := sumElim_comp_map v x _
    rw [hA, hB]
    change ((a.formula arity D).Realize (Sum.elim v (x ∘ Sum.inl)) ∧
      (b.formula arity D).Realize (Sum.elim v (x ∘ Sum.inr))) ↔ _
    rw [ha, hb]
    rfl

theorem freeRing_difference (r : FreeCommRing ι) :
    ∃ a b : Expr ι, a.eval FreeCommRing.of - b.eval FreeCommRing.of = r := by
  induction r using FreeCommRing.induction_on with
  | neg_one => exact ⟨.zero, .one, by simp [Expr.eval]⟩
  | of i => exact ⟨.atom i, .zero, by simp [Expr.eval]⟩
  | add x y hx hy =>
    obtain ⟨a, b, ha⟩ := hx
    obtain ⟨c, d, hc⟩ := hy
    refine ⟨.add a c, .add b d, ?_⟩
    simp only [Expr.eval]
    rw [← ha, ← hc]
    ring
  | mul x y hx hy =>
    obtain ⟨a, b, ha⟩ := hx
    obtain ⟨c, d, hc⟩ := hy
    refine ⟨.add (.mul a c) (.mul b d), .add (.mul a d) (.mul b c), ?_⟩
    simp only [Expr.eval]
    rw [← ha, ← hc]
    ring

end DiamondIntegral.Section4.FieldPositiveExpressions
