import «section 4».GaloisPointCounts
import «section 4».BiUniqueFormula
import Mathlib.Combinatorics.Pigeonhole

/-! Uniform finite bounds on coordinate fibres are first-order conditions.
They give the corresponding polynomial bound on finite-field points. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldBoundedProjection
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def Bounded {K α β : Type*} (D : Set (α → K)) (select : β → α) (C : ℕ) : Prop :=
  ∀ x : Fin (C + 1) → (α → K), (∀ i, x i ∈ D) →
    (∀ i, x i ∘ select = x 0 ∘ select) →
    ∃ i j, i ≠ j ∧ x i = x j

theorem of_fibre_ncard_le {K α β : Type*} {D : Set (α → K)} {select : β → α} {C : ℕ}
    (hfinite : ∀ y, {x ∈ D | x ∘ select = y}.Finite)
    (hcard : ∀ y, {x ∈ D | x ∘ select = y}.ncard ≤ C) : Bounded D select C := by
  intro x hx he
  by_contra h
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩
  let f : Fin (C + 1) → {z ∈ D | z ∘ select = x 0 ∘ select} :=
    fun i => ⟨x i, hx i, he i⟩
  letI : Finite {z ∈ D | z ∘ select = x 0 ∘ select} := hfinite _
  have hle := Nat.card_le_card_of_injective f (fun i j hij => hinj (congrArg Subtype.val hij))
  have hn : C + 1 ≤ C := by simpa only [Nat.card_fin] using hle.trans (hcard (x 0 ∘ select))
  omega

def formula {P α β : Type*} [Finite α] [Finite β]
    (A : Language.ring.Formula (P ⊕ α)) (select : β → α) (C : ℕ) :
    Language.ring.Formula P :=
  (((Formula.iInf fun i : Fin (C + 1) => A.relabel (Sum.map id (fun a => (i, a)))) ⊓
    Formula.iInf (fun i : Fin (C + 1) => Formula.iInf (fun b : β =>
      (Term.var (Sum.inr (i, select b))).equal (Term.var (Sum.inr (0, select b)))))).imp
    (Formula.iSup fun i : Fin (C + 1) => Formula.iSup fun j : Fin (C + 1) =>
      if i ≠ j then Formula.iInf (fun a : α =>
        (Term.var (Sum.inr (i, a))).equal (Term.var (Sum.inr (j, a)))) else ⊥)).iAlls
          (Fin (C + 1) × α)

theorem formula_realize {P α β K : Type*} [Field K] [FirstOrder.Ring.CompatibleRing K]
    [Finite α] [Finite β] (A : Language.ring.Formula (P ⊕ α)) (select : β → α)
    (C : ℕ) (v : P → K) :
    (formula A select C).Realize v ↔ Bounded {x | A.Realize (Sum.elim v x)} select C := by
  simp only [formula, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel, Formula.realize_iSup]
  have hrelabel (x : Fin (C + 1) × α → K) (i : Fin (C + 1)) :
      Sum.elim v x ∘ Sum.map id (fun a => (i, a)) = Sum.elim v (fun a => x (i, a)) := by
    funext s
    cases s <;> rfl
  simp only [hrelabel, Formula.realize_equal, Term.realize_var]
  constructor
  · intro h x hx he
    have h' := h (fun p => x p.1 p.2) ⟨hx, fun i b => congrFun (he i) b⟩
    obtain ⟨i, j, hij⟩ := h'
    split_ifs at hij with hne
    · exact ⟨i, j, hne, funext (by simpa only [Formula.realize_iInf,
        Formula.realize_equal, Term.realize_var, Sum.elim_inr] using hij)⟩
    · exact False.elim hij
  · intro h x hx
    obtain ⟨i, j, hne, hij⟩ := h (fun i a => x (i, a)) hx.1
      (fun i => funext (hx.2 i))
    exact ⟨i, j, by simpa only [if_pos hne, Formula.realize_iInf,
      Formula.realize_equal, Term.realize_var, Sum.elim_inr] using congrFun hij⟩

theorem count_le {E K α β : Type*} [Field E] [Field K] [Algebra E K]
    [Finite E] [Finite α] [Finite β] {D : Set (α → K)} {select : β → α} {C : ℕ}
    (h : Bounded D select C) :
    GaloisPointCounts.count (E := E) D ≤ C * Nat.card E ^ Nat.card β := by
  let T := DefinableGaloisPoints.rationalPoints (E := E) D
  letI : Finite T := DefinableGaloisPoints.rationalPoints_finite D
  letI : Fintype T := Fintype.ofFinite T
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype β := Fintype.ofFinite β
  let f : T → (β → E) := fun x b => Classical.choose (x.property.2 (select b))
  have hf (x : T) (b : β) : algebraMap E K (f x b) = x.val (select b) :=
    Classical.choose_spec (x.property.2 (select b))
  have hbound (y : β → E) : Fintype.card {x : T // f x = y} ≤ C := by
    by_contra hn
    have hle : Fintype.card (Fin (C + 1)) ≤ Fintype.card {x : T // f x = y} := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
    have hm (i : Fin (C + 1)) : (e i).val.val ∈ D := (e i).val.property.1
    have he (i : Fin (C + 1)) : (e i).val.val ∘ select = (e 0).val.val ∘ select := by
      funext b
      change (e i).val.val (select b) = (e 0).val.val (select b)
      rw [← hf, ← hf, (e i).property, (e 0).property]
    obtain ⟨i, j, hne, hij⟩ := h (fun i => (e i).val.val) hm he
    exact hne (e.injective (Subtype.ext (Subtype.ext hij)))
  have htotal : Fintype.card T ≤ Fintype.card (β → E) * C := by
    by_contra hn
    obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (lt_of_not_ge hn)
    exact (not_lt_of_ge (hbound y)) (by simpa only [Fintype.card_subtype] using hy)
  change Nat.card T ≤ _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.mul_comm] using htotal

end DiamondIntegral.Section4.FieldBoundedProjection
