import «section 5».FiniteWitnessFormulas
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.EquivFin

/-! Fixed finite fibre bounds are first-order conditions on an actual
relation graph. The formula forbids a tuple of N+1 distinct source points
in one fibre, uniformly with all parameters left free. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

def tupleEqualityFormula {P α : Type*} [Finite α] (f g : α → P) : L.Formula P :=
  Formula.iInf (fun i => (Term.var (f i)).equal (Term.var (g i)))

theorem tupleEqualityFormula_realize {P α M : Type*} [Finite α] [L.Structure M]
    (f g : α → P) (v : P → M) :
    (tupleEqualityFormula (L := L) f g).Realize v ↔ v ∘ f = v ∘ g := by
  simp [tupleEqualityFormula, funext_iff]

def tupleDistinctFormula {P α ι : Type*} [Finite α] [Finite ι] (f : ι → α → P) : L.Formula P :=
  Formula.iInf (fun i => Formula.iInf (fun j =>
    if i = j then ⊤ else (tupleEqualityFormula (f i) (f j)).not))

theorem tupleDistinctFormula_realize {P α ι M : Type*} [Finite α] [Finite ι] [L.Structure M]
    (f : ι → α → P) (v : P → M) :
    (tupleDistinctFormula (L := L) f).Realize v ↔ Function.Injective (fun i => v ∘ f i) := by
  simp only [tupleDistinctFormula, Formula.realize_iInf]
  constructor
  · intro h i j hij
    by_contra hne
    have hh := h i j
    rw [if_neg hne, Formula.realize_not, tupleEqualityFormula_realize] at hh
    exact hh hij
  · intro h i j
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, Formula.realize_not, tupleEqualityFormula_realize]
      exact fun he => hij (h he)

def fibreCollisionFormula {P α β : Type*} [Finite α] (N : ℕ)
    (A : L.Formula (P ⊕ α)) (R : L.Formula (P ⊕ (α ⊕ β))) :
    L.Formula (P ⊕ (β ⊕ (Fin (N + 1) × α))) :=
  Formula.iInf (fun i : Fin (N + 1) =>
    A.relabel (Sum.map id (fun a => Sum.inr (i, a))) ⊓
      R.relabel (Sum.map id (Sum.elim (fun a => Sum.inr (i, a)) Sum.inl))) ⊓
    tupleDistinctFormula (fun (i : Fin (N + 1)) a => Sum.inr (Sum.inr (i, a)))

theorem fibreCollisionFormula_realize {P α β M : Type*} [Finite α] [L.Structure M]
    (N : ℕ) (A : L.Formula (P ⊕ α)) (R : L.Formula (P ⊕ (α ⊕ β)))
    (v : P → M) (z : β ⊕ (Fin (N + 1) × α) → M) :
    (fibreCollisionFormula N A R).Realize (Sum.elim v z) ↔
      (∀ i : Fin (N + 1), A.Realize (Sum.elim v (fun a => z (.inr (i, a)))) ∧
        R.Realize (Sum.elim v (Sum.elim (fun a => z (.inr (i, a))) (z ∘ Sum.inl)))) ∧
      Function.Injective (fun i : Fin (N + 1) => fun a => z (.inr (i, a))) := by
  simp only [fibreCollisionFormula, Formula.realize_inf, Formula.realize_iInf,
    Formula.realize_relabel, tupleDistinctFormula_realize]
  have hA (i : Fin (N + 1)) : Sum.elim v z ∘ Sum.map id (fun a => Sum.inr (i, a)) =
      Sum.elim v (fun a => z (.inr (i, a))) := by
    funext t
    cases t <;> rfl
  have hR (i : Fin (N + 1)) :
      Sum.elim v z ∘ Sum.map id (Sum.elim (fun a => Sum.inr (i, a)) Sum.inl) =
        Sum.elim v (Sum.elim (fun a => z (.inr (i, a))) (z ∘ Sum.inl)) := by
    funext t
    cases t with
    | inl p => rfl
    | inr t => cases t <;> rfl
  simp only [hA, hR]
  rfl

def finiteFibreValidityFormula {P α β : Type*} [Finite α] [Finite β] (N : ℕ)
    (A : L.Formula (P ⊕ α)) (R : L.Formula (P ⊕ (α ⊕ β))) : L.Formula P :=
  (fibreCollisionFormula N A R).not.iAlls (β ⊕ (Fin (N + 1) × α))

theorem finiteFibreValidityFormula_realize {P α β M : Type*}
    [Finite α] [Finite β] [L.Structure M]
    (N : ℕ) (A : L.Formula (P ⊕ α)) (R : L.Formula (P ⊕ (α ⊕ β))) (v : P → M) :
    (finiteFibreValidityFormula N A R).Realize v ↔
      ∀ (y : β → M) (x : Fin (N + 1) → α → M),
        (∀ i, A.Realize (Sum.elim v (x i)) ∧ R.Realize (Sum.elim v (Sum.elim (x i) y))) →
          ¬Function.Injective x := by
  simp only [finiteFibreValidityFormula, Formula.realize_iAlls, Formula.realize_not,
    fibreCollisionFormula_realize]
  constructor
  · intro h y x hx hinj
    exact h (Sum.elim y (fun p => x p.1 p.2)) ⟨hx, hinj⟩
  · intro h z hz
    exact h (z ∘ Sum.inl) (fun i a => z (.inr (i, a))) hz.1 hz.2

theorem no_injective_fin_iff_card_bound {X : Type*} (S : Set X) (N : ℕ) :
    (∀ f : Fin (N + 1) → S, ¬Function.Injective f) ↔ S.Finite ∧ S.ncard ≤ N := by
  constructor
  · intro h
    have hS : S.Finite := by
      by_contra hn
      let e := Set.Infinite.natEmbedding S hn
      exact h (fun i => e i.val) (e.injective.comp Fin.val_injective)
    letI := hS.fintype
    have hcard : Fintype.card S ≤ N := by
      by_contra hn
      have hle : Fintype.card (Fin (N + 1)) ≤ Fintype.card S := by
        simpa only [Fintype.card_fin] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
      exact h e e.injective
    exact ⟨hS, by simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using hcard⟩
  · rintro ⟨hS, hcard⟩ f hf
    letI := hS.fintype
    have hle := Fintype.card_le_of_injective f hf
    rw [Fintype.card_fin] at hle
    have hcard' : Fintype.card S ≤ N := by
      simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using hcard
    exact Nat.not_succ_le_self N (hle.trans hcard')

theorem finiteFibreValidityFormula_card {P α β M : Type*}
    [Finite α] [Finite β] [L.Structure M]
    (N : ℕ) (A : L.Formula (P ⊕ α)) (R : L.Formula (P ⊕ (α ⊕ β))) (v : P → M) :
    (finiteFibreValidityFormula N A R).Realize v ↔ ∀ y : β → M,
      let S := {x : α → M | A.Realize (Sum.elim v x) ∧ R.Realize (Sum.elim v (Sum.elim x y))}
      S.Finite ∧ S.ncard ≤ N := by
  rw [finiteFibreValidityFormula_realize]
  constructor
  · intro h y
    apply (no_injective_fin_iff_card_bound _ N).mp
    intro f hf
    have hinj : Function.Injective (fun i => (f i).val) := by
      intro i j he
      exact hf (Subtype.ext he)
    exact h y (fun i => (f i).val) (fun i => (f i).property) hinj
  · intro h y x hx hxi
    have hno := (no_injective_fin_iff_card_bound _ N).mpr (h y)
    let f := fun i => (⟨x i, hx i⟩ : {x : α → M |
      A.Realize (Sum.elim v x) ∧ R.Realize (Sum.elim v (Sum.elim x y))})
    exact hno f (fun _ _ he => hxi (congrArg Subtype.val he))

end DiamondIntegral.Section5
