import «section 5».CylindricalFibreSyntax
import Mathlib.Basic.Finite.Sum

/-! A finite formula certifies that a domain is a full preimage of a set
in a quotient sort. Decoding uses images and requires no section. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

def tupleProperFormula {P α : Type*} [Finite α] (U : L.Formula (Fin 1))
    (f : α → P) : L.Formula P := Formula.iInf (fun i => U.relabel (fun _ => f i))

theorem tupleProperFormula_realize {P α M : Type*} [Finite α] [L.Structure M]
    (U : L.Formula (Fin 1)) (f : α → P) (v : P → M) :
    (tupleProperFormula U f).Realize v ↔ ∀ i, U.Realize (fun _ => v (f i)) := by
  simp [tupleProperFormula, Function.comp_def]

def tupleQuotientEqualityFormula {P α : Type*} [Finite α] (E : L.Formula (Fin 2))
    (f g : α → P) : L.Formula P := Formula.iInf (fun i => binaryRelabel E (f i) (g i))

theorem tupleQuotientEqualityFormula_realize {P α M : Type*} [Finite α] [L.Structure M]
    (E : L.Formula (Fin 2)) (f g : α → P) (v : P → M) :
    (tupleQuotientEqualityFormula E f g).Realize v ↔ ∀ i, E.Realize ![v (f i), v (g i)] := by
  simp [tupleQuotientEqualityFormula, binaryRelabel_realize]

def quotientDomainValidityFormula {P α : Type*} [Finite α]
    (U : L.Formula (Fin 1)) (E : L.Formula (Fin 2)) (D : L.Formula (P ⊕ α)) : L.Formula P :=
  (D.imp (tupleProperFormula U Sum.inr)).iAlls α ⊓
    ((tupleProperFormula U (fun a => Sum.inr (Sum.inl a)) ⊓
      tupleProperFormula U (fun a => Sum.inr (Sum.inr a)) ⊓
      tupleQuotientEqualityFormula E (fun a => Sum.inr (Sum.inl a)) (fun a => Sum.inr (Sum.inr a))).imp
        (relationalIff (D.relabel (Sum.map id Sum.inl)) (D.relabel (Sum.map id Sum.inr)))).iAlls (α ⊕ α)

theorem quotientDomainValidityFormula_realize {P α M : Type*} [Finite α] [L.Structure M]
    (U : L.Formula (Fin 1)) (E : L.Formula (Fin 2)) (D : L.Formula (P ⊕ α)) (v : P → M) :
    (quotientDomainValidityFormula U E D).Realize v ↔
      (∀ x, D.Realize (Sum.elim v x) → ∀ i, U.Realize (fun _ => x i)) ∧
      ∀ x y, (∀ i, U.Realize (fun _ => x i)) → (∀ i, U.Realize (fun _ => y i)) →
        (∀ i, E.Realize ![x i, y i]) →
          (D.Realize (Sum.elim v x) ↔ D.Realize (Sum.elim v y)) := by
  simp only [quotientDomainValidityFormula, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, tupleProperFormula_realize, tupleQuotientEqualityFormula_realize,
    relationalIff_realize, Formula.realize_relabel]
  have hx (z : α ⊕ α → M) : Sum.elim v z ∘ Sum.map id Sum.inl = Sum.elim v (z ∘ Sum.inl) := by
    funext t
    cases t <;> rfl
  have hy (z : α ⊕ α → M) : Sum.elim v z ∘ Sum.map id Sum.inr = Sum.elim v (z ∘ Sum.inr) := by
    funext t
    cases t <;> rfl
  simp only [hx, hy, Sum.elim_inr]
  apply and_congr_right
  intro _
  constructor
  · intro h x y hx hy he
    exact h (Sum.elim x y) ⟨⟨hx, hy⟩, he⟩
  · intro h z hz
    exact h (z ∘ Sum.inl) (z ∘ Sum.inr) hz.1.1 hz.1.2 hz.2

def quotientFormulaDomain {P α M Q : Type*} [L.Structure M]
    (D : L.Formula (P ⊕ α)) (v : P → M) (q : M → Q) : Set (α → Q) :=
  (fun x => q ∘ x) '' {x : α → M | D.Realize (Sum.elim v x)}

theorem quotientFormulaDomain_full_preimage {P α M Q : Type*} [Finite α] [L.Structure M]
    (U : L.Formula (Fin 1)) (E : L.Formula (Fin 2)) (D : L.Formula (P ⊕ α))
    (v : P → M) (proper : M → Prop) (q : M → Q)
    (hU : ∀ t, U.Realize t ↔ proper (t 0))
    (hE : ∀ x y, proper x → proper y → (E.Realize ![x, y] ↔ q x = q y))
    (hD : (quotientDomainValidityFormula U E D).Realize v) (x : α → M) :
    D.Realize (Sum.elim v x) ↔ (∀ i, proper (x i)) ∧ q ∘ x ∈ quotientFormulaDomain D v q := by
  obtain ⟨hsorted, hinv⟩ := (quotientDomainValidityFormula_realize U E D v).mp hD
  constructor
  · intro hx
    exact ⟨fun i => (hU _).mp (hsorted x hx i), x, hx, rfl⟩
  · rintro ⟨hx, y, hy, hq⟩
    apply (hinv y x (hsorted y hy) (fun i => (hU _).mpr (hx i)) ?_).mp hy
    intro i
    exact (hE (y i) (x i) ((hU _).mp (hsorted y hy i)) (hx i)).mpr (congrFun hq i)

end DiamondIntegral.Section5
