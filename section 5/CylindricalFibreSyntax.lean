import «section 5».FiniteWitnessFormulas
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

/-! Fixed relational formulas certify the five possible cylindrical fibre
shapes. Endpoint variables are existentially quantified inside the formula. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language

inductive CylinderFibreKind where
  | graph | band | upperRay | lowerRay | line
  deriving DecidableEq

abbrev CylinderFibreKind.endpoints : CylinderFibreKind → ℕ
  | .band => 2
  | .line => 0
  | _ => 1

def CylinderFibreKind.condition {Γ : Type*} [LT Γ] (k : CylinderFibreKind)
    (a : Fin k.endpoints → Γ) (t : Γ) : Prop :=
  match k with
  | .graph => t = a 0
  | .band => a 0 < t ∧ t < a 1
  | .upperRay => a 0 < t
  | .lowerRay => t < a 0
  | .line => True

def CylinderFibreKind.ordered {Γ : Type*} [LT Γ] (k : CylinderFibreKind)
    (a : Fin k.endpoints → Γ) : Prop :=
  match k with
  | .band => a 0 < a 1
  | _ => True

def CylinderFibreKind.Describes {Γ : Type*} [LT Γ] (k : CylinderFibreKind)
    (R : Γ → Prop) : Prop :=
  ∃ a : Fin k.endpoints → Γ, k.ordered a ∧ ∀ t, R t ↔ k.condition a t

variable {L : Language}

def relationalIff {P : Type*} (A B : L.Formula P) : L.Formula P := A.imp B ⊓ B.imp A

theorem relationalIff_realize {P M : Type*} [L.Structure M] (A B : L.Formula P) (v : P → M) :
    (relationalIff A B).Realize v ↔ (A.Realize v ↔ B.Realize v) := by
  simp [relationalIff, iff_def]

def binaryRelabel {P : Type*} (R : L.Formula (Fin 2)) (a b : P) : L.Formula P :=
  R.relabel ![a, b]

theorem binaryRelabel_realize {P M : Type*} [L.Structure M]
    (R : L.Formula (Fin 2)) (a b : P) (v : P → M) :
    (binaryRelabel R a b).Realize v ↔ R.Realize ![v a, v b] := by
  simp only [binaryRelabel, Formula.realize_relabel]
  have he : v ∘ ![a, b] = ![v a, v b] := by
    funext i
    fin_cases i <;> rfl
  rw [he]

def CylinderFibreKind.conditionFormula {P : Type*} (k : CylinderFibreKind)
    (E T : L.Formula (Fin 2)) : L.Formula (P ⊕ (Fin k.endpoints ⊕ Fin 1)) :=
  match k with
  | .graph => binaryRelabel E (.inr (.inr 0)) (.inr (.inl 0))
  | .band => binaryRelabel T (.inr (.inl 0)) (.inr (.inr 0)) ⊓
      binaryRelabel T (.inr (.inr 0)) (.inr (.inl 1))
  | .upperRay => binaryRelabel T (.inr (.inl 0)) (.inr (.inr 0))
  | .lowerRay => binaryRelabel T (.inr (.inr 0)) (.inr (.inl 0))
  | .line => ⊤

def CylinderFibreKind.orderFormula {P : Type*} (k : CylinderFibreKind)
    (T : L.Formula (Fin 2)) : L.Formula (P ⊕ Fin k.endpoints) :=
  match k with
  | .band => binaryRelabel T (.inr 0) (.inr 1)
  | _ => ⊤

def cylindricalFibreValidityFormula {P : Type*} (k : CylinderFibreKind)
    (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ Fin 1)) : L.Formula P :=
  let body : L.Formula (P ⊕ (Fin k.endpoints ⊕ Fin 1)) :=
    (U.relabel (fun _ => Sum.inr (Sum.inr (0 : Fin 1)))).imp
      (relationalIff (D.relabel (Sum.map id Sum.inr)) (k.conditionFormula E T))
  let all := (body.relabel (Equiv.sumAssoc P (Fin k.endpoints) (Fin 1)).symm).iAlls (Fin 1)
  ((Formula.iInf (fun i : Fin k.endpoints => U.relabel (fun _ => Sum.inr i))) ⊓
    k.orderFormula T ⊓ all).iExs (Fin k.endpoints)

theorem cylindricalFibreValidityFormula_realize {P M : Type*} [L.Structure M]
    (k : CylinderFibreKind) (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ Fin 1)) (v : P → M) :
    (cylindricalFibreValidityFormula k U E T D).Realize v ↔
      ∃ a : Fin k.endpoints → M,
        (∀ i, U.Realize (fun _ => a i)) ∧
        (k.orderFormula T).Realize (Sum.elim v a) ∧
        ∀ t : Fin 1 → M, U.Realize t →
          (D.Realize (Sum.elim v t) ↔
            (k.conditionFormula E T).Realize (Sum.elim v (Sum.elim a t))) := by
  simp only [cylindricalFibreValidityFormula, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel, Formula.realize_iAlls,
    Formula.realize_imp, relationalIff_realize]
  have ha (a : Fin k.endpoints → M) (t : Fin 1 → M) :
      Sum.elim (Sum.elim v a) t ∘ (Equiv.sumAssoc P (Fin k.endpoints) (Fin 1)).symm =
        Sum.elim v (Sum.elim a t) := by
    funext i
    cases i with
    | inl p => rfl
    | inr i => cases i <;> rfl
  have hd (a : Fin k.endpoints → M) (t : Fin 1 → M) :
      Sum.elim v (Sum.elim a t) ∘ Sum.map id Sum.inr = Sum.elim v t := by
    funext i
    cases i <;> rfl
  simp only [ha, hd]
  simp only [Function.comp_def, Sum.elim_inr, Sum.elim_inl]
  have ht (t : Fin 1 → M) : (fun _ : Fin 1 => t 0) = t := by
    funext i; fin_cases i; rfl
  simp only [ht, and_assoc]

theorem CylinderFibreKind.conditionFormula_realize {P M Γ : Type*}
    [L.Structure M] [LT Γ] (k : CylinderFibreKind) (E T : L.Formula (Fin 2))
    (proper : M → Prop) (q : M → Γ)
    (hE : ∀ x y, proper x → proper y → (E.Realize ![x, y] ↔ q x = q y))
    (hT : ∀ x y, proper x → proper y → (T.Realize ![x, y] ↔ q x < q y))
    (v : P → M) (a : Fin k.endpoints → M) (t : Fin 1 → M)
    (ha : ∀ i, proper (a i)) (ht : proper (t 0)) :
    (k.conditionFormula E T).Realize (Sum.elim v (Sum.elim a t)) ↔
      k.condition (q ∘ a) (q (t 0)) := by
  cases k with
  | graph => simpa [conditionFormula, condition, binaryRelabel_realize] using hE (t 0) (a 0) ht (ha 0)
  | band =>
    simpa [conditionFormula, condition, binaryRelabel_realize] using
      and_congr (hT (a 0) (t 0) (ha 0) ht) (hT (t 0) (a 1) ht (ha 1))
  | upperRay => simpa [conditionFormula, condition, binaryRelabel_realize] using hT (a 0) (t 0) (ha 0) ht
  | lowerRay => simpa [conditionFormula, condition, binaryRelabel_realize] using hT (t 0) (a 0) ht (ha 0)
  | line => simp [conditionFormula, condition]

theorem CylinderFibreKind.orderFormula_realize {P M Γ : Type*}
    [L.Structure M] [LT Γ] (k : CylinderFibreKind) (T : L.Formula (Fin 2))
    (proper : M → Prop) (q : M → Γ)
    (hT : ∀ x y, proper x → proper y → (T.Realize ![x, y] ↔ q x < q y))
    (v : P → M) (a : Fin k.endpoints → M) (ha : ∀ i, proper (a i)) :
    (k.orderFormula T).Realize (Sum.elim v a) ↔ k.ordered (q ∘ a) := by
  cases k with
  | band => simpa [orderFormula, ordered, binaryRelabel_realize] using hT (a 0) (a 1) (ha 0) (ha 1)
  | graph => simp [orderFormula, ordered]
  | upperRay => simp [orderFormula, ordered]
  | lowerRay => simp [orderFormula, ordered]
  | line => simp [orderFormula, ordered]

theorem cylindricalFibreValidityFormula_quotient {P M Γ : Type*}
    [L.Structure M] [LT Γ] (k : CylinderFibreKind)
    (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ Fin 1)) (v : P → M)
    (proper : M → Prop) (q : M → Γ) (R : Γ → Prop)
    (hU : ∀ t, U.Realize t ↔ proper (t 0))
    (hE : ∀ x y, proper x → proper y → (E.Realize ![x, y] ↔ q x = q y))
    (hT : ∀ x y, proper x → proper y → (T.Realize ![x, y] ↔ q x < q y))
    (hq : ∀ γ, ∃ t, proper t ∧ q t = γ)
    (hD : ∀ t, proper (t 0) → (D.Realize (Sum.elim v t) ↔ R (q (t 0)))) :
    (cylindricalFibreValidityFormula k U E T D).Realize v ↔ k.Describes R := by
  rw [cylindricalFibreValidityFormula_realize]
  constructor
  · rintro ⟨a, ha, ho, h⟩
    have hpa : ∀ i, proper (a i) := fun i => (hU _).mp (ha i)
    refine ⟨q ∘ a, (k.orderFormula_realize T proper q hT v a hpa).mp ho, ?_⟩
    intro γ
    obtain ⟨t, ht, hqt⟩ := hq γ
    have he := h (fun _ => t) ((hU _).mpr ht)
    rw [hD _ ht, k.conditionFormula_realize E T proper q hE hT v a _ hpa ht] at he
    simpa only [hqt] using he
  · rintro ⟨b, ho, h⟩
    choose a ha hqa using (fun i => hq (b i))
    have he : q ∘ a = b := funext hqa
    refine ⟨a, (fun i => (hU _).mpr (ha i)), ?_, ?_⟩
    · apply (k.orderFormula_realize T proper q hT v a ha).mpr
      simpa only [he] using ho
    · intro t ht
      have hpt := (hU _).mp ht
      rw [hD _ hpt, k.conditionFormula_realize E T proper q hE hT v a t ha hpt, he]
      exact h _

end DiamondIntegral.Section5
