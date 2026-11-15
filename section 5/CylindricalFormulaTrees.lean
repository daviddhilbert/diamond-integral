import «section 5».QuotientDomainSyntax
import «section 5».CylindricalFibreCertificates

/-! Complete finite first-order validity formulas for cylindrical cell
certificates. Every recursive domain is checked as a full quotient preimage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

def curryFirstCoordinateFormula {P : Type*} {n : ℕ}
    (D : L.Formula (P ⊕ Fin (n + 1))) : L.Formula ((P ⊕ Fin n) ⊕ Fin 1) :=
  D.relabel (Sum.elim (fun p => Sum.inl (Sum.inl p))
    (Fin.cases (Sum.inr 0) (fun i => Sum.inl (Sum.inr i))))

theorem curryFirstCoordinateFormula_realize {P M : Type*} [L.Structure M] {n : ℕ}
    (D : L.Formula (P ⊕ Fin (n + 1))) (v : P → M) (y : Fin n → M) (t : Fin 1 → M) :
    (curryFirstCoordinateFormula D).Realize (Sum.elim (Sum.elim v y) t) ↔
      D.Realize (Sum.elim v (Fin.cons (t 0) y)) := by
  simp only [curryFirstCoordinateFormula, Formula.realize_relabel]
  have he : Sum.elim (Sum.elim v y) t ∘
      Sum.elim (fun p => Sum.inl (Sum.inl p))
        (Fin.cases (Sum.inr (0 : Fin 1)) (fun i => Sum.inl (Sum.inr i))) =
        Sum.elim v (Fin.cons (t 0) y) := by
    funext i
    cases i with
    | inl p => rfl
    | inr i => refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [he]

inductive CylindricalFormulaTree (L : Language) (P : Type*) : ℕ → Type _ where
  | base (domain : L.Formula (P ⊕ Fin 0)) : CylindricalFormulaTree L P 0
  | step {n : ℕ} (child : CylindricalFormulaTree L P n) (kind : CylinderFibreKind)
      (domain : L.Formula (P ⊕ Fin (n + 1))) : CylindricalFormulaTree L P (n + 1)

def CylindricalFormulaTree.domain {P : Type*} : {n : ℕ} → CylindricalFormulaTree L P n → L.Formula (P ⊕ Fin n)
  | _, .base D => D
  | _, .step _ _ D => D

def CylindricalFormulaTree.shape {P : Type*} : {n : ℕ} → CylindricalFormulaTree L P n → CylindricalShape n
  | _, .base _ => .base
  | _, .step C k _ => k.attach C.shape

def cylindricalStepValidityFormula {P : Type*} {n : ℕ} (k : CylinderFibreKind)
    (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (C : L.Formula (P ⊕ Fin n)) (D : L.Formula (P ⊕ Fin (n + 1))) : L.Formula P :=
  let F := curryFirstCoordinateFormula D
  let empty := ((U.relabel (fun _ => Sum.inr (0 : Fin 1))).imp F.not).iAlls (Fin 1)
  ((C.imp (cylindricalFibreValidityFormula k U E T F)) ⊓ (C.not.imp empty)).iAlls (Fin n)

def CylindricalFormulaTree.validity {P : Type*}
    (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2)) :
    {n : ℕ} → CylindricalFormulaTree L P n → L.Formula P
  | _, .base D => setEqualityValidityFormula D ⊤
  | _, .step C k D => C.validity U E T ⊓ quotientDomainValidityFormula U E D ⊓
      cylindricalStepValidityFormula k U E T C.domain D

theorem cylindricalStepValidityFormula_realize {P M : Type*} [L.Structure M] {n : ℕ}
    (k : CylinderFibreKind) (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (C : L.Formula (P ⊕ Fin n)) (D : L.Formula (P ⊕ Fin (n + 1))) (v : P → M) :
    (cylindricalStepValidityFormula k U E T C D).Realize v ↔
      ∀ y : Fin n → M,
        (C.Realize (Sum.elim v y) →
          (cylindricalFibreValidityFormula k U E T (curryFirstCoordinateFormula D)).Realize (Sum.elim v y)) ∧
        (¬ C.Realize (Sum.elim v y) → ∀ t : Fin 1 → M, U.Realize t →
          ¬ D.Realize (Sum.elim v (Fin.cons (t 0) y))) := by
  simp only [cylindricalStepValidityFormula, Formula.realize_iAlls, Formula.realize_inf,
    Formula.realize_imp, Formula.realize_not, curryFirstCoordinateFormula_realize,
    Formula.realize_relabel]
  have he (y : Fin n → M) (t : Fin 1 → M) :
      Sum.elim (Sum.elim v y) t ∘ (fun _ => Sum.inr (0 : Fin 1)) = t := by
    funext i; fin_cases i; rfl
  simp only [he]

theorem CylindricalFormulaTree.domainValidity {P M : Type*} [L.Structure M]
    (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2)) {n : ℕ}
    (C : CylindricalFormulaTree L P n) (v : P → M) (h : (C.validity U E T).Realize v) :
    (quotientDomainValidityFormula U E C.domain).Realize v := by
  cases C with
  | base D =>
    apply (quotientDomainValidityFormula_realize U E D v).mpr
    constructor
    · intro x hx i
      exact Fin.elim0 i
    · intro x y _ _ _
      have he : x = y := Subsingleton.elim _ _
      subst y
      rfl
  | step C k D =>
    simp only [validity, Formula.realize_inf] at h
    exact h.1.2

end DiamondIntegral.Section5
