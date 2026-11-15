import «section 5».CylindricalFormulaTrees

/-! Exact predicate-row agreement preserves the entire Euler certificate,
including its first-order validity and its discrete cylindrical shape. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

theorem CylinderFibreKind.conditionFormula_parameter_independent {P Q M : Type*} [L.Structure M]
    (k : CylinderFibreKind) (E T : L.Formula (Fin 2)) (v : P → M) (w : Q → M)
    (a : Fin k.endpoints → M) (t : Fin 1 → M) :
    (k.conditionFormula (P := P) E T).Realize (Sum.elim v (Sum.elim a t)) ↔
      (k.conditionFormula (P := Q) E T).Realize (Sum.elim w (Sum.elim a t)) := by
  cases k <;> simp [conditionFormula, binaryRelabel_realize]

theorem CylinderFibreKind.orderFormula_parameter_independent {P Q M : Type*} [L.Structure M]
    (k : CylinderFibreKind) (T : L.Formula (Fin 2)) (v : P → M) (w : Q → M)
    (a : Fin k.endpoints → M) :
    (k.orderFormula (P := P) T).Realize (Sum.elim v a) ↔
      (k.orderFormula (P := Q) T).Realize (Sum.elim w a) := by
  cases k <;> simp [orderFormula, binaryRelabel_realize]

theorem cylindricalFibreValidity_congr {P Q M : Type*} [L.Structure M]
    (k : CylinderFibreKind) (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ Fin 1)) (F : L.Formula (Q ⊕ Fin 1))
    (v : P → M) (w : Q → M)
    (h : ∀ t, D.Realize (Sum.elim v t) ↔ F.Realize (Sum.elim w t)) :
    (cylindricalFibreValidityFormula k U E T D).Realize v ↔
      (cylindricalFibreValidityFormula k U E T F).Realize w := by
  rw [cylindricalFibreValidityFormula_realize, cylindricalFibreValidityFormula_realize]
  simp_rw [h, k.orderFormula_parameter_independent T v w,
    k.conditionFormula_parameter_independent E T v w]

theorem quotientDomainValidity_congr {P Q α M : Type*} [Finite α] [L.Structure M]
    (U : L.Formula (Fin 1)) (E : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ α)) (F : L.Formula (Q ⊕ α)) (v : P → M) (w : Q → M)
    (h : ∀ t, D.Realize (Sum.elim v t) ↔ F.Realize (Sum.elim w t)) :
    (quotientDomainValidityFormula U E D).Realize v ↔ (quotientDomainValidityFormula U E F).Realize w := by
  rw [quotientDomainValidityFormula_realize, quotientDomainValidityFormula_realize]
  simp_rw [h]

theorem cylindricalStepValidity_congr {P Q M : Type*} [L.Structure M] {n : ℕ}
    (k : CylinderFibreKind) (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (C : L.Formula (P ⊕ Fin n)) (D : L.Formula (P ⊕ Fin (n + 1)))
    (F : L.Formula (Q ⊕ Fin n)) (G : L.Formula (Q ⊕ Fin (n + 1))) (v : P → M) (w : Q → M)
    (hC : ∀ x, C.Realize (Sum.elim v x) ↔ F.Realize (Sum.elim w x))
    (hD : ∀ x, D.Realize (Sum.elim v x) ↔ G.Realize (Sum.elim w x)) :
    (cylindricalStepValidityFormula k U E T C D).Realize v ↔
      (cylindricalStepValidityFormula k U E T F G).Realize w := by
  rw [cylindricalStepValidityFormula_realize, cylindricalStepValidityFormula_realize]
  have hf (y : Fin n → M) :
      (cylindricalFibreValidityFormula k U E T (curryFirstCoordinateFormula D)).Realize (Sum.elim v y) ↔
        (cylindricalFibreValidityFormula k U E T (curryFirstCoordinateFormula G)).Realize (Sum.elim w y) :=
    cylindricalFibreValidity_congr k U E T _ _ _ _ (by
      intro t
      rw [curryFirstCoordinateFormula_realize, curryFirstCoordinateFormula_realize]
      exact hD _)
  simp_rw [hC, hD, hf]

inductive CylindricalFormulaTree.RowRelated {P Q M : Type*} [L.Structure M]
    (v : P → M) (w : Q → M) : {n : ℕ} → CylindricalFormulaTree L P n → CylindricalFormulaTree L Q n → Prop where
  | base {D F} (row : ∀ x, D.Realize (Sum.elim v x) ↔ F.Realize (Sum.elim w x)) :
      RowRelated v w (.base D) (.base F)
  | step {n C F} {k : CylinderFibreKind}
      {D : L.Formula (P ⊕ Fin (n + 1))} {G : L.Formula (Q ⊕ Fin (n + 1))}
      (child : RowRelated v w C F)
      (row : ∀ x, D.Realize (Sum.elim v x) ↔ G.Realize (Sum.elim w x)) :
      RowRelated v w (.step C k D) (.step F k G)

theorem CylindricalFormulaTree.RowRelated.domain {P Q M : Type*} [L.Structure M]
    {v : P → M} {w : Q → M} {n : ℕ} {C : CylindricalFormulaTree L P n} {D : CylindricalFormulaTree L Q n}
    (h : RowRelated v w C D) : ∀ x, C.domain.Realize (Sum.elim v x) ↔ D.domain.Realize (Sum.elim w x) := by
  cases h with
  | base h => exact h
  | step _ h => exact h

theorem CylindricalFormulaTree.RowRelated.shape {P Q M : Type*} [L.Structure M]
    {v : P → M} {w : Q → M} {n : ℕ} {C : CylindricalFormulaTree L P n} {D : CylindricalFormulaTree L Q n}
    (h : RowRelated v w C D) : C.shape = D.shape := by
  induction h with
  | base _ => rfl
  | step h _ ih => exact congrArg (fun s => CylinderFibreKind.attach _ s) ih

theorem CylindricalFormulaTree.RowRelated.validity {P Q M : Type*} [L.Structure M]
    {v : P → M} {w : Q → M} {n : ℕ} {C : CylindricalFormulaTree L P n} {D : CylindricalFormulaTree L Q n}
    (h : RowRelated v w C D) (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2)) :
    (C.validity U E T).Realize v ↔ (D.validity U E T).Realize w := by
  induction h with
  | base h =>
    simp only [CylindricalFormulaTree.validity, setEqualityValidityFormula_realize]
    apply Iff.intro
    · intro he
      apply Set.ext
      intro x
      simpa only [Set.mem_ofPred_eq, Formula.realize_top, ← h x] using Set.ext_iff.mp he x
    · intro he
      apply Set.ext
      intro x
      simpa only [Set.mem_ofPred_eq, Formula.realize_top, h x] using Set.ext_iff.mp he x
  | step hrow hD ih =>
    simp only [CylindricalFormulaTree.validity, Formula.realize_inf]
    exact and_congr (and_congr ih (quotientDomainValidity_congr U E _ _ _ _ hD))
      (cylindricalStepValidity_congr _ U E T _ _ _ _ _ _ hrow.domain hD)

end DiamondIntegral.Section5
