import «section 5».CylindricalFibreSyntax

/-! Full finite partition validity: the cover and the exclusion of every
pairwise overlap are both checked, including outside the prescribed domain. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

def finitePartitionValidityFormula {P α ι : Type*} [Finite α] [Finite ι]
    (D : L.Formula (P ⊕ α)) (C : ι → L.Formula (P ⊕ α)) : L.Formula P :=
  (relationalIff D (Formula.iSup C)).iAlls α ⊓
    Formula.iInf (fun i => Formula.iInf (fun j =>
      if i = j then ⊤ else ((C i ⊓ C j).not).iAlls α))

theorem finitePartitionValidityFormula_realize {P α ι M : Type*}
    [Finite α] [Finite ι] [L.Structure M]
    (D : L.Formula (P ⊕ α)) (C : ι → L.Formula (P ⊕ α)) (v : P → M) :
    (finitePartitionValidityFormula D C).Realize v ↔
      (∀ x, D.Realize (Sum.elim v x) ↔ ∃ i, (C i).Realize (Sum.elim v x)) ∧
        ∀ i j, i ≠ j → ∀ x, ¬ ((C i).Realize (Sum.elim v x) ∧ (C j).Realize (Sum.elim v x)) := by
  simp only [finitePartitionValidityFormula, Formula.realize_inf, Formula.realize_iAlls,
    relationalIff_realize, Formula.realize_iSup, Formula.realize_iInf]
  apply and_congr_right
  intro _
  constructor
  · intro h i j hij
    have hh := h i j
    rw [if_neg hij, Formula.realize_iAlls] at hh
    intro x
    simpa only [Formula.realize_not, Formula.realize_inf] using hh x
  · intro h i j
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, Formula.realize_iAlls]
      intro x
      simpa only [Formula.realize_not, Formula.realize_inf] using h i j hij x

theorem finitePartitionValidityFormula_unique {P α ι M : Type*}
    [Finite α] [Finite ι] [L.Structure M]
    (D : L.Formula (P ⊕ α)) (C : ι → L.Formula (P ⊕ α)) (v : P → M)
    (h : (finitePartitionValidityFormula D C).Realize v) :
    ∀ x, D.Realize (Sum.elim v x) ↔ ∃! i, (C i).Realize (Sum.elim v x) := by
  obtain ⟨hcover, hdisj⟩ := (finitePartitionValidityFormula_realize D C v).mp h
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (hcover x).mp hx
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra hji
    exact hdisj j i hji x ⟨hj, hi⟩
  · rintro ⟨i, hi, _⟩
    exact (hcover x).mpr ⟨i, hi⟩

end DiamondIntegral.Section5
