import «section 5».FirstOrderEulerCertificates
import «section 5».CylindricalFormulaCongruence

/-! Whole finite Euler certificates retain validity under primitive row
agreement. Their source is also certified as a full quotient preimage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language}

theorem finitePartitionValidity_congr {P Q α ι M : Type*} [Finite α] [Finite ι] [L.Structure M]
    (D : L.Formula (P ⊕ α)) (C : ι → L.Formula (P ⊕ α))
    (F : L.Formula (Q ⊕ α)) (G : ι → L.Formula (Q ⊕ α)) (v : P → M) (w : Q → M)
    (hD : ∀ x, D.Realize (Sum.elim v x) ↔ F.Realize (Sum.elim w x))
    (hC : ∀ i x, (C i).Realize (Sum.elim v x) ↔ (G i).Realize (Sum.elim w x)) :
    (finitePartitionValidityFormula D C).Realize v ↔ (finitePartitionValidityFormula F G).Realize w := by
  rw [finitePartitionValidityFormula_realize, finitePartitionValidityFormula_realize]
  simp_rw [hD, hC]

theorem EulerFormulaCertificate.source_quotient_validity {P M : Type*} [L.Structure M] {n : ℕ}
    (C : EulerFormulaCertificate L P n) (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ Fin n)) (v : P → M) (h : (C.validity U E T D).Realize v) :
    (quotientDomainValidityFormula U E D).Realize v := by
  have hh := h
  simp only [validity, Formula.realize_inf, finiteWitnessValidityFormula_realize] at hh
  obtain ⟨hcover, _⟩ := (finitePartitionValidityFormula_realize D (fun i => (C.cells i).domain) v).mp hh.2
  have hc (i : Fin C.size) := (quotientDomainValidityFormula_realize U E (C.cells i).domain v).mp
    ((C.cells i).domainValidity U E T v (hh.1 i))
  apply (quotientDomainValidityFormula_realize U E D v).mpr
  constructor
  · intro x hx
    obtain ⟨i, hi⟩ := (hcover x).mp hx
    exact (hc i).1 x hi
  · intro x y hx hy he
    rw [hcover x, hcover y]
    exact exists_congr (fun i => (hc i).2 x y hx hy he)

theorem EulerFormulaCertificate.validity_congr {P Q M : Type*} [L.Structure M] {n : ℕ}
    (C : EulerFormulaCertificate L P n) (F : Fin C.size → CylindricalFormulaTree L Q n)
    (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ Fin n)) (G : L.Formula (Q ⊕ Fin n)) (v : P → M) (w : Q → M)
    (hrow : ∀ i, CylindricalFormulaTree.RowRelated v w (C.cells i) (F i))
    (hD : ∀ x, D.Realize (Sum.elim v x) ↔ G.Realize (Sum.elim w x)) :
    (C.validity U E T D).Realize v ↔ ((EulerFormulaCertificate.mk C.size F).validity U E T G).Realize w := by
  simp only [validity, Formula.realize_inf, finiteWitnessValidityFormula_realize]
  exact and_congr (forall_congr' (fun i => (hrow i).validity U E T))
    (finitePartitionValidity_congr D _ G _ v w hD (fun i => (hrow i).domain))

theorem EulerFormulaCertificate.eulerValue_congr {P Q M : Type*} [L.Structure M] {n : ℕ}
    (C : EulerFormulaCertificate L P n) (F : Fin C.size → CylindricalFormulaTree L Q n)
    (v : P → M) (w : Q → M) (hrow : ∀ i, CylindricalFormulaTree.RowRelated v w (C.cells i) (F i))
    (k : DiamondIntegral.Section4.EulerKind) :
    C.eulerValue k = (EulerFormulaCertificate.mk C.size F).eulerValue k := by
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun s => s.eulerValue k) (hrow i).shape)

end DiamondIntegral.Section5
