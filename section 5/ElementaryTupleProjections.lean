import «section 5».ElementaryNamedDefinableSets
import Mathlib.Data.Fin.Tuple.Basic

/-! Restriction along an elementary embedding commutes with existential
projection of an actual definable graph. In particular, an output over
an input from the smaller model can be chosen in that smaller model. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language} {M N P : Type} [L.Structure M] [L.Structure N]
variable {n m : ℕ}

def splitTupleFormula (φ : L.Formula (P ⊕ Fin (n+m))) :
    L.Formula ((P ⊕ Fin n) ⊕ Fin m) :=
  φ.relabel ((_root_.Equiv.sumAssoc P (Fin n) (Fin m)).symm ∘
    Sum.map id finSumFinEquiv.symm)

theorem splitTupleFormula_realize (φ : L.Formula (P ⊕ Fin (n+m)))
    (c : P → M) (x : Fin n → M) (y : Fin m → M) :
    (splitTupleFormula φ).Realize (Sum.elim (Sum.elim c x) y) ↔
      φ.Realize (Sum.elim c (Fin.append x y)) := by
  rw [splitTupleFormula,Formula.realize_relabel]
  apply Iff.of_eq
  congr 1
  funext i
  cases i with
  | inl p => rfl
  | inr j =>
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;>
      simp [Function.comp_def,Fin.append_left,Fin.append_right]

theorem elementary_tuple_exists_row (e : M ↪ₑ[L] N) (c : P → M)
    (φ : L.Formula (P ⊕ Fin (n+m))) (x : Fin n → M) :
    (∃ y : Fin m → N,φ.Realize (Sum.elim (e ∘ c) (Fin.append (e ∘ x) y))) ↔
      ∃ y : Fin m → M,φ.Realize (Sum.elim c (Fin.append x y)) := by
  have h := e.map_formula ((splitTupleFormula φ).iExs (Fin m)) (Sum.elim c x)
  have he : e ∘ Sum.elim c x = Sum.elim (e ∘ c) (e ∘ x) := by
    funext i
    cases i <;> rfl
  simpa only [he,Formula.realize_iExs,splitTupleFormula_realize] using h

theorem elementary_actual_projection (e : M ↪ₑ[L] N) (c : P → M)
    (G : L.DefinableSet (Set.range (e ∘ c)) (Fin (n+m))) (x : Fin n → M) :
    (∃ y : Fin m → N,Fin.append (e ∘ x) y ∈ G.val) ↔
      ∃ y : Fin m → M,Fin.append x y ∈ (elementaryActualDefinableEquiv e c G).val := by
  let T := (namedActualDefinableEquiv (e ∘ c)).symm G
  obtain ⟨φ,hφ⟩ := T.property
  have hg : G.val = namedFormulaSet (e ∘ c) φ := hφ
  have hsmall : (elementaryActualDefinableEquiv e c G).val = namedFormulaSet c φ := by
    ext w
    change e ∘ w ∈ G.val ↔ w ∈ namedFormulaSet c φ
    rw [hg,elementary_namedFormula_mem]
  rw [hg,hsmall]
  exact elementary_tuple_exists_row e c φ x

end DiamondIntegral.Section5
