import «section 5».NativeRVValuePatterns

/-! Distinct full RV value patterns have a literal parameter-free formula.
The formula is interpreted only on actual RV rows, including their zeros. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def valueDistinctFormula {P α ι : Type*} [Finite α] [Finite ι]
    (E : LRV.Formula (Fin 2)) (f : ι → α → P) : LRV.Formula P :=
  Formula.iInf (fun i => Formula.iInf (fun j =>
    if i = j then ⊤ else (tupleQuotientEqualityFormula E (f i) (f j)).not))

theorem native_tuple_quotient_equality {P : Type*} {n : ℕ}
    (E : NativeRVValueSyntax M) (f g : Fin n → P) (v : P → M)
    (hf : ∀ i, iRV (v (f i))) (hg : ∀ i, iRV (v (g i))) :
    (tupleQuotientEqualityFormula E.equal f g).Realize v ↔
      rawRVValuePattern (v ∘ f) = rawRVValuePattern (v ∘ g) := by
  rw [tupleQuotientEqualityFormula_realize, funext_iff]
  apply forall_congr'
  intro i
  rw [E.realize]
  simpa only [rawRVValuePattern, Function.comp_apply, dif_pos (hf i), dif_pos (hg i), Values.sameValue] using
    (Values.vrv_eq_iff (⟨v (f i), hf i⟩ : CanonicalRV.RVSort M) ⟨v (g i), hg i⟩).symm

theorem valueDistinctFormula_realize {P ι : Type*} [Finite ι] {n : ℕ}
    (E : NativeRVValueSyntax M) (f : ι → Fin n → P) (v : P → M)
    (hRV : ∀ i j, iRV (v (f i j))) :
    (valueDistinctFormula E.equal f).Realize v ↔
      Function.Injective (fun i => rawRVValuePattern (v ∘ f i)) := by
  simp only [valueDistinctFormula, Formula.realize_iInf]
  constructor
  · intro h i j hij
    by_contra hn
    have hh := h i j
    rw [if_neg hn, Formula.realize_not,
      native_tuple_quotient_equality E (f i) (f j) v (hRV i) (hRV j)] at hh
    exact hh hij
  · intro h i j
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, Formula.realize_not,
        native_tuple_quotient_equality E (f i) (f j) v (hRV i) (hRV j)]
      exact fun he => hij (h he)

end DiamondIntegral.Section5
