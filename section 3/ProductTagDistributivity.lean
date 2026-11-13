import Mathlib.Logic.Equiv.Fin.Basic

/-! The explicit finite-tag distributivity permutation. -/
set_option autoImplicit false
namespace DiamondIntegral.Section3

def finProductSumDistrib (a b c : ℕ) : Fin (a * (b + c)) ≃ Fin (a * b + a * c) :=
  (finProdFinEquiv.symm : Fin (a * (b + c)) ≃ Fin a × Fin (b + c)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin a)) finSumFinEquiv.symm).trans
      ((Equiv.prodSumDistrib (Fin a) (Fin b) (Fin c)).trans
        ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)))

@[simp] theorem finProductSumDistrib_left {a b c : ℕ} (i : Fin a) (j : Fin b) :
    finProductSumDistrib a b c (finProdFinEquiv (i, Fin.castAdd c j)) =
      Fin.castAdd (a * c) (finProdFinEquiv (i, j)) := by
  simp only [finProductSumDistrib, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.prodSumDistrib_apply_left,
    Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

@[simp] theorem finProductSumDistrib_right {a b c : ℕ} (i : Fin a) (j : Fin c) :
    finProductSumDistrib a b c (finProdFinEquiv (i, Fin.natAdd b j)) =
      Fin.natAdd (a * b) (finProdFinEquiv (i, j)) := by
  simp only [finProductSumDistrib, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.prodSumDistrib_apply_right,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

end DiamondIntegral.Section3
