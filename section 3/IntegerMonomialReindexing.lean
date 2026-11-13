import «section 3».IntegerMonomialMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {α β ι G : Type} [Fintype α] [Fintype β] [CommGroup G]

theorem integerMonomialMap_reindex_input (e : α ≃ β) (A : Matrix ι α ℤ) (z : β → G) :
    integerMonomialMap A (z ∘ e) = integerMonomialMap (fun i j => A i (e.symm j)) z := by
  funext i
  simpa only [integerMonomialMap,Function.comp_apply,Equiv.symm_apply_apply] using
    e.prod_comp (fun j => z j ^ A i (e.symm j))
end DiamondIntegral.Section3
