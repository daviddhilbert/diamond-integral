import «section 5».CylindricalFibreSyntax
import Mathlib.Order.Interval.Set.LinearOrder

/-! Ordered endpoints of each nonempty cylindrical fibre are unique. -/
set_option autoImplicit false
namespace DiamondIntegral.Section5

theorem CylinderFibreKind.endpoints_unique {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
    (shape : CylinderFibreKind) (a b : Fin shape.endpoints → Γ)
    (ha : shape.ordered a) (hb : shape.ordered b)
    (he : ∀ t, shape.condition a t ↔ shape.condition b t) : a = b := by
  cases shape with
  | graph =>
    have h : a 0 = b 0 := (he (a 0)).mp rfl
    funext j
    exact (congrArg a (Subsingleton.elim j 0)).trans (h.trans (congrArg b (Subsingleton.elim 0 j)))
  | band =>
    have hab : Set.Ioo (a 0) (a 1) ⊆ Set.Ioo (b 0) (b 1) := fun t ht => (he t).mp ht
    have hba : Set.Ioo (b 0) (b 1) ⊆ Set.Ioo (a 0) (a 1) := fun t ht => (he t).mpr ht
    have h1 := (Set.Ioo_subset_Ioo_iff ha).mp hab
    have h2 := (Set.Ioo_subset_Ioo_iff hb).mp hba
    funext j
    fin_cases j
    · exact le_antisymm h2.1 h1.1
    · exact le_antisymm h1.2 h2.2
  | upperRay =>
    have h : a 0 = b 0 := Set.Ioi_injective (Set.ext he)
    funext j
    exact (congrArg a (Subsingleton.elim j 0)).trans (h.trans (congrArg b (Subsingleton.elim 0 j)))
  | lowerRay =>
    have h : a 0 = b 0 := Set.Iio_injective (Set.ext he)
    funext j
    exact (congrArg a (Subsingleton.elim j 0)).trans (h.trans (congrArg b (Subsingleton.elim 0 j)))
  | line => exact Subsingleton.elim _ _

end DiamondIntegral.Section5
