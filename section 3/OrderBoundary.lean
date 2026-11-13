import Section4.CanonicalOrderController
import Mathlib.Data.Set.Finite.Basic
set_option autoImplicit false
open Classical
noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Section4
variable {α : Type} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α] [DenselyOrdered α]

def orderBoundary (D : Set α) : Set α :=
  {a | ¬ ∃ l u, l < a ∧ a < u ∧ ∀ z, l < z → z < u → (z ∈ D ↔ a ∈ D)}

theorem orderBoundary_eq_minimal_controller {D : Set α} {F : Finset α}
    (hF : FiniteOrder.Controls F D) (hmin : ∀ H, FiniteOrder.Controls H D → F.card ≤ H.card) :
    orderBoundary D = (F : Set α) := by
  letI : DecidableEq α := Classical.decEq α
  ext a
  constructor
  · intro ha
    by_contra hn
    exact ha (FiniteOrder.local_constant_of_missing hF hn)
  · intro ha
    rintro ⟨l,u,hl,hu,hloc⟩
    have hE := FiniteOrder.erase_controls_of_local hF hl hu hloc
    exact (not_le_of_gt (Finset.card_erase_lt_of_mem ha)) (hmin _ hE)

theorem orderBoundary_finite_of_controller {D : Set α} (hD : ∃ F, FiniteOrder.Controls F D) :
    (orderBoundary D).Finite := by
  obtain ⟨F,hF,hmin⟩ := FiniteOrder.exists_minimal_controller hD
  rw [orderBoundary_eq_minimal_controller hF hmin]
  exact F.finite_toSet

theorem orderBoundary_controls {D : Set α} (hD : ∃ F, FiniteOrder.Controls F D) :
    FiniteOrder.Controls (orderBoundary_finite_of_controller hD).toFinset D := by
  obtain ⟨F,hF,hmin⟩ := FiniteOrder.exists_minimal_controller hD
  have he : (orderBoundary_finite_of_controller hD).toFinset = F := by
    apply Finset.coe_injective
    rw [Set.Finite.coe_toFinset,orderBoundary_eq_minimal_controller hF hmin]
  rw [he]
  exact hF
end DiamondIntegral.Section3
