import «section 3».OrderBoundary
import «section 3».FiniteColumnPartition
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
set_option autoImplicit false
open Classical SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {α X : Type} [LinearOrder α]

theorem finite_columns_of_common_controller (R : α → X → Prop) (A : Set X)
    (F : Finset α) (h : ∀ x ∈ A, FiniteOrder.Controls F (relationColumn R x)) :
    (relationColumn R '' A).Finite := by
  classical
  let pattern (γ : α) : F → Bool × Bool := fun p => (decide (γ < p.val),decide (p.val < γ))
  have hsame {γ δ : α} (he : pattern γ = pattern δ) : FiniteOrder.Pattern F γ δ := by
    intro p hp
    have he' := congrFun he (⟨p,hp⟩ : F)
    have h1 := congrArg Prod.fst he'
    have h2 := congrArg Prod.snd he'
    exact ⟨decide_eq_decide.mp h1,decide_eq_decide.mp h2⟩
  have hf : (Set.range (fun W : Set (F → Bool × Bool) => pattern ⁻¹' W)).Finite := Set.finite_range _
  apply hf.subset
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨pattern '' relationColumn R x,?_⟩
  ext γ
  constructor
  · rintro ⟨δ,hδ,he⟩
    exact (h x hx δ γ (hsame he)).mp hδ
  · intro hγ
    exact ⟨γ,hγ,rfl⟩

theorem finite_columns_of_finite_boundary_union [NoMinOrder α] [NoMaxOrder α] [DenselyOrdered α]
    (R : α → X → Prop) (A : Set X)
    (hctrl : ∀ x ∈ A, ∃ F, FiniteOrder.Controls F (relationColumn R x))
    (E : Set α) (hE : E.Finite)
    (hsub : ∀ x ∈ A, orderBoundary (relationColumn R x) ⊆ E) :
    (relationColumn R '' A).Finite := by
  apply finite_columns_of_common_controller R A hE.toFinset
  intro x hx γ δ hpat
  apply orderBoundary_controls (hctrl x hx) γ δ
  intro p hp
  exact hpat p (hE.mem_toFinset.mpr (hsub x hx ((orderBoundary_finite_of_controller (hctrl x hx)).mem_toFinset.mp hp)))
end DiamondIntegral.Section3
