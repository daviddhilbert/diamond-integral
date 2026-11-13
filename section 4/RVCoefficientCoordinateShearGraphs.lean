import «section 4».RVCoefficientShearGraphs
import «section 4».RVCoordinateScaling

/-! Original-base definability for retaining a coefficient tuple and
scaling one chosen coordinate of an arbitrary finite RV tuple by one
coefficient coordinate. Other coordinates are retained verbatim. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoefficientCoordinateShearGraphs
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks RVCoordinateScaling
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def shear {a n : ℕ} (j : Fin a) (i : Fin n) (u : Fin (n + a) → M) : Fin (n + a) → M :=
  join n a (u ∘ headIndex n a)
    (fun l => if l = i then iRVMul (u (headIndex n a j)) (u (tailIndex n a l)) else u (tailIndex n a l))

theorem shear_join {a n : ℕ} (j : Fin a) (i : Fin n) (x : Fin a → M) (z : Fin n → M)
    (t : Code (M := M)) (ht : raw t = x j) :
    shear j i (join n a x z) = join n a x (scaleAt t i z) := by
  have hh : join n a x z ∘ headIndex n a = x := funext (join_head n a x z)
  unfold shear scaleAt
  rw [hh]
  congr 1
  funext l
  rw [join_head, join_tail, ht]

theorem scalar_projection (B : Base (M := M)) {a : ℕ} (I : Set (Fin a → M))
    (hI : DefinableOverBase B (fun _ : Fin a => .rv) I) (p : Fin a) :
    DefinableOverBase B (fun _ : Fin (1 + a) => .rv) (graphOn I (fun u => ![u p])) := by
  have he : (fun u : Fin a → M => ![u p]) = (fun u => u ∘ (fun _ : Fin 1 => p)) := by
    funext u l
    fin_cases l
    rfl
  rw [he]
  exact RVCoordinateMaps.coordinate_graph_definable B I hI (fun _ : Fin 1 => p)

theorem graph_definable (B : Base (M := M)) {a n : ℕ} (I : Set (Fin (n + a) → M))
    (hI : DefinableOverBase B (fun _ : Fin (n + a) => .rv) I) (j : Fin a) (i : Fin n) :
    DefinableOverBase B (fun _ : Fin ((n + a) + (n + a)) => .rv) (graphOn I (shear j i)) := by
  apply RVDefinableTupleMaps.graph_definable B I hI (shear j i)
  apply GammaBoundedProducts.all_coordinates n a
    (fun t => DefinableOverBase B (fun _ : Fin (1 + (n + a)) => .rv)
      (graphOn I (fun u => ![shear j i u t]))) id
  · intro l
    change DefinableOverBase B (fun _ : Fin (1 + (n + a)) => .rv)
      (graphOn I (fun u => ![shear j i u (headIndex n a l)]))
    have he : (fun u : Fin (n + a) → M => ![shear j i u (headIndex n a l)]) =
        (fun u => ![u (headIndex n a l)]) := by
      funext u
      simp only [shear, join_head, Function.comp_apply]
    rw [he]
    exact scalar_projection B I hI (headIndex n a l)
  · intro l
    change DefinableOverBase B (fun _ : Fin (1 + (n + a)) => .rv)
      (graphOn I (fun u => ![shear j i u (tailIndex n a l)]))
    by_cases hl : l = i
    · have he : (fun u : Fin (n + a) → M => ![shear j i u (tailIndex n a l)]) =
          (fun u => ![iRVMul (u (headIndex n a j)) (u (tailIndex n a l))]) := by
        funext u
        simp only [shear, join_tail, ite_eq_left hl]
      rw [he]
      exact RVVariableMultiplication.scalar_graph_definable B I hI (headIndex n a j) (tailIndex n a l)
    · have he : (fun u : Fin (n + a) → M => ![shear j i u (tailIndex n a l)]) =
          (fun u => ![u (tailIndex n a l)]) := by
        funext u
        simp only [shear, join_tail, ite_eq_right hl]
      rw [he]
      exact scalar_projection B I hI (tailIndex n a l)

end DiamondIntegral.Section4.RVCoefficientCoordinateShearGraphs
