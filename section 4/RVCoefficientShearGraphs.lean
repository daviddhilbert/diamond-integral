import «section 4».RVDefinableTupleMaps
import «section 4».RVVariableMultiplication
import «section 4».RVScaledRays

/-! Multiplication of a free proper RV coordinate by a retained coefficient
coordinate has a definable graph over the original base. The coefficient
tuple is retained, so no point of a finite RV coefficient set is selected. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoefficientShearGraphs
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def shear {a : ℕ} (j : Fin a) (u : Fin (1 + a) → M) : Fin (1 + a) → M :=
  join 1 a (u ∘ headIndex 1 a) ![iRVMul (u (headIndex 1 a j)) (u (tailIndex 1 a 0))]

theorem shear_join {a : ℕ} (j : Fin a) (x : Fin a → M) (z : Fin 1 → M) :
    shear j (join 1 a x z) = join 1 a x (RVNamedMultiplication.scale (x j) z) := by
  have hh : join 1 a x z ∘ headIndex 1 a = x := funext (join_head 1 a x z)
  unfold shear RVNamedMultiplication.scale
  rw [hh, join_head, join_tail]

theorem graph_definable (B : Base (M := M)) {a : ℕ} (I : Set (Fin (1 + a) → M))
    (hI : DefinableOverBase B (fun _ : Fin (1 + a) => .rv) I) (j : Fin a) :
    DefinableOverBase B (fun _ : Fin ((1 + a) + (1 + a)) => .rv) (graphOn I (shear j)) := by
  apply RVDefinableTupleMaps.graph_definable B I hI (shear j)
  apply GammaBoundedProducts.all_coordinates 1 a
    (fun t => DefinableOverBase B (fun _ : Fin (1 + (1 + a)) => .rv)
      (graphOn I (fun u => ![shear j u t]))) id
  · intro i
    have he : (fun u : Fin (1 + a) → M => ![shear j u (headIndex 1 a i)]) =
        (fun u => u ∘ (fun _ : Fin 1 => headIndex 1 a i)) := by
      funext u l
      fin_cases l
      simp only [shear, join_head, Function.comp_apply]
      rfl
    change DefinableOverBase B (fun _ : Fin (1 + (1 + a)) => .rv)
      (graphOn I (fun u => ![shear j u (headIndex 1 a i)]))
    rw [he]
    exact RVCoordinateMaps.coordinate_graph_definable B I hI (fun _ : Fin 1 => headIndex 1 a i)
  · intro i
    fin_cases i
    have he : (fun u : Fin (1 + a) → M => ![shear j u (tailIndex 1 a 0)]) =
        (fun u => ![iRVMul (u (headIndex 1 a j)) (u (tailIndex 1 a 0))]) := by
      funext u
      simp only [shear, join_tail, Matrix.cons_val_zero]
    change DefinableOverBase B (fun _ : Fin (1 + (1 + a)) => .rv)
      (graphOn I (fun u => ![shear j u (tailIndex 1 a 0)]))
    rw [he]
    exact RVVariableMultiplication.scalar_graph_definable B I hI (headIndex 1 a j) (tailIndex 1 a 0)

end DiamondIntegral.Section4.RVCoefficientShearGraphs
