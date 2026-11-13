import «section 4».RVCoordinateMaps
import Section3.GammaClosureLaws

/-! Partial RV tuple maps have original-base definable graphs whenever
all their scalar coordinate graphs do. The actual domain and all RV sort
conditions are retained, also for an empty output tuple. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDefinableTupleMaps
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def scalarIndices (m n : ℕ) (i : Fin n) : Fin (1 + m) → Fin (n + m) :=
  join 1 m (headIndex n m) (fun _ => tailIndex n m i)

theorem scalarIndices_head {m n : ℕ} (w : Fin (n + m) → M) (i : Fin n) :
    (w ∘ scalarIndices m n i) ∘ headIndex 1 m = w ∘ headIndex n m := by
  funext j
  simp only [Function.comp_apply, scalarIndices, join_head]

theorem scalarIndices_tail {m n : ℕ} (w : Fin (n + m) → M) (i : Fin n) :
    (w ∘ scalarIndices m n i) ∘ tailIndex 1 m = ![w (tailIndex n m i)] := by
  funext j
  fin_cases j
  simp only [Function.comp_apply, scalarIndices, join_tail]
  rfl

theorem scalar_pullback {m n : ℕ} (I : Set (Fin m → M))
    (F : (Fin m → M) → (Fin n → M)) (w : Fin (n + m) → M) (i : Fin n) :
    w ∘ scalarIndices m n i ∈ graphOn I (fun u => ![F u i]) ↔
      w ∘ headIndex n m ∈ I ∧ F (w ∘ headIndex n m) i = w (tailIndex n m i) := by
  change (_ ∈ I ∧ ![F _ i] = _) ↔ _
  rw [scalarIndices_head, scalarIndices_tail]
  constructor
  · rintro ⟨hi, he⟩
    exact ⟨hi, congrFun he 0⟩
  · rintro ⟨hi, he⟩
    exact ⟨hi, congrArg (fun t => ![t]) he⟩

theorem graph_definable (B : Base (M := M)) {m n : ℕ} (I : Set (Fin m → M))
    (hI : DefinableOverBase B (fun _ : Fin m => .rv) I)
    (F : (Fin m → M) → (Fin n → M))
    (hF : ∀ i, DefinableOverBase B (fun _ : Fin (1 + m) => .rv) (graphOn I (fun u => ![F u i]))) :
    DefinableOverBase B (fun _ : Fin (n + m) => .rv) (graphOn I F) := by
  let P (i : Fin n) : Set (Fin (n + m) → M) :=
    {w | w ∘ scalarIndices m n i ∈ graphOn I (fun u => ![F u i]) ∧ w ∈ sortedUniverse (fun _ => .rv)}
  have hP (i : Fin n) : DefinableOverBase B (fun _ : Fin (n + m) => .rv) (P i) :=
    (hF i).preimage_real (fun _ : Fin (n + m) => .rv) (scalarIndices m n i)
  have h := (hI.preimage_real (fun _ : Fin (n + m) => .rv) (headIndex n m)).inter
    (DefinableOverBase.finite_iInter Finset.univ P (fun i _ => hP i))
  convert h using 1
  ext w
  change (w ∘ headIndex n m ∈ I ∧ F (w ∘ headIndex n m) = w ∘ tailIndex n m) ↔
    ((w ∘ headIndex n m ∈ I ∧ w ∈ sortedUniverse (fun _ => .rv)) ∧
      w ∈ sortedUniverse (fun _ => .rv) ∧ ∀ i ∈ Finset.univ, w ∈ P i)
  constructor
  · rintro ⟨hi, he⟩
    have hrv : w ∈ sortedUniverse (fun _ => .rv) := by
      apply GammaBoundedProducts.all_coordinates n m iRV w
      · intro j
        exact hI.proper _ hi j
      · intro i
        have hg : join 1 m (w ∘ headIndex n m) ![F (w ∘ headIndex n m) i] ∈
            graphOn I (fun u => ![F u i]) := (graphOn_exists _ _ _).mpr ⟨_, hi, rfl⟩
        have hp := (hF i).proper _ hg (tailIndex 1 m 0)
        have he' : F (w ∘ headIndex n m) i = w (tailIndex n m i) := congrFun he i
        have hp' : iRV (F (w ∘ headIndex n m) i) := by
          change iRV ((join 1 m (w ∘ headIndex n m) ![F (w ∘ headIndex n m) i]) (tailIndex 1 m 0)) at hp
          rw [join_tail] at hp
          exact hp
        exact he' ▸ hp'
    refine ⟨⟨hi, hrv⟩, hrv, ?_⟩
    intro i _
    exact ⟨(scalar_pullback I F w i).mpr ⟨hi, congrFun he i⟩, hrv⟩
  · rintro ⟨⟨hi, _⟩, _, hp⟩
    refine ⟨hi, ?_⟩
    funext i
    exact ((scalar_pullback I F w i).mp (hp i (Finset.mem_univ i)).1).2

end DiamondIntegral.Section4.RVDefinableTupleMaps
