import «section 4».RVNamedMultiplication

/-! The original-base graph of multiplication with both RV inputs free.
This allows a retained coefficient coordinate to supply a multiplier,
without choosing a definable point in its value fibre. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVVariableMultiplication
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def graph : Set (Fin 3 → M) := {z | (∀ i, iRV (z i)) ∧ iRVMul (z 0) (z 1) = z 2}

omit hM in
theorem raw_graph_definable (S : Set M) :
    SpecialTransformations.Section3.DefinableOver S (fun _ : Fin 3 => .rv) (graph (M := M)) := by
  let p : Parameters S := ⟨0, Fin.elim0, (fun _ => .vf), (fun i => i.elim0), (fun i => i.elim0)⟩
  let tm : LRV.Term (Fin 0 ⊕ Fin 3) := .func Fn.rvMul ![.var (.inr 0), .var (.inr 1)]
  let φ : LRV.BoundedFormula (Fin 0) 3 := .equal tm (.var (.inr 2))
  have hs : TmSort p.sorts (fun _ : Fin 3 => .rv) tm = some .rv := by
    apply tmSort_func
    intro i
    fin_cases i <;> rfl
  have hw : WellSorted p.sorts (fun _ : Fin 3 => .rv) φ := .equal (fun _ => .rv) hs rfl
  refine ⟨p, φ, hw, ?_⟩
  ext z
  have he : tm.realize (Sum.elim p.values z) = iRVMul (z 0) (z 1) := by
    change Structure.funMap (L := LRV) Fn.rvMul
      (fun i => (![.var (.inr 0), .var (.inr 1)] i : LRV.Term (Fin 0 ⊕ Fin 3)).realize
        (Sum.elim p.values z)) = _
    have ha : (fun i => (![.var (.inr 0), .var (.inr 1)] i : LRV.Term (Fin 0 ⊕ Fin 3)).realize
        (Sum.elim p.values z)) = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
    rw [ha]
    rfl
  change ((∀ i, iRV (z i)) ∧ iRVMul (z 0) (z 1) = z 2) ↔
    (∀ i, iRV (z i)) ∧ tm.realize (Sum.elim p.values z) = z 2
  rw [he]

theorem graph_definable (B : Base (M := M)) :
    DefinableOverBase B (fun _ : Fin 3 => .rv) (graph (M := M)) :=
  real_definableOverBase B _ _ (raw_graph_definable B.real)

theorem scalar_graph_definable (B : Base (M := M)) {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (p q : Fin n) :
    DefinableOverBase B (fun _ : Fin (1 + n) => .rv)
      (graphOn I (fun u => ![iRVMul (u p) (u q)])) := by
  let π : Fin 3 → Fin (1 + n) := ![headIndex 1 n p, headIndex 1 n q, tailIndex 1 n 0]
  have h := (hI.preimage_real (fun _ : Fin (1 + n) => .rv) (headIndex 1 n)).inter
    ((graph_definable B).preimage_real (fun _ : Fin (1 + n) => .rv) π)
  convert h using 1
  ext w
  change (w ∘ headIndex 1 n ∈ I ∧ ![iRVMul (w (headIndex 1 n p)) (w (headIndex 1 n q))] = w ∘ tailIndex 1 n) ↔
    ((w ∘ headIndex 1 n ∈ I ∧ w ∈ sortedUniverse (fun _ => .rv)) ∧
      (w ∘ π ∈ graph ∧ w ∈ sortedUniverse (fun _ => .rv)))
  constructor
  · rintro ⟨hi, he⟩
    have hrv : w ∈ sortedUniverse (fun _ => .rv) := by
      apply GammaBoundedProducts.all_coordinates 1 n iRV w
      · intro i
        exact hI.proper _ hi i
      · intro i
        fin_cases i
        have he0 := congrFun he 0
        change iRVMul (w (headIndex 1 n p)) (w (headIndex 1 n q)) = w (tailIndex 1 n 0) at he0
        change iRV (w (tailIndex 1 n 0))
        rw [← he0]
        exact rv_mul_mem hM (hI.proper _ hi p) (hI.proper _ hi q)
    refine ⟨⟨hi, hrv⟩, ⟨?_, ?_⟩, hrv⟩
    · exact fun i => hrv (π i)
    · exact congrFun he 0
  · rintro ⟨⟨hi, _⟩, ⟨_, he⟩, _⟩
    refine ⟨hi, ?_⟩
    funext i
    fin_cases i
    exact he

end DiamondIntegral.Section4.RVVariableMultiplication
