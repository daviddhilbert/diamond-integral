import «section 4».RVCoordinateMaps
import Section3.GammaClosureLaws

/-! Multiplication by an original-base definable RV point has an actual
original-base definable graph. The proof eliminates the temporary real
name; it never chooses a section of the Gamma value map. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVNamedMultiplication
open RVMeasuredCharts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem raw_graph_definable (t : M) (ht : iRV t) :
    SpecialTransformations.Section3.DefinableOver ({t} : Set M) (fun _ : Fin 2 => .rv)
      {z | (∀ i, iRV (z i)) ∧ iRVMul t (z 0) = z 1} := by
  let p : Parameters ({t} : Set M) :=
    ⟨1, ![t], (fun _ => .rv), (by intro i; fin_cases i; exact ht),
      (by intro i; fin_cases i; exact Set.mem_singleton t)⟩
  let tm : LRV.Term (Fin 1 ⊕ Fin 2) := .func Fn.rvMul ![.var (.inl 0), .var (.inr 0)]
  let φ : LRV.BoundedFormula (Fin 1) 2 := .equal tm (.var (.inr 1))
  have hs : TmSort p.sorts (fun _ : Fin 2 => .rv) tm = some .rv := by
    apply tmSort_func
    intro i
    fin_cases i <;> rfl
  have hw : WellSorted p.sorts (fun _ : Fin 2 => .rv) φ := .equal (fun _ => .rv) hs rfl
  refine ⟨p, φ, hw, ?_⟩
  ext z
  have he : tm.realize (Sum.elim p.values z) = iRVMul t (z 0) := by
    change Structure.funMap (L := LRV) Fn.rvMul
      (fun i => (![.var (.inl 0), .var (.inr 0)] i : LRV.Term (Fin 1 ⊕ Fin 2)).realize
        (Sum.elim p.values z)) = _
    have hargs : (fun i => (![.var (.inl 0), .var (.inr 0)] i : LRV.Term (Fin 1 ⊕ Fin 2)).realize
        (Sum.elim p.values z)) = ![t, z 0] := by funext i; fin_cases i <;> rfl
    rw [hargs]
    rfl
  change ((∀ i, iRV (z i)) ∧ iRVMul t (z 0) = z 1) ↔
    (∀ i, iRV (z i)) ∧ tm.realize (Sum.elim p.values z) = z 1
  rw [he]

theorem graph_definable (B : Base (M := M)) (t : M) (ht : iRV t)
    (hname : DefinableClosureAtBase B .rv t) :
    DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | (∀ i, iRV (z i)) ∧ iRVMul t (z 0) = z 1} := by
  have h := real_definableOverBase (⟨{t}, ∅⟩ : Base (M := M)) _ _ (raw_graph_definable t ht)
  apply h.eliminate_definable_params
  · rintro c rfl
    exact ⟨.rv, hname⟩
  · intro γ hγ
    exact hγ.elim

def scale (t : M) (u : Fin 1 → M) : Fin 1 → M := ![iRVMul t (u 0)]

theorem graphOn_definable (B : Base (M := M)) (t : M) (ht : iRV t)
    (hname : DefinableClosureAtBase B .rv t) (I : Set (Fin 1 → M))
    (hI : DefinableOverBase B (fun _ : Fin 1 => .rv) I) :
    DefinableOverBase B (fun _ : Fin 2 => .rv) (graphOn I (scale t)) := by
  have h := (hI.preimage_real (fun _ : Fin 2 => .rv) (headIndex 1 1)).inter
    (graph_definable B t ht hname)
  convert h using 1
  ext w
  change (w ∘ headIndex 1 1 ∈ I ∧ scale t (w ∘ headIndex 1 1) = w ∘ tailIndex 1 1) ↔
    (w ∘ headIndex 1 1 ∈ I ∧ (∀ i, iRV (w i))) ∧
      (∀ i, iRV (w i)) ∧ iRVMul t (w 0) = w 1
  constructor
  · rintro ⟨hinput, he⟩
    have h0 : iRV (w 0) := hI.proper _ hinput 0
    have h1 : iRV (w 1) := by
      have he0 := congrFun he 0
      change iRVMul t (w 0) = w 1 at he0
      rw [← he0]
      exact rv_mul_mem hM ht h0
    have hall : ∀ i, iRV (w i) := by intro i; fin_cases i; exact h0; exact h1
    exact ⟨⟨hinput, hall⟩, hall, congrFun he 0⟩
  · rintro ⟨⟨hinput, _⟩, _, he⟩
    refine ⟨hinput, ?_⟩
    funext i
    fin_cases i
    exact he

end DiamondIntegral.Section4.RVNamedMultiplication
