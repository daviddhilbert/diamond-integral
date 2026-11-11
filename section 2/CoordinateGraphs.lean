import «section 2».AtomicPolydiscs
import «section 2».VFImages
import «section 2».ScalarImages

/-! Full scalar graphs of coordinate-line restrictions. Only the other
source coordinates are named; the varying input and output remain free. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Restriction of a full definable graph to one coordinate line, over
exactly the original base plus the fixed other VF coordinates. -/
theorem coordinate_line_graph_definable (B : ParameterBase M) {n : ℕ}
    (D : Fin (n+1) → Set M) (f : (Fin (n+1) → M) → M)
    (hA : IsAtomic B (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin (n+2) => .vf)
      (vfFunctionGraph {a | ∀ j, a j ∈ D j} f))
    (a : Fin (n+1) → M) (ha : ∀ j, a j ∈ D j) (i : Fin (n+1)) :
    GammaParameters.DefinableOverBase (tupleBase B (Fin.removeNth i a))
      (fun _ : Fin 2 => .vf)
      (scalarVFGraph (D i) (fun x => f (Function.update a i x))) := by
  classical
  let E := tupleBase B (Fin.removeNth i a)
  have hG' := hG.mono (show B.real ⊆ E.real from Set.subset_union_left)
    (Set.Subset.refl _)
  have hnames (j : Fin n) : GammaParameters.DefinableClosureAtBase E .vf
      (Fin.removeNth i a j) :=
    GammaParameters.real_definableAtBase E .vf {Fin.removeNth i a j}
      (definableClosureAt_of_mem (Or.inr (Set.mem_range_self j))
        (hA.2.2.1 ha (i.succAbove j)))
  let other : Fin n → Fin (n+2) := fun j => (i.succAbove j).castSucc
  have hN := (GammaParameters.tuple_singleton_definable_base E
    (fun _ : Fin n => .vf) (Fin.removeNth i a) hnames).preimage_real
      (fun _ : Fin (n+2) => .vf) other
  let π : Fin 2 → Fin (n+2) := ![i.castSucc, Fin.last (n+1)]
  have hp := (hG'.inter hN).image_real π
  convert hp using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨hzD, hzf⟩
    let b := Function.update a i (z 0)
    let w : Fin (n+2) → M := Fin.snoc b (f b)
    have hb : ∀ j, b j ∈ D j := by
      intro j
      by_cases hj : j = i
      · subst j; simpa [b] using hzD
      · simpa only [b, Function.update_of_ne hj] using ha j
    have hwG : w ∈ vfFunctionGraph {a | ∀ j, a j ∈ D j} f := by
      refine ⟨?_, by simp [w]⟩
      change ∀ j, Fin.init w j ∈ D j
      simpa only [w, Fin.init_snoc] using hb
    have hwN : w ∘ other = Fin.removeNth i a := by
      funext j
      simp [w, other, b, Fin.removeNth, Fin.succAbove_ne]
    refine ⟨w, ⟨hwG, hwN, hG'.proper w hwG⟩, ?_⟩
    funext j
    fin_cases j
    · simp [w, π, b]
    · simp only [Function.comp_apply, π, Matrix.cons_val_succ', Matrix.cons_val_fin_one,
        w, Fin.snoc_last]
      exact hzf.symm
  · rintro ⟨w, ⟨⟨hwA, hwf⟩, hwN, _⟩, he⟩
    let b := Fin.init w
    have hwi : b i = z 0 := by
      have h := congrFun he 0
      simpa only [b, Function.comp_apply, π, Matrix.cons_val_zero, Fin.init] using h
    have hlast : w (Fin.last (n+1)) = z 1 := by
      have h := congrFun he 1
      simpa [π] using h
    have hother : Fin.removeNth i b = Fin.removeNth i a := by
      funext j
      exact congrFun hwN j
    have hb : b = Function.update a i (z 0) := by
      rw [← Fin.insertNth_self_removeNth i b, hwi, hother, Fin.insertNth_removeNth]
    refine ⟨?_, ?_⟩
    · have hh := hwA i
      change b i ∈ D i at hh
      rwa [hwi] at hh
    · change z 1 = f (Function.update a i (z 0))
      change f b = w (Fin.last (n+1)) at hwf
      rw [← hb]
      exact hlast.symm.trans hwf.symm

end DiamondIntegral.Section2
