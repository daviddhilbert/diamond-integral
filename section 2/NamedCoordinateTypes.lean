import «section 2».DiscTypeFibres

/-! Coordinate fibres and nonempty subsets of complete types over existing
disc names. Only the other actual VF coordinates enter the real base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem GeneratesTypeOverFiniteDiscNames.coordinate_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) {B : ParameterBase M} {k n : ℕ}
    {closed : Fin k → Bool} {d : Fin k → VF M} {δ : Fin k → Gamma M}
    {A : Set (Fin (n+1) → M)}
    (hA : GeneratesTypeOverFiniteDiscNames B closed d δ (fun _ => .vf) A)
    (a : Fin (n+1) → M) (ha : a ∈ A) (i : Fin (n+1)) :
    GeneratesTypeOverFiniteDiscNames (tupleBase B (Fin.removeNth i a)) closed d δ
      (fun _ : Fin 1 => .vf) {z | Fin.insertNth i (z 0) (Fin.removeNth i a) ∈ A} := by
  classical
  refine ⟨⟨fun _ => a i,?_⟩,?_,?_⟩
  · change Fin.insertNth i (a i) (Fin.removeNth i a) ∈ A
    rwa [Fin.insertNth_self_removeNth]
  · intro z hz j
    fin_cases j
    change sortEval SortTag.vf (z 0)
    simpa only [Fin.insertNth_apply_same] using hA.2.1 hz i
  · intro C hC
    have hnames (j : Fin n) : sortEval SortTag.vf (Fin.removeNth i a j) := hA.2.1 ha (i.succAbove j)
    obtain ⟨P,hP,hrow⟩ := promote_tuple_definable_disc_names hc B closed d δ
      (fun _ : Fin n => .vf) (Fin.removeNth i a) hnames (fun _ : Fin 1 => .vf) C hC
    let π : Fin (n+1) → Fin (n+1) := Fin.lastCases i i.succAbove
    have happend (z : Fin 1 → M) :
        Fin.insertNth i (z 0) (Fin.removeNth i a) ∘ π = Fin.append (Fin.removeNth i a) z := by
      funext j
      refine Fin.lastCases ?_ (fun q => ?_) j
      · simp only [Function.comp_apply,π,Fin.lastCases_last,Fin.insertNth_apply_same,
          Fin.append_right_eq_snoc,Fin.snoc_last]
      · simp only [Function.comp_apply,π,Fin.lastCases_castSucc,Fin.insertNth_apply_succAbove,
          Fin.append_right_eq_snoc,Fin.snoc_castSucc]
    have hU := hP.preimage_real (fun _ : Fin (n+1) => .vf) π
    rcases hA.2.2 _ hU with hsub | hdis
    · left
      intro z hz
      have hp := (hsub hz).1
      rw [happend] at hp
      exact (hrow z).mp hp
    · right
      apply Set.disjoint_left.mpr
      intro z hz hzC
      apply Set.disjoint_left.mp hdis hz
      refine ⟨?_,hA.2.1 hz⟩
      rw [happend]
      exact (hrow z).mpr hzC

end DiamondIntegral.Section2
