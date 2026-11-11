import «section 2».DiscTupleRealMaps
import «section 2».NamedCoordinateTypes
import «section 2».NamedVFImages
import «section 2».ScalarImages

/-! Actual coordinate sections and their full scalar graphs over exactly
the existing DC names and the other fixed VF coordinates. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped Classical

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem coordinate_section_definable_disc_names (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (C : Set (Fin (n+1) → M)) (hC : DefinableOverFiniteDiscNames B ground d τ (fun _ => .vf) C)
    (b : Fin (n+1) → M) (i : Fin (n+1)) :
    DefinableOverFiniteDiscNames (tupleBase B (Fin.removeNth i b)) ground d τ (fun _ : Fin 1 => .vf)
      {z | Fin.insertNth i (z 0) (Fin.removeNth i b) ∈ C} := by
  let E := tupleBase B (Fin.removeNth i b)
  let Φ (z : Fin 1 → M) := Fin.insertNth i (z 0) (Fin.removeNth i b)
  have hfixed (q : Fin n) : Fin.removeNth i b q ∈ E.real := Or.inr (Set.mem_range_self q)
  have hΦ : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ E.real Φ := by
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    intro j
    refine i.succAboveCases ?_ (fun q => ?_) j
    · simpa only [Φ,Fin.insertNth_apply_same] using (Set.DefinableFun.proj LRV (i := (0 : Fin 1)))
    · simpa only [Φ,Fin.insertNth_apply_succAbove] using LRV.definableFun_const (Fin 1) (hfixed q)
  have hC' := hC.mono (E := E) Set.subset_union_left (Set.Subset.refl _)
  convert hC'.preimage_real_map (fun _ : Fin 1 => .vf) Φ hΦ using 1
  ext z
  constructor
  · intro hz
    refine ⟨hz,fun j => ?_⟩
    fin_cases j
    change sortEval SortTag.vf (z 0)
    simpa only [Φ,Fin.insertNth_apply_same] using hC'.proper hz i
  · exact And.left

theorem coordinate_line_atomic_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (B : ParameterBase M) {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin (n+1) → Set M)
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (b : Fin (n+1) → M) (hb : ∀ j, b j ∈ D j) (i : Fin (n+1)) :
    IsAtomicOverFiniteDiscNames (tupleBase B (Fin.removeNth i b)) ground d τ
      (fun _ : Fin 1 => .vf) {z | z 0 ∈ D i} := by
  have hdef := coordinate_section_definable_disc_names B ground d τ _ hA.1 b i
  have htype := hA.2.coordinate_fibre hc b hb i
  have he : {z : Fin 1 → M | ∀ j, Fin.insertNth i (z 0) (Fin.removeNth i b) j ∈ D j} = {z | z 0 ∈ D i} := by
    ext z
    constructor
    · intro hz
      change z 0 ∈ D i
      simpa only [Fin.insertNth_apply_same] using hz i
    · intro hz j
      change z 0 ∈ D i at hz
      refine i.succAboveCases ?_ (fun q => ?_) j
      · simpa only [Fin.insertNth_apply_same] using hz
      · simpa only [Fin.insertNth_apply_succAbove,Fin.removeNth] using hb (i.succAbove q)
  have he' : {z : Fin 1 → M | Fin.insertNth i (z 0) (Fin.removeNth i b) ∈ {a | ∀ j, a j ∈ D j}} =
      {z | z 0 ∈ D i} := he
  rw [he'] at hdef htype
  exact ⟨hdef,htype⟩

theorem coordinate_line_graph_definable_disc_names (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin (n+1) → Set M) (f : (Fin (n+1) → M) → M)
    (hG : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+2) => .vf)
      (vfFunctionGraph {a | ∀ j, a j ∈ D j} f))
    (b : Fin (n+1) → M) (hb : ∀ j, b j ∈ D j) (i : Fin (n+1)) :
    DefinableOverFiniteDiscNames (tupleBase B (Fin.removeNth i b)) ground d τ (fun _ : Fin 2 => .vf)
      (scalarVFGraph (D i) (fun x => f (Function.update b i x))) := by
  let E := tupleBase B (Fin.removeNth i b)
  let Φ (z : Fin 2 → M) : Fin (n+2) → M := Fin.snoc (Fin.insertNth i (z 0) (Fin.removeNth i b)) (z 1)
  have hfixed (q : Fin n) : Fin.removeNth i b q ∈ E.real := Or.inr (Set.mem_range_self q)
  have hΦ : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ E.real Φ := by
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    intro j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · simpa only [Φ,Fin.snoc_last] using (Set.DefinableFun.proj LRV (i := (1 : Fin 2)))
    · refine i.succAboveCases ?_ (fun q => ?_) q
      · simpa only [Φ,Fin.snoc_castSucc,Fin.insertNth_apply_same] using (Set.DefinableFun.proj LRV (i := (0 : Fin 2)))
      · simpa only [Φ,Fin.snoc_castSucc,Fin.insertNth_apply_succAbove] using LRV.definableFun_const (Fin 2) (hfixed q)
  have hG' := hG.mono (E := E) Set.subset_union_left (Set.Subset.refl _)
  have hrow (z : Fin 2 → M) : Φ z ∈ vfFunctionGraph {a | ∀ j, a j ∈ D j} f ↔
      z 0 ∈ D i ∧ z 1 = f (Function.update b i (z 0)) := by
    simp only [vfFunctionGraph,Φ,Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last,Fin.insertNth_removeNth]
    constructor
    · rintro ⟨hD,hf⟩
      exact ⟨by simpa only [Function.update_self] using hD i,hf.symm⟩
    · rintro ⟨hz,hf⟩
      refine ⟨fun j => ?_,hf.symm⟩
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using hz
      · simpa only [Function.update_of_ne hj] using hb j
  convert hG'.preimage_real_map (fun _ : Fin 2 => .vf) Φ hΦ using 1
  ext z
  change (_ ∧ _) ↔ (Φ z ∈ vfFunctionGraph {a | ∀ j, a j ∈ D j} f ∧ z ∈ GammaParameters.sortedUniverse _)
  constructor
  · intro hz
    have hg := (hrow z).mpr hz
    refine ⟨hg,fun j => ?_⟩
    fin_cases j
    · change sortEval SortTag.vf (z 0)
      simpa only [Φ,Fin.snoc_castSucc,Fin.insertNth_apply_same] using hG'.proper hg i.castSucc
    · change sortEval SortTag.vf (z 1)
      simpa only [Φ,Fin.snoc_last] using hG'.proper hg (Fin.last (n+1))
  · intro hz
    exact (hrow z).mp hz.1

end DiamondIntegral.Section2
