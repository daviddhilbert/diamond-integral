import «section 2».DiscTupleNames
import «section 2».GammaRelationMaps

/-!
# A coordinate line with the other discs represented explicitly

The fixed other VF points and their actual Gamma radii are named. Only
the disc in the varying coordinate remains an imaginary parameter; none
of its centres is added to the base.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def coordinateDiscBase (B : ParameterBase M) {n : ℕ} (b : Fin (n+1) → VF M)
    (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) : ParameterBase M :=
  ⟨B.real ∪ Set.range (Fin.removeNth i (SpecialTransformations.Section4.vfValues b)),
    B.gamma ∪ Set.range (Fin.removeNth i δ)⟩

private def coordinateGammaIndex (k : ℕ) {n : ℕ} (i : Fin (n+1)) :
    Fin (k+(n+1)) → Fin ((k+n)+1) :=
  Fin.addCases (fun j => (Fin.castAdd n j).castSucc)
    (Fin.insertNth i (Fin.last (k+n)) (fun j => (Fin.natAdd k j).castSucc))

private theorem coordinateGammaIndex_append {k n : ℕ} (i : Fin (n+1))
    (γ : Fin k → Gamma M) (δ : Fin n → Gamma M) (η : Fin 1 → Gamma M) :
    Fin.append (Fin.append γ δ) η ∘ coordinateGammaIndex k i =
      Fin.append γ (Fin.insertNth i (η 0) δ) := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · simp only [Function.comp_apply, coordinateGammaIndex, Fin.addCases_left,
      Fin.append_right_eq_snoc, Fin.snoc_castSucc, Fin.append_left]
  · refine i.succAboveCases ?_ (fun q => ?_) q
    · simp only [Function.comp_apply, coordinateGammaIndex, Fin.addCases_right,
        Fin.insertNth_apply_same, Fin.append_right_eq_snoc, Fin.snoc_last, Fin.append_right]
    · simp only [Function.comp_apply, coordinateGammaIndex, Fin.addCases_right,
        Fin.insertNth_apply_succAbove, Fin.append_right_eq_snoc, Fin.snoc_castSucc, Fin.append_right]

private def coordinateRealMap {n : ℕ} (b : Fin (n+1) → VF M) (i : Fin (n+1))
    (z : Fin (1+1) → M) : Fin ((n+1)+(n+1)) → M :=
  Fin.append
    (Fin.insertNth i (z 0) (Fin.removeNth i (SpecialTransformations.Section4.vfValues b)))
    (Fin.insertNth i (z 1) (Fin.removeNth i (SpecialTransformations.Section4.vfValues b)))

omit hM in
private theorem insert_coordinate_definable (T : Set M) {n : ℕ} (v : Fin n → M)
    (hv : ∀ q, v q ∈ T) (i : Fin (n+1)) (j : Fin 2) :
    T.DefinableMap LRV (fun z : Fin 2 → M => Fin.insertNth i (z j) v) := by
  intro q
  refine i.succAboveCases ?_ (fun q => ?_) q
  · simpa only [Fin.insertNth_apply_same] using (Set.DefinableFun.proj LRV (i := j))
  · simpa only [Fin.insertNth_apply_succAbove] using (LRV.definableFun_const (Fin 2) (hv q))

private theorem coordinateRealMap_definable (B : ParameterBase M) {n : ℕ}
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _
      (coordinateDiscBase B b δ i).real (coordinateRealMap b i) := by
  let S : Set M := (coordinateDiscBase B b δ i).real
  let v : Fin n → M := Fin.removeNth i (SpecialTransformations.Section4.vfValues b)
  have hv (q : Fin n) : v q ∈ S := Or.inr (Set.mem_range_self q)
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hleft := @insert_coordinate_definable M N S n v hv i 0
  have hright := @insert_coordinate_definable M N S n v hv i 1
  intro j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · simpa only [coordinateRealMap, Fin.append_left] using hleft q
  · simpa only [coordinateRealMap, Fin.append_right] using hright q

private theorem coordinateRealMap_append {n : ℕ} (b : Fin (n+1) → VF M) (i : Fin (n+1))
    (c : Fin 1 → VF M) (x : Fin 1 → M) :
    coordinateRealMap b i (Fin.append (SpecialTransformations.Section4.vfValues c) x) =
      Fin.append
        (SpecialTransformations.Section4.vfValues (Fin.insertNth i (c 0) (Fin.removeNth i b)))
        (Fin.insertNth i (x 0) (Fin.removeNth i (SpecialTransformations.Section4.vfValues b))) := by
  unfold coordinateRealMap
  change Fin.append (Fin.insertNth i (c 0).val _) (Fin.insertNth i (x 0) _) = _
  congr 1
  funext j
  refine i.succAboveCases ?_ (fun q => ?_) j
  · simp only [SpecialTransformations.Section4.vfValues, Fin.insertNth_apply_same]
  · simp only [SpecialTransformations.Section4.vfValues, Fin.insertNth_apply_succAbove,
      Fin.removeNth]

private def coordinateDiscRelation {B : ParameterBase M} {n : ℕ}
    {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B closed (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) :
    GammaParameters.Relation (coordinateDiscBase B b δ i).real ((R.supportArity+n)+1)
      (1+1) (Fin.append (fun _ : Fin 1 => .vf) (fun _ : Fin 1 => .vf)) :=
  gammaRelationPreimageMap
    ((R.relation.monoReal Set.subset_union_left).precomposeGamma (coordinateGammaIndex R.supportArity i))
    _ (coordinateRealMap b i) (coordinateRealMap_definable B b δ i)

private theorem coordinateDiscRelation_mem {B : ParameterBase M} {n : ℕ}
    {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B closed (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1))
    (c : Fin 1 → VF M) (γ : Fin 1 → Gamma M) (x : Fin 1 → M) :
    Fin.append (SpecialTransformations.Section4.vfValues c) x ∈
        (coordinateDiscRelation R b δ i).fibre
          (Fin.append (Fin.append R.support (Fin.removeNth i δ)) γ) ↔
      Fin.append
          (SpecialTransformations.Section4.vfValues (Fin.insertNth i (c 0) (Fin.removeNth i b)))
          (Fin.insertNth i (x 0) (Fin.removeNth i (SpecialTransformations.Section4.vfValues b))) ∈
        R.relation.fibre (Fin.append R.support (Fin.insertNth i (γ 0) (Fin.removeNth i δ))) := by
  change (_ ∈ ((R.relation.monoReal _).precomposeGamma _).fibre _ ∧
    _ ∈ GammaParameters.sortedUniverse _) ↔ _
  rw [gammaRelation_precompose_fibre, coordinateGammaIndex_append, coordinateRealMap_append]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    have hx := R.relation.fibre_proper _ _ h (Fin.natAdd (n+1) i)
    have hx0 : iVF (x 0) := by
      simpa only [Fin.append_right, Fin.insertNth_apply_same, sortEval, iVF] using hx
    intro j
    refine Fin.addCases (fun q => ?_) (fun q => ?_) j
    · simpa only [Fin.append_left, SpecialTransformations.Section4.vfValues, sortEval, iVF]
        using (c q).property
    · fin_cases q
      change sortEval SortTag.vf (x 0)
      exact hx0

/-- The varying coordinate is represented by its actual disc name.
The base contains only the other VF coordinates and their radii. -/
def FiniteDiscTupleRelation.coordinateLine {B : ParameterBase M} {n : ℕ}
    {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B closed (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) :
    FiniteDiscTupleRelation (coordinateDiscBase B b δ i) (![closed i]) (fun _ : Fin 1 => .vf) where
  supportArity := R.supportArity+n
  support := Fin.append R.support (Fin.removeNth i δ)
  support_mem := by
    intro j
    refine Fin.addCases (fun q => ?_) (fun q => ?_) j
    · simpa only [Fin.append_left, coordinateDiscBase, Set.mem_union] using (Or.inl (R.support_mem q) :
        R.support q ∈ B.gamma ∪ Set.range (Fin.removeNth i δ))
    · simpa only [Fin.append_right, coordinateDiscBase, Set.mem_union] using (Or.inr (Set.mem_range_self q) :
        Fin.removeNth i δ q ∈ B.gamma ∪ Set.range (Fin.removeNth i δ))
  relation := coordinateDiscRelation R b δ i
  invariant := by
    intro c c' γ γ' he x
    rw [coordinateDiscRelation_mem, coordinateDiscRelation_mem]
    have heFull : finitePolydiscNames closed
        (Fin.insertNth i (c 0) (Fin.removeNth i b)) (Fin.insertNth i (γ 0) (Fin.removeNth i δ)) =
        finitePolydiscNames closed (Fin.insertNth i (c' 0) (Fin.removeNth i b))
          (Fin.insertNth i (γ' 0) (Fin.removeNth i δ)) := by
      funext j
      refine i.succAboveCases ?_ (fun q => ?_) j
      · have h := congrFun he 0
        simpa only [finitePolydiscNames, Matrix.cons_val_zero, Fin.insertNth_apply_same] using h
      · simp only [finitePolydiscNames, Fin.insertNth_apply_succAbove]
    exact R.invariant _ _ _ _ heFull _

theorem FiniteDiscTupleRelation.coordinateLine_fibre {B : ParameterBase M} {n : ℕ}
    {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B closed (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) :
    (R.coordinateLine b δ i).fibre (![b i]) (![δ i]) =
      {x : Fin 1 → M | Function.update (SpecialTransformations.Section4.vfValues b) i (x 0) ∈
        R.fibre b δ} := by
  ext x
  change Fin.append (SpecialTransformations.Section4.vfValues (![b i])) x ∈
    (coordinateDiscRelation R b δ i).fibre
      (Fin.append (Fin.append R.support (Fin.removeNth i δ)) (![δ i])) ↔ _
  rw [coordinateDiscRelation_mem]
  simp only [Matrix.cons_val_zero, Fin.insertNth_self_removeNth, Fin.insertNth_removeNth]
  rfl

end DiamondIntegral.Section2
