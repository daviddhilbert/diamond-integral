import «section 2».PrefixedDiscCoordinates

/-! A coordinate-line relation with an untouched prefix of ground DC
names. Neither those centres nor the varying new centre is a real name. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def prefixedCoordinateRelation {B : ParameterBase M} {k n : ℕ}
    {ground : Fin k → Bool} {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B (Fin.append ground closed) (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) :
    GammaParameters.Relation (coordinateDiscBase B b δ i).real ((R.supportArity+n)+(k+1))
      ((k+1)+1) (Fin.append (fun _ : Fin (k+1) => .vf) (fun _ : Fin 1 => .vf)) :=
  gammaRelationPreimageMap
    ((R.relation.monoReal Set.subset_union_left).precomposeGamma (prefixedCoordinateGammaIndex R.supportArity k i))
    _ (prefixedCoordinateRealMap b i) (prefixedCoordinateRealMap_definable B b δ i)

theorem prefixedCoordinateRelation_mem {B : ParameterBase M} {k n : ℕ}
    {ground : Fin k → Bool} {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B (Fin.append ground closed) (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1))
    (a : Fin k → VF M) (c : VF M) (τ : Fin k → Gamma M) (γ : Gamma M) (x : Fin 1 → M) :
    Fin.append (vfValues (Fin.snoc a c)) x ∈ (prefixedCoordinateRelation R b δ i).fibre
        (Fin.append (Fin.append R.support (Fin.removeNth i δ)) (Fin.snoc τ γ)) ↔
      Fin.append (vfValues (Fin.append a (Fin.insertNth i c (Fin.removeNth i b))))
        (Fin.insertNth i (x 0) (Fin.removeNth i (vfValues b))) ∈
        R.relation.fibre (Fin.append R.support (Fin.append τ (Fin.insertNth i γ (Fin.removeNth i δ)))) := by
  change (_ ∈ ((R.relation.monoReal _).precomposeGamma _).fibre _ ∧
    _ ∈ GammaParameters.sortedUniverse _) ↔ _
  rw [gammaRelation_precompose_fibre,prefixedCoordinateGammaIndex_append,prefixedCoordinateRealMap_append]
  constructor
  · exact And.left
  · intro h
    have hx := R.relation.fibre_proper _ _ h (Fin.natAdd (k+(n+1)) i)
    have hx0 : iVF (x 0) := by
      simpa only [Fin.append_right,Fin.insertNth_apply_same,sortEval,iVF] using hx
    refine ⟨h,fun j => ?_⟩
    refine Fin.addCases (fun q => ?_) (fun q => ?_) j
    · simp only [Fin.append_left,vfValues,sortEval,iVF]
      exact ((Fin.snoc a c : Fin (k+1) → VF M) q).property
    · fin_cases q
      simp only [Fin.append_right,sortEval,iVF]
      exact hx0

theorem prefixedCoordinateRelation_mem_general {B : ParameterBase M} {k n : ℕ}
    {ground : Fin k → Bool} {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B (Fin.append ground closed) (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1))
    (a : Fin (k+1) → VF M) (τ : Fin (k+1) → Gamma M) (x : Fin 1 → M) :
    Fin.append (vfValues a) x ∈ (prefixedCoordinateRelation R b δ i).fibre
        (Fin.append (Fin.append R.support (Fin.removeNth i δ)) τ) ↔
      Fin.append (vfValues (Fin.append (Fin.init a) (Fin.insertNth i (a (Fin.last k)) (Fin.removeNth i b))))
        (Fin.insertNth i (x 0) (Fin.removeNth i (vfValues b))) ∈ R.relation.fibre
        (Fin.append R.support (Fin.append (Fin.init τ) (Fin.insertNth i (τ (Fin.last k)) (Fin.removeNth i δ)))) := by
  simpa only [Fin.snoc_init_self] using prefixedCoordinateRelation_mem R b δ i
    (Fin.init a) (a (Fin.last k)) (Fin.init τ) (τ (Fin.last k)) x

def FiniteDiscTupleRelation.prefixedCoordinateLine {B : ParameterBase M} {k n : ℕ}
    {ground : Fin k → Bool} {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B (Fin.append ground closed) (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) :
    FiniteDiscTupleRelation (coordinateDiscBase B b δ i) (Fin.snoc ground (closed i)) (fun _ : Fin 1 => .vf) where
  supportArity := R.supportArity+n
  support := Fin.append R.support (Fin.removeNth i δ)
  support_mem := by
    intro j
    refine Fin.addCases (fun q => ?_) (fun q => ?_) j
    · simpa only [Fin.append_left,coordinateDiscBase,Set.mem_union] using
        (Or.inl (R.support_mem q) : R.support q ∈ B.gamma ∪ Set.range (Fin.removeNth i δ))
    · simpa only [Fin.append_right,coordinateDiscBase,Set.mem_union] using
        (Or.inr (Set.mem_range_self q) : Fin.removeNth i δ q ∈ B.gamma ∪ Set.range (Fin.removeNth i δ))
  relation := prefixedCoordinateRelation R b δ i
  invariant := by
    intro a a' τ τ' he x
    rw [prefixedCoordinateRelation_mem_general,prefixedCoordinateRelation_mem_general]
    have heFull : finitePolydiscNames (Fin.append ground closed)
        (Fin.append (Fin.init a) (Fin.insertNth i (a (Fin.last k)) (Fin.removeNth i b)))
        (Fin.append (Fin.init τ) (Fin.insertNth i (τ (Fin.last k)) (Fin.removeNth i δ))) =
      finitePolydiscNames (Fin.append ground closed)
        (Fin.append (Fin.init a') (Fin.insertNth i (a' (Fin.last k)) (Fin.removeNth i b)))
        (Fin.append (Fin.init τ') (Fin.insertNth i (τ' (Fin.last k)) (Fin.removeNth i δ))) := by
      funext j
      refine Fin.addCases (fun q => ?_) (fun q => ?_) j
      · have h := congrFun he q.castSucc
        simpa only [finitePolydiscNames,Fin.append_left,Fin.snoc_castSucc,Fin.init] using h
      · refine i.succAboveCases ?_ (fun q => ?_) q
        · have h := congrFun he (Fin.last k)
          simpa only [finitePolydiscNames,Fin.append_right,Fin.snoc_last,Fin.insertNth_apply_same] using h
        · simp only [finitePolydiscNames,Fin.append_right,Fin.insertNth_apply_succAbove]
    exact R.invariant _ _ _ _ heFull _

theorem FiniteDiscTupleRelation.prefixedCoordinateLine_fibre {B : ParameterBase M} {k n : ℕ}
    {ground : Fin k → Bool} {closed : Fin (n+1) → Bool}
    (R : FiniteDiscTupleRelation B (Fin.append ground closed) (fun _ : Fin (n+1) => .vf))
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1))
    (a : Fin k → VF M) (τ : Fin k → Gamma M) :
    (R.prefixedCoordinateLine b δ i).fibre (Fin.snoc a (b i)) (Fin.snoc τ (δ i)) =
      {x : Fin 1 → M | Function.update (vfValues b) i (x 0) ∈
        R.fibre (Fin.append a b) (Fin.append τ δ)} := by
  ext x
  change Fin.append (vfValues (Fin.snoc a (b i))) x ∈ (prefixedCoordinateRelation R b δ i).fibre
    (Fin.append (Fin.append R.support (Fin.removeNth i δ)) (Fin.snoc τ (δ i))) ↔ _
  rw [prefixedCoordinateRelation_mem]
  simp only [Fin.insertNth_self_removeNth,Fin.insertNth_removeNth]
  rfl

end DiamondIntegral.Section2
