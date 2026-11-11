import «section 2».DiscTupleLogic
import «section 2».GammaRelationMaps

/-! Definable substitutions in real output coordinates preserve the
entire fixed DC tuple and its global presentation invariance. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def FiniteDiscTupleRelation.preimageRealMap {B : ParameterBase M} {k n m : ℕ}
    {closed : Fin k → Bool} {sn : Fin n → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (sm : Fin m → SortTag)
    (f : (Fin m → M) → Fin n → M)
    (hf : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ B.real f) :
    FiniteDiscTupleRelation B closed sm where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := gammaRelationPreimageMap R.relation (Fin.append (fun _ : Fin k => .vf) sm)
    (fun z => Fin.append (z ∘ Fin.castAdd m) (f (z ∘ Fin.natAdd k))) (by
      let N := CanonicalStructure.normalize (M := M)
      letI := N
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [Fin.append_left,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Fin.castAdd m i : Fin (k+m))))
      · simpa only [Fin.append_right,Function.comp_def] using (hf i).comp
          (fun q => Set.DefinableFun.proj LRV (i := (Fin.natAdd k q : Fin (k+m)))))
  invariant := by
    intro a a' δ δ' he x
    have hmap (b : Fin k → VF M) :
        Fin.append (Fin.append (vfValues b) x ∘ Fin.castAdd m)
          (f (Fin.append (vfValues b) x ∘ Fin.natAdd k)) = Fin.append (vfValues b) (f x) := by
      congr 1
      · funext j
        simp only [Function.comp_apply,Fin.append_left]
      · congr 1
        funext j
        simp only [Function.comp_apply,Fin.append_right]
    have hsort (b : Fin k → VF M) :
        Fin.append (vfValues b) x ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sm) ↔
          x ∈ GammaParameters.sortedUniverse sm := by
      constructor
      · intro h j
        simpa only [Fin.append_right] using h (Fin.natAdd k j)
      · intro h j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa only [Fin.append_left,vfValues,sortEval,iVF] using (b i).property
        · simpa only [Fin.append_right] using h i
    change (Fin.append (Fin.append (vfValues a) x ∘ Fin.castAdd m)
        (f (Fin.append (vfValues a) x ∘ Fin.natAdd k)) ∈ R.relation.fibre (Fin.append R.support δ) ∧
      Fin.append (vfValues a) x ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sm)) ↔
      (Fin.append (Fin.append (vfValues a') x ∘ Fin.castAdd m)
        (f (Fin.append (vfValues a') x ∘ Fin.natAdd k)) ∈ R.relation.fibre (Fin.append R.support δ') ∧
      Fin.append (vfValues a') x ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sm))
    rw [hmap a,hmap a',hsort a,hsort a']
    exact and_congr (R.invariant a a' δ δ' he (f x)) Iff.rfl

theorem FiniteDiscTupleRelation.preimageRealMap_fibre {B : ParameterBase M} {k n m : ℕ}
    {closed : Fin k → Bool} {sn : Fin n → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (sm : Fin m → SortTag)
    (f : (Fin m → M) → Fin n → M)
    (hf : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ B.real f)
    (a : Fin k → VF M) (δ : Fin k → Gamma M) :
    (R.preimageRealMap sm f hf).fibre a δ = {x | f x ∈ R.fibre a δ ∧ x ∈ GammaParameters.sortedUniverse sm} := by
  ext x
  change (Fin.append (Fin.append (vfValues a) x ∘ Fin.castAdd m)
      (f (Fin.append (vfValues a) x ∘ Fin.natAdd k)) ∈ R.relation.fibre (Fin.append R.support δ) ∧
      Fin.append (vfValues a) x ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sm)) ↔
    (f x ∈ R.fibre a δ ∧ x ∈ GammaParameters.sortedUniverse sm)
  have hleft : Fin.append (vfValues a) x ∘ Fin.castAdd m = vfValues a := by funext j; exact Fin.append_left _ _ j
  have hright : Fin.append (vfValues a) x ∘ Fin.natAdd k = x := by funext j; exact Fin.append_right _ _ j
  rw [hleft,hright]
  apply and_congr Iff.rfl
  constructor
  · intro h j
    simpa only [Fin.append_right] using h (Fin.natAdd k j)
  · intro h j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,vfValues,sortEval,iVF] using (a i).property
    · simpa only [Fin.append_right] using h i

theorem DefinableOverFiniteDiscNames.preimage_real_map {B : ParameterBase M} {k n m : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ sn A) (sm : Fin m → SortTag)
    (f : (Fin m → M) → Fin n → M)
    (hf : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ B.real f) :
    DefinableOverFiniteDiscNames B closed a δ sm {x | f x ∈ A ∧ x ∈ GammaParameters.sortedUniverse sm} := by
  obtain ⟨R,rfl⟩ := hA
  exact ⟨R.preimageRealMap sm f hf,R.preimageRealMap_fibre sm f hf a δ⟩

end DiamondIntegral.Section2
