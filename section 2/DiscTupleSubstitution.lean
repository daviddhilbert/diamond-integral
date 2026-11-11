import «section 2».DiscTupleNames
import «section 2».GammaRelationMaps

/-!
# Substituting named real coordinates in disc-parameter formulas

The actual DC names and all Gamma-code invariance are retained. Only real
constants already belonging to the stated ground base are substituted.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private def middleConstantsMap {n p m : ℕ} (u : Fin p → M) (z : Fin (n+m) → M) :
    Fin (n+(p+m)) → M :=
  Fin.append (z ∘ Fin.castAdd m) (Fin.append u (z ∘ Fin.natAdd n))

omit hM in
private theorem middleConstantsMap_definable (T : Set M) {n p m : ℕ} (u : Fin p → M)
    (hu : ∀ i, u i ∈ T) : T.DefinableMap LRV (middleConstantsMap (n := n) (m := m) u) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [middleConstantsMap, Fin.append_left, Function.comp_apply] using
      (Set.DefinableFun.proj LRV (i := Fin.castAdd m i))
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [middleConstantsMap, Fin.append_right, Fin.append_left] using
        LRV.definableFun_const (Fin (n+m)) (hu i)
    · simpa only [middleConstantsMap, Fin.append_right, Function.comp_apply] using
        (Set.DefinableFun.proj LRV (i := Fin.natAdd n i))

private theorem middleConstantsMap_append {n p m : ℕ} (u : Fin p → M)
    (a : Fin n → VF M) (x : Fin m → M) :
    middleConstantsMap u (Fin.append (SpecialTransformations.Section4.vfValues a) x) =
      Fin.append (SpecialTransformations.Section4.vfValues a) (Fin.append u x) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [middleConstantsMap, Fin.append_left, Function.comp_apply]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [middleConstantsMap, Fin.append_left, Fin.append_right]
    · simp only [middleConstantsMap, Fin.append_right, Function.comp_apply]

private theorem append_vf_sorted {n m : ℕ} (a : Fin n → VF M)
    (sn : Fin m → SortTag) (x : Fin m → M) :
    Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
      GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sn) ↔
      x ∈ GammaParameters.sortedUniverse sn := by
  constructor
  · intro h j
    simpa only [Fin.append_right] using h (Fin.natAdd n j)
  · intro h j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [Fin.append_left, SpecialTransformations.Section4.vfValues, sortEval, iVF]
        using (a k).property
    · simpa only [Fin.append_right] using h k

def FiniteDiscTupleRelation.fixPrefix {B : ParameterBase M} {n p m : ℕ}
    {closed : Fin n → Bool} {sp : Fin p → SortTag} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed (Fin.append sp sn)) (u : Fin p → M)
    (hu : ∀ i, u i ∈ B.real) : FiniteDiscTupleRelation B closed sn where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := gammaRelationPreimageMap R.relation (Fin.append (fun _ : Fin n => .vf) sn)
    (middleConstantsMap u)
    (@middleConstantsMap_definable M (CanonicalStructure.normalize (M := M)) B.real n p m u hu)
  invariant := by
    intro a a' δ δ' he x
    change (_ ∈ R.relation.fibre (Fin.append R.support δ) ∧ _ ∈ GammaParameters.sortedUniverse _) ↔
      (_ ∈ R.relation.fibre (Fin.append R.support δ') ∧ _ ∈ GammaParameters.sortedUniverse _)
    rw [middleConstantsMap_append, middleConstantsMap_append, append_vf_sorted, append_vf_sorted]
    exact and_congr (R.invariant a a' δ δ' he (Fin.append u x)) Iff.rfl

theorem FiniteDiscTupleRelation.fixPrefix_fibre {B : ParameterBase M} {n p m : ℕ}
    {closed : Fin n → Bool} {sp : Fin p → SortTag} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed (Fin.append sp sn)) (u : Fin p → M)
    (hu : ∀ i, u i ∈ B.real) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    (R.fixPrefix u hu).fibre a δ = {x : Fin m → M | Fin.append u x ∈ R.fibre a δ} := by
  ext x
  change (_ ∈ R.relation.fibre (Fin.append R.support δ) ∧ _ ∈ GammaParameters.sortedUniverse _) ↔ _
  rw [middleConstantsMap_append, append_vf_sorted]
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx, fun i => ?_⟩
    simpa only [Fin.append_right] using R.fibre_proper a δ hx (Fin.natAdd p i)

theorem DefinableOverFiniteDiscNames.fix_prefix {B : ParameterBase M} {n p m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sp : Fin p → SortTag} {sn : Fin m → SortTag} {A : Set (Fin (p+m) → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ (Fin.append sp sn) A)
    (u : Fin p → M) (hu : ∀ i, u i ∈ B.real) :
    DefinableOverFiniteDiscNames B closed a δ sn {x | Fin.append u x ∈ A} := by
  obtain ⟨R, rfl⟩ := hA
  exact ⟨R.fixPrefix u hu, R.fixPrefix_fibre u hu a δ⟩

end DiamondIntegral.Section2
