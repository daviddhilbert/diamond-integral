import «section 2».DiscTupleIntersection

/-!
# Selecting and retaining actual disc names

A formula using selected disc coordinates is a formula over the entire
disc tuple. Extra names add no chosen centres or radius representatives.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private def gammaSelection (k : ℕ) {n l : ℕ} (π : Fin l → Fin n) :
    Fin (k+l) → Fin (k+n) :=
  Fin.addCases (Fin.castAdd n) (fun j => Fin.natAdd k (π j))

private theorem gammaSelection_append {k n l : ℕ} (π : Fin l → Fin n)
    (γ : Fin k → Gamma M) (δ : Fin n → Gamma M) :
    Fin.append γ δ ∘ gammaSelection k π = Fin.append γ (δ ∘ π) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, gammaSelection, Fin.addCases_left, Fin.append_left]
  · simp only [Function.comp_apply, gammaSelection, Fin.addCases_right, Fin.append_right]

private def realSelection (m : ℕ) {n l : ℕ} (π : Fin l → Fin n) :
    Fin (l+m) → Fin (n+m) :=
  Fin.addCases (fun j => Fin.castAdd m (π j)) (Fin.natAdd n)

private theorem realSelection_append {n l m : ℕ} (π : Fin l → Fin n)
    (a : Fin n → VF M) (x : Fin m → M) :
    Fin.append (SpecialTransformations.Section4.vfValues a) x ∘ realSelection m π =
      Fin.append (SpecialTransformations.Section4.vfValues (a ∘ π)) x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, realSelection, Fin.addCases_left, Fin.append_left,
      SpecialTransformations.Section4.vfValues]
  · simp only [Function.comp_apply, realSelection, Fin.addCases_right, Fin.append_right]

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

def FiniteDiscTupleRelation.pullbackDiscNames {B : ParameterBase M} {n l m : ℕ}
    (closed : Fin n → Bool) (π : Fin l → Fin n) {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B (closed ∘ π) sn) : FiniteDiscTupleRelation B closed sn where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := (R.relation.precomposeGamma (gammaSelection R.supportArity π)).interRealPreimage
    (Fin.append (fun _ : Fin n => .vf) sn)
    (GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sn))
    (GammaParameters.sortedUniverse_definable B.real _) (realSelection m π)
  invariant := by
    intro a a' δ δ' he x
    change (_ ∈ (R.relation.precomposeGamma _).fibre (Fin.append R.support δ) ∧
      _ ∈ GammaParameters.sortedUniverse _) ↔
      (_ ∈ (R.relation.precomposeGamma _).fibre (Fin.append R.support δ') ∧
        _ ∈ GammaParameters.sortedUniverse _)
    rw [gammaRelation_precompose_fibre, gammaRelation_precompose_fibre,
      gammaSelection_append, gammaSelection_append, realSelection_append,
      realSelection_append, append_vf_sorted, append_vf_sorted]
    exact and_congr (R.invariant _ _ _ _ (congrArg (fun D => D ∘ π) he) x) Iff.rfl

theorem FiniteDiscTupleRelation.pullbackDiscNames_fibre {B : ParameterBase M} {n l m : ℕ}
    (closed : Fin n → Bool) (π : Fin l → Fin n) {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B (closed ∘ π) sn) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    (R.pullbackDiscNames closed π).fibre a δ = R.fibre (a ∘ π) (δ ∘ π) := by
  ext x
  change (_ ∈ (R.relation.precomposeGamma _).fibre (Fin.append R.support δ) ∧
    _ ∈ GammaParameters.sortedUniverse _) ↔ _
  rw [gammaRelation_precompose_fibre, gammaSelection_append, realSelection_append, append_vf_sorted]
  exact ⟨fun h => h.1, fun h => ⟨h, R.fibre_proper _ _ h⟩⟩

theorem DefinableOverFiniteDiscNames.pullback_names {B : ParameterBase M} {n l m : ℕ}
    (closed : Fin n → Bool) (π : Fin l → Fin n) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    {sn : Fin m → SortTag} {A : Set (Fin m → M)}
    (hA : DefinableOverFiniteDiscNames B (closed ∘ π) (a ∘ π) (δ ∘ π) sn A) :
    DefinableOverFiniteDiscNames B closed a δ sn A := by
  obtain ⟨R, hR⟩ := hA
  exact ⟨R.pullbackDiscNames closed π, (R.pullbackDiscNames_fibre closed π a δ).trans hR⟩

end DiamondIntegral.Section2
