import «section 2».DiscTupleProjection

/-!
# Boolean conjunction with actual disc names

Ground Gamma supports are combined before intersecting relations. Their
disc coordinates still range over every presentation of the same DC tuple.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gammaRelation_precompose_fibre {S : Set M} {k l m : ℕ}
    {sn : Fin m → SortTag} (Q : GammaParameters.Relation S k m sn)
    (π : Fin k → Fin l) (δ : Fin l → Gamma M) :
    (Q.precomposeGamma π).fibre δ = Q.fibre (δ ∘ π) := by
  ext x
  change (GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives δ)) ∧
    (GammaParameters.rawTuple (GammaParameters.representatives δ) ∘ π, x) ∈ Q.carrier) ↔
    x ∈ Q.fibre (δ ∘ π)
  rw [and_iff_right (GammaParameters.rawTuple_proper _)]
  have he : GammaParameters.values (GammaParameters.representatives δ ∘ π) = δ ∘ π := by
    funext j
    exact congrFun (GammaParameters.representatives_values δ) (π j)
  exact (Q.mem_fibre_iff (GammaParameters.representatives δ ∘ π) (δ ∘ π) he x).symm

private def supportLeft (k l n : ℕ) : Fin (k+n) → Fin ((k+l)+n) :=
  Fin.addCases (fun j => Fin.castAdd n (Fin.castAdd l j)) (Fin.natAdd (k+l))

private def supportRight (k l n : ℕ) : Fin (l+n) → Fin ((k+l)+n) :=
  Fin.addCases (fun j => Fin.castAdd n (Fin.natAdd k j)) (Fin.natAdd (k+l))

private theorem append_supportLeft {k l n : ℕ} (γ : Fin k → Gamma M)
    (η : Fin l → Gamma M) (δ : Fin n → Gamma M) :
    Fin.append (Fin.append γ η) δ ∘ supportLeft k l n = Fin.append γ δ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, supportLeft, Fin.addCases_left, Fin.append_left]
  · simp only [Function.comp_apply, supportLeft, Fin.addCases_right, Fin.append_right]

private theorem append_supportRight {k l n : ℕ} (γ : Fin k → Gamma M)
    (η : Fin l → Gamma M) (δ : Fin n → Gamma M) :
    Fin.append (Fin.append γ η) δ ∘ supportRight k l n = Fin.append η δ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, supportRight, Fin.addCases_left, Fin.append_left, Fin.append_right]
  · simp only [Function.comp_apply, supportRight, Fin.addCases_right, Fin.append_right]

def FiniteDiscTupleRelation.inter {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R T : FiniteDiscTupleRelation B closed sn) : FiniteDiscTupleRelation B closed sn where
  supportArity := R.supportArity + T.supportArity
  support := Fin.append R.support T.support
  support_mem := by
    intro i
    exact Fin.addCases (fun j => by simpa only [Fin.append_left] using R.support_mem j)
      (fun j => by simpa only [Fin.append_right] using T.support_mem j) i
  relation := (R.relation.precomposeGamma (supportLeft _ _ n)).inter
    (T.relation.precomposeGamma (supportRight _ _ n))
  invariant := by
    intro a a' δ δ' he x
    change (_ ∈ (R.relation.precomposeGamma _).fibre _ ∧
      _ ∈ (T.relation.precomposeGamma _).fibre _) ↔
      (_ ∈ (R.relation.precomposeGamma _).fibre _ ∧
        _ ∈ (T.relation.precomposeGamma _).fibre _)
    rw [gammaRelation_precompose_fibre, gammaRelation_precompose_fibre,
      gammaRelation_precompose_fibre, gammaRelation_precompose_fibre,
      append_supportLeft, append_supportLeft, append_supportRight, append_supportRight]
    exact and_congr (R.invariant a a' δ δ' he x) (T.invariant a a' δ δ' he x)

theorem FiniteDiscTupleRelation.inter_fibre {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R T : FiniteDiscTupleRelation B closed sn) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    (R.inter T).fibre a δ = R.fibre a δ ∩ T.fibre a δ := by
  ext x
  change (_ ∈ (R.relation.precomposeGamma _).fibre
      (Fin.append (Fin.append R.support T.support) δ) ∧
    _ ∈ (T.relation.precomposeGamma _).fibre
      (Fin.append (Fin.append R.support T.support) δ)) ↔ _
  rw [gammaRelation_precompose_fibre, gammaRelation_precompose_fibre,
    append_supportLeft, append_supportRight]
  rfl

theorem DefinableOverFiniteDiscNames.inter {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A C : Set (Fin m → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ sn A)
    (hC : DefinableOverFiniteDiscNames B closed a δ sn C) :
    DefinableOverFiniteDiscNames B closed a δ sn (A ∩ C) := by
  obtain ⟨R, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hC
  exact ⟨R.inter T, R.inter_fibre T a δ⟩

end DiamondIntegral.Section2
