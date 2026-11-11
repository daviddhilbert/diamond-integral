import «section 2».DiscTupleLogic
import «section 2».Atomic

/-! Original-base formulas embed in the actual finite-disc parameter
context. The unused disc variables retain their proper Gamma-code guards;
no representative is added as a ground parameter. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem gamma_precompose_fibre {S : Set M} {k l m : ℕ}
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

omit hM in
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

/-- A formula over the original real/Gamma base remains a formula after
naming any finite tuple of finite-radius discs. The formula is globally
independent of their centres and radii, not just at a selected tuple. -/
theorem definableOverFiniteDiscNames_of_ground (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M))
    (hA : GammaParameters.DefinableOverBase B sn A) :
    DefinableOverFiniteDiscNames B closed a δ sn A := by
  obtain ⟨k, γ, hγ, Q, hQA⟩ := hA
  let Q' := Q.precomposeGamma (Fin.castAdd n)
  let sm := Fin.append (fun _ : Fin n => SortTag.vf) sn
  let Qr := Q'.interRealPreimage sm (GammaParameters.sortedUniverse sm)
    (GammaParameters.sortedUniverse_definable B.real sm) (Fin.natAdd n)
  have hQf (η : Fin n → Gamma M) : Q'.fibre (Fin.append γ η) = Q.fibre γ := by
    rw [gamma_precompose_fibre]
    congr 1
    funext j
    simp only [Function.comp_apply, Fin.append_left]
  have htail (b : Fin n → VF M) (x : Fin m → M) :
      Fin.append (SpecialTransformations.Section4.vfValues b) x ∘ Fin.natAdd n = x := by
    funext j
    simp only [Function.comp_apply, Fin.append_right]
  have hQr (b : Fin n → VF M) (η : Fin n → Gamma M) (x : Fin m → M) :
      Fin.append (SpecialTransformations.Section4.vfValues b) x ∈ Qr.fibre (Fin.append γ η) ↔
        x ∈ Q.fibre γ ∧ x ∈ GammaParameters.sortedUniverse sn := by
    change (_ ∈ Q'.fibre (Fin.append γ η) ∧
      Fin.append (SpecialTransformations.Section4.vfValues b) x ∈ GammaParameters.sortedUniverse sm) ↔ _
    rw [htail, hQf, append_vf_sorted]
  let R : FiniteDiscTupleRelation B closed sn := {
    supportArity := k
    support := γ
    support_mem := hγ
    relation := Qr
    invariant := by
      intro b b' η η' _he x
      exact (hQr b η x).trans (hQr b' η' x).symm }
  refine ⟨R, ?_⟩
  ext x
  change Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
    Qr.fibre (Fin.append γ δ) ↔ x ∈ A
  rw [hQr, hQA]
  exact and_iff_left_of_imp (fun hx => GammaParameters.DefinableOverBase.proper
    ⟨k, γ, hγ, Q, hQA⟩ x hx)

/-- Complete-type generation over the finite imaginary disc names. -/
def GeneratesTypeOverFiniteDiscNames (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  A.Nonempty ∧ A ⊆ GammaParameters.sortedUniverse sn ∧
    ∀ C, DefinableOverFiniteDiscNames B closed a δ sn C → A ⊆ C ∨ Disjoint A C

def IsAtomicOverFiniteDiscNames (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  DefinableOverFiniteDiscNames B closed a δ sn A ∧
    GeneratesTypeOverFiniteDiscNames B closed a δ sn A

/-- Forgetting the DC names keeps agreement on every original-base formula. -/
theorem GeneratesTypeOverFiniteDiscNames.ground {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A : Set (Fin m → M)}
    (hA : GeneratesTypeOverFiniteDiscNames B closed a δ sn A) :
    GeneratesCompleteType B sn A :=
  ⟨hA.1, hA.2.1, fun C hC => hA.2.2 C
    (definableOverFiniteDiscNames_of_ground B closed a δ sn C hC)⟩

/-- A nonempty subset of a complete-type-generating set still generates
that type over the same disc names. -/
theorem GeneratesTypeOverFiniteDiscNames.subset_nonempty {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A C : Set (Fin m → M)}
    (hA : GeneratesTypeOverFiniteDiscNames B closed a δ sn A)
    (hCA : C ⊆ A) (hne : C.Nonempty) :
    GeneratesTypeOverFiniteDiscNames B closed a δ sn C := by
  refine ⟨hne, hCA.trans hA.2.1, ?_⟩
  intro U hU
  rcases hA.2.2 U hU with h | h
  · exact Or.inl (hCA.trans h)
  · exact Or.inr (h.mono_left hCA)

/-- Type generation depends on actual DC names, with no choice of centre. -/
theorem generatesTypeOverFiniteDiscNames_iff_of_names (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (a a' : Fin n → VF M) (δ δ' : Fin n → Gamma M)
    (he : finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ')
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) :
    GeneratesTypeOverFiniteDiscNames B closed a δ sn A ↔
      GeneratesTypeOverFiniteDiscNames B closed a' δ' sn A := by
  constructor
  · rintro ⟨hne, hs, ht⟩
    exact ⟨hne, hs, fun C hC => ht C
      ((definableOverFiniteDiscNames_iff_of_names B closed a a' δ δ' he sn C).mpr hC)⟩
  · rintro ⟨hne, hs, ht⟩
    exact ⟨hne, hs, fun C hC => ht C
      ((definableOverFiniteDiscNames_iff_of_names B closed a a' δ δ' he sn C).mp hC)⟩

/-- Atomicity, as well as type generation, depends only on the DC names. -/
theorem isAtomicOverFiniteDiscNames_iff_of_names (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (a a' : Fin n → VF M) (δ δ' : Fin n → Gamma M)
    (he : finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ')
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) :
    IsAtomicOverFiniteDiscNames B closed a δ sn A ↔
      IsAtomicOverFiniteDiscNames B closed a' δ' sn A :=
  and_congr (definableOverFiniteDiscNames_iff_of_names B closed a a' δ δ' he sn A)
    (generatesTypeOverFiniteDiscNames_iff_of_names B closed a a' δ δ' he sn A)

/-- An infinite set generating a complete type over the DC names cannot
meet a finite ground-definable set. Ground definability of the first set
is not assumed or inferred. -/
theorem GeneratesTypeOverFiniteDiscNames.disjoint_ground_finite
    {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A C : Set (Fin m → M)}
    (hA : GeneratesTypeOverFiniteDiscNames B closed a δ sn A) (hinf : A.Infinite)
    (hC : GammaParameters.DefinableOverBase B sn C) (hfin : C.Finite) :
    Disjoint A C := by
  rcases hA.ground.2.2 C hC with h | h
  · exact (hinf (hfin.subset h)).elim
  · exact h

end DiamondIntegral.Section2
