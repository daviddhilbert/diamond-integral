import «section 2».DiscTupleParameters

/-! Logical operations on the actual finite-disc parameter interface.
Every operation retains the full Gamma-code preimage and invariance under
changing all centre/radius presentations of the named discs. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

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

/-- Sorted complement is taken in the real output context, not in all M. -/
def FiniteDiscTupleRelation.compl {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) : FiniteDiscTupleRelation B closed sn where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := R.relation.compl
  invariant := by
    intro a a' δ δ' he x
    change (GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives
        (Fin.append R.support δ))) ∧
      Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
        GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sn) ∧
      Fin.append (SpecialTransformations.Section4.vfValues a) x ∉
        R.relation.fibre (Fin.append R.support δ)) ↔
      (GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives
        (Fin.append R.support δ'))) ∧
      Fin.append (SpecialTransformations.Section4.vfValues a') x ∈
        GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sn) ∧
      Fin.append (SpecialTransformations.Section4.vfValues a') x ∉
        R.relation.fibre (Fin.append R.support δ'))
    simp only [GammaParameters.rawTuple_proper, true_and, append_vf_sorted]
    exact and_congr Iff.rfl (not_congr (R.invariant a a' δ δ' he x))

theorem FiniteDiscTupleRelation.compl_fibre {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    R.compl.fibre a δ = GammaParameters.sortedUniverse sn \ R.fibre a δ := by
  ext x
  change (GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives
      (Fin.append R.support δ))) ∧
    Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
      GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sn) ∧
    Fin.append (SpecialTransformations.Section4.vfValues a) x ∉
      R.relation.fibre (Fin.append R.support δ)) ↔
    (x ∈ GammaParameters.sortedUniverse sn ∧ x ∉ R.fibre a δ)
  simp only [GammaParameters.rawTuple_proper, true_and, append_vf_sorted]
  rfl

theorem DefinableOverFiniteDiscNames.compl {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A : Set (Fin m → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ sn A) :
    DefinableOverFiniteDiscNames B closed a δ sn (GammaParameters.sortedUniverse sn \ A) := by
  obtain ⟨R, rfl⟩ := hA
  exact ⟨R.compl, R.compl_fibre a δ⟩

/-- Pull back real output coordinates while leaving every named DC
parameter intact. The new output context is guarded explicitly. -/
def FiniteDiscTupleRelation.preimageReal {B : ParameterBase M} {n m l : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (sm : Fin l → SortTag) (π : Fin m → Fin l) :
    FiniteDiscTupleRelation B closed sm where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := R.relation.interRealPreimage (Fin.append (fun _ : Fin n => .vf) sm)
    (GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sm))
    (GammaParameters.sortedUniverse_definable B.real _)
    (Fin.addCases (Fin.castAdd l) (fun j => Fin.natAdd n (π j)))
  invariant := by
    intro a a' δ δ' he x
    have hc (b : Fin n → VF M) :
        Fin.append (SpecialTransformations.Section4.vfValues b) x ∘
          Fin.addCases (Fin.castAdd l) (fun j => Fin.natAdd n (π j)) =
          Fin.append (SpecialTransformations.Section4.vfValues b) (x ∘ π) := by
      funext j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [Function.comp_apply, Fin.addCases_left, Fin.append_left]
      · simp only [Function.comp_apply, Fin.addCases_right, Fin.append_right]
    change (_ ∈ R.relation.fibre (Fin.append R.support δ) ∧
      Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
        GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sm)) ↔
      (_ ∈ R.relation.fibre (Fin.append R.support δ') ∧
      Fin.append (SpecialTransformations.Section4.vfValues a') x ∈
        GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sm))
    rw [hc a, hc a', append_vf_sorted, append_vf_sorted]
    exact and_congr (R.invariant a a' δ δ' he (x ∘ π)) Iff.rfl

theorem FiniteDiscTupleRelation.preimageReal_fibre {B : ParameterBase M} {n m l : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (sm : Fin l → SortTag) (π : Fin m → Fin l)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    (R.preimageReal sm π).fibre a δ =
      {x | x ∘ π ∈ R.fibre a δ ∧ x ∈ GammaParameters.sortedUniverse sm} := by
  ext x
  have hc : Fin.append (SpecialTransformations.Section4.vfValues a) x ∘
      Fin.addCases (Fin.castAdd l) (fun j => Fin.natAdd n (π j)) =
      Fin.append (SpecialTransformations.Section4.vfValues a) (x ∘ π) := by
    funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [Function.comp_apply, Fin.addCases_left, Fin.append_left]
    · simp only [Function.comp_apply, Fin.addCases_right, Fin.append_right]
  change (_ ∈ R.relation.fibre (Fin.append R.support δ) ∧
    Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
      GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sm)) ↔
      (x ∘ π ∈ R.fibre a δ ∧ x ∈ GammaParameters.sortedUniverse sm)
  rw [hc, append_vf_sorted]
  rfl

theorem DefinableOverFiniteDiscNames.preimage_real {B : ParameterBase M} {n m l : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A : Set (Fin m → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ sn A)
    (sm : Fin l → SortTag) (π : Fin m → Fin l) :
    DefinableOverFiniteDiscNames B closed a δ sm
      {x | x ∘ π ∈ A ∧ x ∈ GammaParameters.sortedUniverse sm} := by
  obtain ⟨R, rfl⟩ := hA
  exact ⟨R.preimageReal sm π, R.preimageReal_fibre sm π a δ⟩

/-- Enlarging real/Gamma parameters retains the same actual disc names. -/
def FiniteDiscTupleRelation.mono {B E : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (hr : B.real ⊆ E.real) (hg : B.gamma ⊆ E.gamma) :
    FiniteDiscTupleRelation E closed sn where
  supportArity := R.supportArity
  support := R.support
  support_mem := fun j => hg (R.support_mem j)
  relation := R.relation.monoReal hr
  invariant := R.invariant

theorem DefinableOverFiniteDiscNames.mono {B E : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A : Set (Fin m → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ sn A)
    (hr : B.real ⊆ E.real) (hg : B.gamma ⊆ E.gamma) :
    DefinableOverFiniteDiscNames E closed a δ sn A := by
  obtain ⟨R, hR⟩ := hA
  exact ⟨R.mono hr hg, hR⟩

end DiamondIntegral.Section2
