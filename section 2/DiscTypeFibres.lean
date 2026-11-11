import «section 2».DiscTuplePromotion
import «section 2».DiscTupleSubstitution

/-! Complete types over existing finite disc names after projecting or
fixing real coordinates. Parameter promotion is proved by the invariant
presentation hull; the centres are never ground names. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem GeneratesTypeOverFiniteDiscNames.image_real {B : ParameterBase M} {k n m : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : GeneratesTypeOverFiniteDiscNames B closed a δ sn A) (π : Fin m → Fin n) :
    GeneratesTypeOverFiniteDiscNames B closed a δ (sn ∘ π) ((fun x => x ∘ π) '' A) := by
  refine ⟨hA.1.image _,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩ i
    exact hA.2.1 hy (π i)
  · intro C hC
    rcases hA.2.2 _ (hC.preimage_real sn π) with hsub | hdis
    · exact Or.inl (by rintro x ⟨y,hy,rfl⟩; exact (hsub hy).1)
    · exact Or.inr (Set.disjoint_left.mpr (by
        rintro x ⟨y,hy,rfl⟩ hx
        exact Set.disjoint_left.mp hdis hy ⟨hx,hA.2.1 hy⟩))

theorem IsAtomicOverFiniteDiscNames.image_real {B : ParameterBase M} {k n m : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : IsAtomicOverFiniteDiscNames B closed a δ sn A) (π : Fin m → Fin n) :
    IsAtomicOverFiniteDiscNames B closed a δ (sn ∘ π) ((fun x => x ∘ π) '' A) :=
  ⟨hA.1.image_real π,hA.2.image_real π⟩

theorem GeneratesTypeOverFiniteDiscNames.block_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) {B : ParameterBase M} {k p n : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    {sp : Fin p → SortTag} {sn : Fin n → SortTag} {A : Set (Fin (p+n) → M)}
    (hA : GeneratesTypeOverFiniteDiscNames B closed a δ (Fin.append sp sn) A)
    (u : Fin p → M) (hne : {x : Fin n → M | Fin.append u x ∈ A}.Nonempty) :
    GeneratesTypeOverFiniteDiscNames (tupleBase B u) closed a δ sn {x : Fin n → M | Fin.append u x ∈ A} := by
  have hu (i : Fin p) : sortEval (sp i) (u i) := by
    obtain ⟨x,hx⟩ := hne
    simpa only [Fin.append_left] using hA.2.1 hx (Fin.castAdd n i)
  refine ⟨hne,?_,?_⟩
  · intro x hx i
    simpa only [Fin.append_right] using hA.2.1 hx (Fin.natAdd p i)
  · intro C hC
    obtain ⟨P,hP,hrow⟩ := promote_tuple_definable_disc_names hc B closed a δ sp u hu sn C hC
    rcases hA.2.2 P hP with hsub | hdis
    · exact Or.inl (fun x hx => (hrow x).mp (hsub hx))
    · exact Or.inr (Set.disjoint_left.mpr (fun x hx hC => Set.disjoint_left.mp hdis hx ((hrow x).mpr hC)))

theorem IsAtomicOverFiniteDiscNames.block_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) {B : ParameterBase M} {k p n : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    {sp : Fin p → SortTag} {sn : Fin n → SortTag} {A : Set (Fin (p+n) → M)}
    (hA : IsAtomicOverFiniteDiscNames B closed a δ (Fin.append sp sn) A)
    (u : Fin p → M) (hne : {x : Fin n → M | Fin.append u x ∈ A}.Nonempty) :
    IsAtomicOverFiniteDiscNames (tupleBase B u) closed a δ sn {x : Fin n → M | Fin.append u x ∈ A} := by
  have hdef := (hA.1.mono (E := tupleBase B u) Set.subset_union_left (Set.Subset.refl _)).fix_prefix u
    (fun i => Or.inr (Set.mem_range_self i))
  exact ⟨hdef,hA.2.block_fibre hc u hne⟩

end DiamondIntegral.Section2
