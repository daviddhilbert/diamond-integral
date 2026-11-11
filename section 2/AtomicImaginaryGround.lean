import «section 2».AtomicDiscGroundChange
import «section 2».PolydiscNormalForm

/-! Finite RV tuples and singleton closed-disc ground names in 2.24.
Only points uniquely decoded from singleton names enter the real base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem lemma_2_24_disc_names_rv_tuple (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n m : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j})
    (t : Fin m → RVInfinity M) :
    IsAtomicOverFiniteDiscNames ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j} := by
  classical
  let E (s : Finset (Fin m)) : ParameterBase M :=
    ⟨B.real ∪ (fun j => (t j).val) '' (s : Set (Fin m)),B.gamma⟩
  have hE (s : Finset (Fin m)) :
      IsAtomicOverFiniteDiscNames (E s) closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j} := by
    induction s using Finset.induction_on with
    | empty => simpa only [E,Finset.coe_empty,Set.image_empty,Set.union_empty] using hA
    | @insert i s _hi ih =>
      have hΓE : NontrivialDefinableGamma (E s) := hΓ.mono Set.subset_union_left (Set.Subset.refl _)
      have h := lemma_2_24_disc_names hc h00 (E s) hΓE cited closed a δ D hopen ih (t i)
      simpa only [E,adjoinRV,Finset.coe_insert,Set.image_insert_eq,Set.union_insert] using h
  simpa only [E,Finset.coe_univ,Set.image_univ] using hE Finset.univ

theorem lemma_2_24_disc_normal_form (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {p k n : ℕ} (points : Fin p → VF M) (closed : Fin k → Bool)
    (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverDiscNamesNormalForm B points closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j})
    (t : RVInfinity M) :
    IsAtomicOverDiscNamesNormalForm (adjoinRV B t) points closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j} := by
  unfold IsAtomicOverDiscNamesNormalForm at hA ⊢
  rw [tupleBase_adjoinRV]
  exact lemma_2_24_disc_names hc h00 (tupleBase B (SpecialTransformations.Section4.vfValues points))
    (hΓ.mono Set.subset_union_left (Set.Subset.refl _))
    cited closed a δ D hopen hA t

end DiamondIntegral.Section2
