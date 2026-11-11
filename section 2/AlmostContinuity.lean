import «section 2».RVUnionDimension
import Section8.GenericOutputBall

/-!
# Lemma 2.36: continuity off a closed lower-dimensional set

This is the result quoted in the manuscript from [17, Lemma 8.7], whose
checked proof is already available as `Section8.lemma_8_7_canonical`.
That theorem supplies the closed exceptional set
over the same real ground base. Its dimension bound is transported to the
manuscript's direct interior dimension by the actual open-polydisc criterion.
Zero source arity is included using the approved empty-set value minus infinity.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfDimension_lt_of_companion_lt
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hd : vfDim Δ A < n) : vfDimension A.carrier < (n : WithBot ℕ) := by
  apply lt_of_le_of_ne (vfDimension_le_arity A.carrier)
  intro he
  obtain ⟨t, D, hD⟩ := (lemma_2_17 A.carrier).mp he
  exact hd.ne (vfDim_eq_arity_of_contains_polydisc hc hs hsmall Δ hΔ hv A t D hD)

/-- Integration of the quoted [17, Lemma 8.7] as Lemma 2.36, including zero
source arity. The graph and closed exceptional
set use exactly the original real base S, and the dimension is the paper's
own minus-infinity-valued interior dimension. -/
theorem lemma_2_36
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n m : ℕ} (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfGraph f)) :
    ∃ A : Set (Fin n → VF M), S.Definable LRV (vfValues '' A) ∧ IsClosed A ∧
      vfDimension (A ×ˢ (Set.univ : Set (Fin 0 → RVInfinity M))) < (n : WithBot ℕ) ∧
      ContinuousOn f Aᶜ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨∅, ?_, isClosed_empty, ?_, ?_⟩
    · simpa only [Set.image_empty] using (Set.definable_empty :
        S.Definable LRV (∅ : Set (Fin 0 → M)))
    · simp only [Set.empty_prod, vfDimension_empty]
      exact WithBot.bot_lt_coe 0
    · have he : f = fun _ => f 0 :=
        funext (fun x => congrArg f (Subsingleton.elim x 0))
      rw [he]
      exact continuous_const.continuousOn
  · obtain ⟨B, hB, hsort, hclosed, hdim, hcont⟩ :=
      lemma_8_7_canonical hc hκ hs hsmall hn hv f hf
    let A : Set (Fin n → VF M) := {a | vfValues a ∈ B}
    have he : vfValues '' A = B := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hz
        let a : Fin n → VF M := fun i => ⟨z i, hsort hz i⟩
        exact ⟨a, hz, rfl⟩
    refine ⟨A, he.symm ▸ hB, hclosed, ?_, hcont⟩
    have hcarrier : (vfObjectOfRaw hB).carrier =
        A ×ˢ (Set.univ : Set (Fin 0 → RVInfinity M)) := by
      ext p
      exact (and_iff_left (Set.mem_univ p.2)).symm
    rw [← hcarrier]
    exact vfDimension_lt_of_companion_lt hc hs hsmall _ (rawRVSpace_rvCoded 1)
      hv (vfObjectOfRaw hB) hdim

end DiamondIntegral.Section2
