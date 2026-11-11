import «section 2».ZeroFaceRVFibres
import «section 2».ScalarCorrespondencePullback
import «section 2».OpenRVPartition

/-! The zero-pattern extension of Corollary 2.30 used in 2.35. A finite
original-base partition has constant RV rows on every contained actual
RV polydisc, including arbitrary singleton-zero coordinate factors. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem finitary_rv_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    (D : Set (Fin n → M)) (hD : DefinableOver S (fun _ => .vf) D)
    (F : (Fin n → M) → Set M)
    (hF : DefinableOver S (fun _ : Fin (n+1) => .vf)
      {z | Fin.init z ∈ D ∧ z (Fin.last n) ∈ F (Fin.init z)})
    (hfinite : ∀ x ∈ D, (F x).Finite) (hrv : ∀ x ∈ D, Set.InjOn iRv (F x)) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ D ∧ DefinableOver S (fun _ => .vf) V ∧ RVPolydiscRowsConstant F V) ∧
      ∀ x ∈ D, ∃ V ∈ Q, x ∈ V := by
  classical
  let C (Z : Set (Fin n)) := zeroFaceChart Z
  have hface (Z : Set (Fin n)) :
      ∃ Q : Set (Set (Fin (C Z).freeArity → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
        (∀ V ∈ Q, V.Nonempty ∧ V ⊆ (C Z).slice (0 : VF M).val D ∧
          DefinableOver S (fun _ => .vf) V ∧
          OpenRVRowsConstant (fun u => F ((C Z).insert (0 : VF M).val u)) V) ∧
        ∀ u ∈ (C Z).slice (0 : VF M).val D, ∃ V ∈ Q, u ∈ V := by
    let E := (C Z).slice (0 : VF M).val D
    have hE : DefinableOver S (fun _ => .vf) E := (C Z).vf_slice_definable hc S D hD
    have hΦ := (C Z).insert_definable S (0 : VF M).val (vfZero_singleton_definable S)
    have hmap : Set.MapsTo ((C Z).insert (0 : VF M).val) E D := fun _ h => h.1
    have hpull := scalar_correspondence_pullback_definable hc S D E hE
      ((C Z).insert (0 : VF M).val) hΦ hmap F hF
    exact finitary_open_rv_partition hc h00 hs S hsmall hΓ unary rvbase image E hE
      (fun u => F ((C Z).insert (0 : VF M).val u)) hpull
      (fun u hu => hfinite _ (hmap hu)) (fun u hu => hrv _ (hmap hu))
  choose Q hQ using hface
  let P : Set (Set (Fin n → M)) := ⋃ Z : Set (Fin n), ((C Z).lift (0 : VF M).val) '' Q Z
  have hPf : P.Finite := Set.finite_iUnion (fun Z => (hQ Z).1.image _)
  refine ⟨P,hPf,?_,?_,?_⟩
  · rintro V hV W hW hne
    obtain ⟨Z,hVZ⟩ := Set.mem_iUnion.mp hV
    obtain ⟨V₀,hV₀,rfl⟩ := hVZ
    obtain ⟨T,hWT⟩ := Set.mem_iUnion.mp hW
    obtain ⟨W₀,hW₀,rfl⟩ := hWT
    by_cases hZT : Z = T
    · subst T
      apply (C Z).lift_disjoint
      apply (hQ Z).2.1 hV₀ hW₀
      intro he
      exact hne (he ▸ rfl)
    · exact (C Z).lift_other_disjoint (C T) (0 : VF M).val V₀ W₀
        (fun u hu => ((hQ Z).2.2.1 V₀ hV₀).2.1 hu |>.2)
        (fun u hu => ((hQ T).2.2.1 W₀ hW₀).2.1 hu |>.2) hZT
  · intro V hV
    obtain ⟨Z,hVZ⟩ := Set.mem_iUnion.mp hV
    obtain ⟨V₀,hV₀,rfl⟩ := hVZ
    obtain ⟨hne,hVD,hVdef,hopen⟩ := (hQ Z).2.2.1 V₀ hV₀
    have hnz : ∀ u ∈ V₀, ∀ i, u i ≠ (0 : VF M).val := fun u hu => (hVD hu).2
    refine ⟨?_,(C Z).lift_subset _ D V₀ hVD,(C Z).vf_lift_definable hc S V₀ hVdef,
      (C Z).rv_rows_constant_lift F V₀ hnz hopen⟩
    obtain ⟨u,hu⟩ := hne
    refine ⟨(C Z).insert (0 : VF M).val u,fun i => (C Z).insert_zero _ u i,?_⟩
    simpa only [ZeroFaceChart.project_insert] using hu
  · intro x hx
    let Z : Set (Fin n) := {j | x j = (0 : VF M).val}
    have hxE : (C Z).project x ∈ (C Z).slice (0 : VF M).val D :=
      (C Z).slice_project _ D x hx (fun _ => Iff.rfl)
    obtain ⟨V,hV,hxV⟩ := (hQ Z).2.2.2 _ hxE
    refine ⟨(C Z).lift (0 : VF M).val V,Set.mem_iUnion.mpr ⟨Z,Set.mem_image_of_mem _ hV⟩,?_,hxV⟩
    exact fun i => (C Z).zero_mem i

end DiamondIntegral.Section2
