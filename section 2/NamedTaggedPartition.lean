import «section 2».NamedTypePartition
import «section 2».NamedGoodTaggedCodes
import «section 2».NamedTypeGoodDiscs

/-! Corollary 2.30's actual finite partition over old DC ground names.
The good-code predicate and both compactness steps are proved, rather
than included as premises of the numbered result. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem good_tagged_polydisc_partition_disc_names
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {k n : ℕ} (ground : Fin k → Bool) (b : Fin k → VF M) (τ : Fin k → Gamma M)
    (A : Set (Fin n → M))
    (hA : DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ => .vf) A)
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (hfinite : ∀ x ∈ A, {y | (x,y) ∈ F}.Finite)
    (hrv : ∀ x ∈ A, Set.InjOn iRv {y | (x,y) ∈ F}) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧ DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ => .vf) V ∧
        ∀ d, rawOpenPolydiscProper d → rawOpenPolydisc d ⊆ V →
          d ∈ rawGoodTaggedPolydiscCodes F) ∧ ∀ x ∈ A, ∃ V ∈ Q, x ∈ V := by
  let B : ParameterBase M := ⟨S,∅⟩
  let D : Set (Fin (n+n) → M) := {d | rawOpenPolydiscProper d}
  let P := D ∩ rawGoodTaggedPolydiscCodes F
  have hD : DefinableOverFiniteDiscNames B ground b τ (fun _ => .vf) D :=
    definableOverFiniteDiscNames_of_ground B ground b τ _ D
      ((GammaParameters.base_empty_iff S _ D).mpr
        (raw_definableOver_sorted hc S _ D (rawOpenPolydiscProper_definable S n)
          (fun d hd => rawOpenPolydiscProper_sorted d hd)))
  have hP : DefinableOverFiniteDiscNames B ground b τ (fun _ => .vf) P := by
    convert hD.inter (goodTaggedCodes_definable_disc_names hc B ground b τ F hF) using 1
    ext d
    exact ⟨fun h => ⟨h.1,rawOpenPolydiscProper_sorted d h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
  let R := rawOpenPolydisc (M := M) (n := n)
  let H : Set (Fin ((n+n)+n) → M) :=
    {z | z ∘ Fin.castAdd n ∈ D ∧ z ∘ Fin.natAdd (n+n) ∈ R (z ∘ Fin.castAdd n)}
  have hHraw : S.Definable LRV H :=
    ((rawOpenPolydiscProper_definable S n).preimage_comp (Fin.castAdd n)).inter
      ((rawOpenPolydisc_membership_definable S n).preimage_comp
        (Sum.elim (Fin.castAdd n) (Fin.natAdd (n+n))))
  have hHsort : H ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
    intro z hz j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact rawOpenPolydiscProper_sorted _ hz.1 i
    · exact rawOpenPolydisc_proper _ hz.2 i
  have hH : DefinableOverFiniteDiscNames B ground b τ (fun _ => .vf) H :=
    definableOverFiniteDiscNames_of_ground B ground b τ _ H
      ((GammaParameters.base_empty_iff S _ H).mpr (raw_definableOver_sorted hc S _ H hHraw hHsort))
  have htype : ∀ u ∈ A, ∀ d ∈ D, R d ⊆ namedDiscTypeLocus B ground b τ u → d ∈ P := by
    intro u hu d hd hsub
    have hTA : namedDiscTypeLocus B ground b τ u ⊆ A := fun _ hx => hx.2 A hA hu
    refine ⟨hd,?_⟩
    exact type_good_tagged_polydisc_code_disc_names hc h00 B hΓ unary gamma rvbase image ground b τ d hd
      _ (namedDiscTypeLocus_generates B ground b τ u (hA.proper hu)) hsub F hF
      (fun x hx => hfinite x (hTA (hsub hx))) (fun x hx => hrv x (hTA (hsub hx)))
  obtain ⟨C,hCf,hC,hcov⟩ := named_type_local_finite_good_cover hs hκ S hsmall ground b τ A hA D P hD hP R hH htype
  obtain ⟨Q,hQf,hQdis,hQ,hQcov⟩ := named_finite_good_cover_partition B ground b τ A hA D P R C hCf hC hcov
  refine ⟨Q,hQf,hQdis,?_,hQcov⟩
  intro V hV
  obtain ⟨hne,hVA,hVdef,hgood⟩ := hQ V hV
  exact ⟨hne,hVA,hVdef,fun d hd hsub => (hgood d hd hsub).2⟩

end DiamondIntegral.Section2
