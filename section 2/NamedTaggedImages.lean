import «section 2».NamedRVBranches
import «section 2».NamedPolydiscImages

/-! Full Lemma 2.29 over an existing finite tuple of DC ground names.
All branch graphs, their domain, RV tags and image atomicity retain exactly
that context. The geometric input from [18] remains unary. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem lemma_2_29_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (cited : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ j, IsOpenDisc (D j))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F})
    (hfinite : ∀ a ∈ {a | ∀ j, a j ∈ D j}, {y | (a, y) ∈ F}.Finite)
    (hrv : ∀ a ∈ {a | ∀ j, a j ∈ D j}, Set.InjOn iRv {y | (a, y) ∈ F}) :
    let A := {a | ∀ j, a j ∈ D j}
    ∃ T : Set (RVInfinity M), T.Finite ∧
      DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin 1 => .rv) {z | z 0 ∈ Subtype.val '' T} ∧
      ∃ g : RVInfinity M → (Fin n → M) → M,
        (∀ t ∈ T,
          DefinableOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin (n+1) => .vf)
            (vfFunctionGraph A (g t)) ∧
          ((∃ c : VF M, ∀ a ∈ A, g t a = c.val) ∨
            (IsAtomicOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin 1 => .vf)
                {z | z 0 ∈ g t '' A} ∧ IsOpenDisc (g t '' A))) ∧
          ∀ a ∈ A, ∀ y, ((a, y) ∈ F ∧ iRv y = t.val) ↔ g t a = y) ∧
        ∀ a ∈ A, ∀ y, (a, y) ∈ F ↔ ∃ t ∈ T, g t a = y := by
  classical
  let A : Set (Fin n → M) := {a | ∀ j, a j ∈ D j}
  have hball (j) : IsBall (D j) := (hopen j).isBall
  have hinf (j) : (D j).Infinite := (hopen j).infinite
  obtain ⟨hTags, hTagsDef, hbranches⟩ :=
    atomic_polydisc_rv_branches_disc_names hc h00 B hΓ rvbase ground d τ D hopen hA F hF hfinite hrv
  let T : Set (RVInfinity M) := {t | t.val ∈ vfRelationTags A F}
  have hT : T.Finite := hTags.preimage Subtype.val_injective.injOn
  have hTraw : Subtype.val '' T = vfRelationTags A F := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hz
      exact ⟨⟨z, hTagsDef.proper (show (fun _ : Fin 1 => z) ∈ {w | w 0 ∈ vfRelationTags A F} from hz) 0⟩, hz, rfl⟩
  have hchoose (t : RVInfinity M) : ∃ g : (Fin n → M) → M,
      t ∈ T →
        DefinableOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin (n+1) => .vf)
          (vfFunctionGraph A g) ∧
        ((∃ c : VF M, ∀ a ∈ A, g a = c.val) ∨
          (IsAtomicOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin 1 => .vf) {z | z 0 ∈ g '' A} ∧
            IsOpenDisc (g '' A))) ∧
        ∀ a ∈ A, ∀ y, ((a, y) ∈ F ∧ iRv y = t.val) ↔ g a = y := by
    by_cases ht : t ∈ T
    · obtain ⟨g, hG, _, hg⟩ := hbranches t ht
      have htag (y : M) (hy : y ∈ g '' A) : iRv y = t.val := by
        obtain ⟨a, ha, rfl⟩ := hy
        exact ((hg a ha (g a)).mpr rfl).2
      have hproper : {x : VF M | x.val ∈ g '' A} ≠ Set.univ := by
        intro he
        have hz : (0 : VF M).val ∈ g '' A := (Set.ext_iff.mp he 0).mpr (Set.mem_univ _)
        have ho : (1 : VF M).val ∈ g '' A := (Set.ext_iff.mp he 1).mpr (Set.mem_univ _)
        have heRv : rv M (1 : VF M) = rv M (0 : VF M) :=
          Subtype.ext ((htag _ ho).trans (htag _ hz).symm)
        have heZero : (1 : VF M) = 0 := (rv_eq_zero_iff _).mp (heRv.trans (rv_zero))
        exact one_ne_zero heZero
      have hΓt : NontrivialDefinableGamma (adjoinRV B t) :=
        hΓ.mono (Set.subset_insert _ _) (Set.Subset.refl _)
      have hAt := lemma_2_24_disc_names hc h00 B hΓ rvbase ground d τ D hopen hA t
      have hshape := atomic_open_polydisc_image_disc_names hc h00 (adjoinRV B t) hΓt cited ground d τ D hopen hAt g hG hproper
      exact ⟨g, fun _ => ⟨hG, hshape, hg⟩⟩
    · exact ⟨fun _ => (0 : VF M).val, fun h => (ht h).elim⟩
  choose g hg using hchoose
  refine ⟨T, hT, hTraw ▸ hTagsDef, g, hg, ?_⟩
  intro a ha y
  constructor
  · intro hy
    obtain ⟨t, ht, _, hyF, hyt⟩ := (vfTagBranch_cover_disc_names B ground d τ A F hF a ha y).mp hy
    exact ⟨t, ht, ((hg t ht).2.2 a ha y).mp ⟨hyF, hyt⟩⟩
  · rintro ⟨t, ht, hgy⟩
    exact (((hg t ht).2.2 a ha y).mpr hgy).1

end DiamondIntegral.Section2
