import «section 2».NamedRVConstancy
import «section 2».NamedVFImages
import «section 2».RVBranches

/-! Finite tagged branches over the original base and retained DC names.
Individual branches add precisely their RV tag; zero and empty tag families
are included. The scalar image atomicity has the same parameter context. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfRelationTags_definable_disc_names (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (A : Set (Fin n → M)) (F : Set ((Fin n → M) × M))
    (hA : DefinableOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) :
    DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin 1 => .rv) {z | z 0 ∈ vfRelationTags A F} := by
  let sn : Fin (n + 1) → SortTag := Fin.lastCases .rv (fun _ : Fin n => .vf)
  have hR := vfRVImage_definable_disc_names B ground d τ F hF
  have hA' := hA.preimage_real sn Fin.castSucc
  have hp := (hR.inter hA').image_real (fun _ : Fin 1 => Fin.last n)
  change DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ vfRelationTags A F}
  have hst : sn ∘ (fun _ : Fin 1 => Fin.last n) = (fun _ => .rv) := by
    funext j
    simp [sn]
  rw [hst] at hp
  convert hp using 1
  ext z
  constructor
  · rintro ⟨a, ha, ht⟩
    let w : Fin (n + 1) → M := Fin.snoc a (z 0)
    have hwR : (Fin.init w, w (Fin.last n)) ∈ vfRVImage F := by
      simpa only [w, Fin.init_snoc, Fin.snoc_last] using ht
    have hwA : w ∘ Fin.castSucc ∈ A := by
      simpa only [w, Function.comp_def, Fin.snoc_castSucc] using ha
    refine ⟨w, ⟨hwR, hwA, hR.proper hwR⟩, ?_⟩
    funext j
    fin_cases j
    simp [w, Function.comp_apply]
  · rintro ⟨w, ⟨hwR, hwA, _⟩, he⟩
    have ht : w (Fin.last n) = z 0 := congrFun he 0
    refine ⟨Fin.init w, hwA, ?_⟩
    change (Fin.init w, z 0) ∈ vfRVImage F
    change (Fin.init w, w (Fin.last n)) ∈ vfRVImage F at hwR
    rwa [ht] at hwR

theorem vfTagBranch_definable_disc_names (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (A : Set (Fin n → M)) (F : Set ((Fin n → M) × M))
    (hA : DefinableOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) (t : RVInfinity M) :
    DefinableOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ vfTagBranch A F t} := by
  let sn : Fin (n + 2) → SortTag := Fin.lastCases .rv (fun _ : Fin (n + 1) => .vf)
  let R : Set ((Fin (n + 1) → M) × M) :=
    {p | p.1 ∈ GammaParameters.sortedUniverse (fun _ => .vf) ∧
      iRv (p.1 (Fin.last n)) = p.2}
  have heq := definableOverFiniteDiscNames_of_ground B ground d τ sn _
    (rv_eq_definable B sn (Fin.last n).castSucc (Fin.last (n + 1)) (by simp [sn]) (by simp [sn]))
  have hR : DefinableOverFiniteDiscNames B ground d τ sn
      {z | (Fin.init z, z (Fin.last (n + 1))) ∈ R} := by
    convert heq using 1
    ext z
    change ((∀ j : Fin (n + 1), iVF (z j.castSucc)) ∧
      iRv (z (Fin.last n).castSucc) = z (Fin.last (n + 1))) ↔
      (z ∈ GammaParameters.sortedUniverse sn ∧
      iRv (z (Fin.last n).castSucc) = z (Fin.last (n + 1)))
    constructor
    · rintro ⟨hv, ht⟩
      refine ⟨?_, ht⟩
      intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [← ht]
        have hrv : iRV (iRv (z (Fin.last n).castSucc)) :=
          (rv M (⟨_, hv (Fin.last n)⟩ : VF M)).property
        simpa only [sn, Fin.lastCases_last, sortEval, iRV] using
          hrv
      · simpa only [sn, Fin.lastCases_castSucc, sortEval, iVF] using hv k
    · rintro ⟨hs, ht⟩
      exact ⟨fun j => by
        simpa only [sn, Fin.lastCases_castSucc, sortEval, iVF] using hs j.castSucc, ht⟩
  have hcut := rv_row_definable_disc_names B ground d τ R hR t
  have hF' := hF.mono (show B.real ⊆ (adjoinRV B t).real from Set.subset_insert _ _)
    (Set.Subset.refl _)
  have hA' := (hA.mono (show B.real ⊆ (adjoinRV B t).real from Set.subset_insert _ _)
    (Set.Subset.refl _)).preimage_real (fun _ : Fin (n + 1) => .vf) Fin.castSucc
  convert (hA'.inter hF').inter hcut using 1
  ext z
  change (Fin.init z ∈ A ∧ (Fin.init z, z (Fin.last n)) ∈ F ∧
    iRv (z (Fin.last n)) = t.val) ↔
    (((Fin.init z ∈ A ∧ z ∈ GammaParameters.sortedUniverse (fun _ => .vf)) ∧
      (Fin.init z, z (Fin.last n)) ∈ F) ∧
      (z ∈ GammaParameters.sortedUniverse (fun _ => .vf) ∧ iRv (z (Fin.last n)) = t.val))
  constructor
  · rintro ⟨ha, hf, ht⟩
    exact ⟨⟨⟨ha, hF'.proper hf⟩, hf⟩, hF'.proper hf, ht⟩
  · rintro ⟨⟨⟨ha, _⟩, hf⟩, _, ht⟩
    exact ⟨ha, hf, ht⟩
theorem vfTagBranch_cover_disc_names (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (A : Set (Fin n → M)) (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F}) (a : Fin n → M) (ha : a ∈ A) (y : M) :
    (a,y) ∈ F ↔ ∃ t : RVInfinity M, t.val ∈ vfRelationTags A F ∧ (a,y) ∈ vfTagBranch A F t := by
  obtain ⟨R,hRF⟩ := hF
  have hAux := R.definable_fibre d τ
  rw [hRF] at hAux
  exact vfTagBranch_cover _ A F hAux a ha y

theorem atomic_polydisc_rv_branches_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ j, IsOpenDisc (D j))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F})
    (hfinite : ∀ a ∈ {a | ∀ j, a j ∈ D j}, {y | (a, y) ∈ F}.Finite)
    (hrv : ∀ a ∈ {a | ∀ j, a j ∈ D j}, Set.InjOn iRv {y | (a, y) ∈ F}) :
    let A := {a | ∀ j, a j ∈ D j}
    (vfRelationTags A F).Finite ∧
    DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin 1 => .rv) {z | z 0 ∈ vfRelationTags A F} ∧
    ∀ t : RVInfinity M, t.val ∈ vfRelationTags A F →
      ∃ g : (Fin n → M) → M,
        DefinableOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin (n + 1) => .vf)
          {z | Fin.init z ∈ A ∧ g (Fin.init z) = z (Fin.last n)} ∧
        IsAtomicOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin 1 => .vf) {z | z 0 ∈ g '' A} ∧
        ∀ a ∈ A, ∀ y, ((a, y) ∈ F ∧ iRv y = t.val) ↔ g a = y := by
  let A : Set (Fin n → M) := {a | ∀ j, a j ∈ D j}
  have hcommon := lemma_2_26_disc_names hc h00 B hΓ cited ground d τ D hopen hA F hF hfinite hrv
  refine ⟨vfRelationTags_finite A F hA.2.1 hcommon hfinite,
    vfRelationTags_definable_disc_names B ground d τ A F hA.1 hF, ?_⟩
  intro t ht
  obtain ⟨g, hg⟩ := vfTagBranch_function A F hcommon hrv t ht
  have hG : DefinableOverFiniteDiscNames (adjoinRV B t) ground d τ
      (fun _ : Fin (n + 1) => .vf) (vfFunctionGraph A g) := by
    convert vfTagBranch_definable_disc_names B ground d τ A F hA.1 hF t using 1
    ext z
    change (Fin.init z ∈ A ∧ g (Fin.init z) = z (Fin.last n)) ↔
      (Fin.init z, z (Fin.last n)) ∈ vfTagBranch A F t
    constructor
    · rintro ⟨ha, hgy⟩
      exact (hg _ ha _).mpr hgy
    · intro hz
      exact ⟨hz.1, (hg _ hz.1 _).mp hz⟩
  refine ⟨g, hG, vf_function_image_atomic_disc_names (adjoinRV B t) ground d τ A g
    (lemma_2_24_disc_names hc h00 B hΓ cited ground d τ D hopen hA t) hG, ?_⟩
  intro a ha y
  exact ⟨fun hy => (hg a ha y).mp ⟨ha, hy⟩,
    fun hy => ((hg a ha y).mpr hy).2⟩

end DiamondIntegral.Section2
