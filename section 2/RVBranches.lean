import «section 2».RVImage
import «section 2».VFImages

/-! Finite RV-labelled branches extracted from the checked image-constancy
result. The tag set includes rv(0). Individual tags are named only when
forming their branch graphs; no individual ground-definability is assumed. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfRelationTags {n : ℕ} (A : Set (Fin n → M)) (F : Set ((Fin n → M) × M)) : Set M :=
  {t | ∃ a ∈ A, (a, t) ∈ vfRVImage F}

def vfTagBranch {n : ℕ} (A : Set (Fin n → M))
    (F : Set ((Fin n → M) × M)) (t : RVInfinity M) : Set ((Fin n → M) × M) :=
  {p | p.1 ∈ A ∧ p ∈ F ∧ iRv p.2 = t.val}

omit hM in
/-- All source rows have precisely the global tag set. No nonempty-row
hypothesis is used: the common set is allowed to be empty. -/
theorem vfRelationTags_eq_row {n : ℕ} (A : Set (Fin n → M))
    (F : Set ((Fin n → M) × M))
    (hcommon : ∀ a ∈ A, ∀ b ∈ A,
      iRv '' {y | (a, y) ∈ F} = iRv '' {y | (b, y) ∈ F})
    (a : Fin n → M) (ha : a ∈ A) :
    vfRelationTags A F = iRv '' {y | (a, y) ∈ F} := by
  ext t
  constructor
  · rintro ⟨b, hb, y, hy, hyt⟩
    rw [← hcommon b hb a ha]
    exact ⟨y, hy, hyt⟩
  · rintro ⟨y, hy, hyt⟩
    exact ⟨a, ha, y, hy, hyt⟩

omit hM in
/-- Finiteness is inherited from one finite VF row, with the zero tag kept. -/
theorem vfRelationTags_finite {n : ℕ} (A : Set (Fin n → M))
    (F : Set ((Fin n → M) × M)) (hne : A.Nonempty)
    (hcommon : ∀ a ∈ A, ∀ b ∈ A,
      iRv '' {y | (a, y) ∈ F} = iRv '' {y | (b, y) ∈ F})
    (hfinite : ∀ a ∈ A, {y | (a, y) ∈ F}.Finite) :
    (vfRelationTags A F).Finite := by
  obtain ⟨a, ha⟩ := hne
  rw [vfRelationTags_eq_row A F hcommon a ha]
  exact (hfinite a ha).image _

/-- The complete finite tag set is definable over the original base, even
when its individual members require names. -/
theorem vfRelationTags_definable (B : ParameterBase M) {n : ℕ}
    (A : Set (Fin n → M)) (F : Set ((Fin n → M) × M))
    (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) A)
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) :
    GammaParameters.DefinableAtBase B .rv (vfRelationTags A F) := by
  let sn : Fin (n + 1) → SortTag := Fin.lastCases .rv (fun _ : Fin n => .vf)
  have hR := vfRVImage_definable B F hF
  have hA' := hA.preimage_real sn Fin.castSucc
  have hp := (hR.inter hA').image_real (fun _ : Fin 1 => Fin.last n)
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv)
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
    refine ⟨w, ⟨hwR, hwA, hR.proper w hwR⟩, ?_⟩
    funext j
    fin_cases j
    simp [w, Function.comp_apply]
  · rintro ⟨w, ⟨hwR, hwA, _⟩, he⟩
    have ht : w (Fin.last n) = z 0 := congrFun he 0
    refine ⟨Fin.init w, hwA, ?_⟩
    change (Fin.init w, z 0) ∈ vfRVImage F
    change (Fin.init w, w (Fin.last n)) ∈ vfRVImage F at hwR
    rwa [ht] at hwR

/-- A tag branch has its exact full graph over B together with that RV
name. This retains both its domain and its zero tag. -/
theorem vfTagBranch_definable (B : ParameterBase M) {n : ℕ}
    (A : Set (Fin n → M)) (F : Set ((Fin n → M) × M))
    (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) A)
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) (t : RVInfinity M) :
    GammaParameters.DefinableOverBase (adjoinRV B t) (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ vfTagBranch A F t} := by
  let sn : Fin (n + 2) → SortTag := Fin.lastCases .rv (fun _ : Fin (n + 1) => .vf)
  let R : Set ((Fin (n + 1) → M) × M) :=
    {p | p.1 ∈ GammaParameters.sortedUniverse (fun _ => .vf) ∧
      iRv (p.1 (Fin.last n)) = p.2}
  have heq := rv_eq_definable B sn (Fin.last n).castSucc (Fin.last (n + 1))
    (by simp [sn]) (by simp [sn])
  have hR : GammaParameters.DefinableOverBase B sn
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
  have hcut := rv_row_definable B R hR t
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
    exact ⟨⟨⟨ha, hF'.proper z hf⟩, hf⟩, hF'.proper z hf, ht⟩
  · rintro ⟨⟨⟨ha, _⟩, hf⟩, _, ht⟩
    exact ⟨ha, hf, ht⟩

omit hM in
/-- Each retained tag selects exactly one VF value in every source row. -/
theorem vfTagBranch_existsUnique {n : ℕ} (A : Set (Fin n → M))
    (F : Set ((Fin n → M) × M))
    (hcommon : ∀ a ∈ A, ∀ b ∈ A,
      iRv '' {y | (a, y) ∈ F} = iRv '' {y | (b, y) ∈ F})
    (hrv : ∀ a ∈ A, Set.InjOn iRv {y | (a, y) ∈ F})
    (t : RVInfinity M) (ht : t.val ∈ vfRelationTags A F)
    (a : Fin n → M) (ha : a ∈ A) :
    ∃! y, (a, y) ∈ vfTagBranch A F t := by
  have htag : t.val ∈ iRv '' {y | (a, y) ∈ F} := by
    rwa [← vfRelationTags_eq_row A F hcommon a ha]
  obtain ⟨y, hy, hyt⟩ := htag
  refine ⟨y, ⟨ha, hy, hyt⟩, ?_⟩
  rintro z ⟨_, hz, hzt⟩
  exact hrv a ha hz hy (hzt.trans hyt.symm)

/-- Choice produces single-valued functions without discarding their
B+t-definable restricted graphs. The empty tag family needs no branch. -/
theorem vfTagBranch_function {n : ℕ} (A : Set (Fin n → M))
    (F : Set ((Fin n → M) × M))
    (hcommon : ∀ a ∈ A, ∀ b ∈ A,
      iRv '' {y | (a, y) ∈ F} = iRv '' {y | (b, y) ∈ F})
    (hrv : ∀ a ∈ A, Set.InjOn iRv {y | (a, y) ∈ F})
    (t : RVInfinity M) (ht : t.val ∈ vfRelationTags A F) :
    ∃ g : (Fin n → M) → M, ∀ a ∈ A, ∀ y,
      (a, y) ∈ vfTagBranch A F t ↔ g a = y := by
  classical
  have hex (a : Fin n → M) (ha : a ∈ A) :=
    vfTagBranch_existsUnique A F hcommon hrv t ht a ha
  let g (a : Fin n → M) : M := if ha : a ∈ A then (hex a ha).choose else (0 : VF M).val
  refine ⟨g, ?_⟩
  intro a ha y
  have hspec := (hex a ha).choose_spec
  have hg : g a = (hex a ha).choose := dite_eq_left ha
  rw [hg]
  exact ⟨fun hy => (hspec.2 y hy).symm, fun hy => hy ▸ hspec.1⟩

/-- The tagged branches reconstruct every VF row, including its zero value. -/
theorem vfTagBranch_cover (B : ParameterBase M) {n : ℕ}
    (A : Set (Fin n → M)) (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) (a : Fin n → M) (ha : a ∈ A) (y : M) :
    (a, y) ∈ F ↔ ∃ t : RVInfinity M,
      t.val ∈ vfRelationTags A F ∧ (a, y) ∈ vfTagBranch A F t := by
  constructor
  · intro hy
    have hrow : (Fin.snoc a y : Fin (n + 1) → M) ∈
        {z : Fin (n + 1) → M | (Fin.init z, z (Fin.last n)) ∈ F} := by
      simpa only [Fin.init_snoc, Fin.snoc_last, Set.mem_ofPred_eq] using hy
    have hyVF : iVF y := by
      simpa only [Fin.snoc_last, sortEval, iVF] using
        hF.proper (Fin.snoc a y) hrow (Fin.last n)
    let t := rv M (⟨y, hyVF⟩ : VF M)
    exact ⟨t, ⟨a, ha, y, hy, rfl⟩, ha, hy, rfl⟩
  · rintro ⟨t, _, _, hy, _⟩
    exact hy

/-- The finite single-valued branch construction used before the geometric
part of 2.29. It uses the checked 2.26, not a geometric image premise. -/
theorem atomic_polydisc_rv_branches (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) {n : ℕ} (D : Fin n → Set M)
    (hball : ∀ j, IsBall (D j)) (hinf : ∀ j, (D j).Infinite)
    (hA : IsAtomic B (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F})
    (hfinite : ∀ a ∈ {a | ∀ j, a j ∈ D j}, {y | (a, y) ∈ F}.Finite)
    (hrv : ∀ a ∈ {a | ∀ j, a j ∈ D j}, Set.InjOn iRv {y | (a, y) ∈ F}) :
    let A := {a | ∀ j, a j ∈ D j}
    (vfRelationTags A F).Finite ∧
    GammaParameters.DefinableAtBase B .rv (vfRelationTags A F) ∧
    ∀ t : RVInfinity M, t.val ∈ vfRelationTags A F →
      ∃ g : (Fin n → M) → M,
        GammaParameters.DefinableOverBase (adjoinRV B t) (fun _ : Fin (n + 1) => .vf)
          {z | Fin.init z ∈ A ∧ g (Fin.init z) = z (Fin.last n)} ∧
        IsAtomic (adjoinRV B t) (fun _ : Fin 1 => .vf) {z | z 0 ∈ g '' A} ∧
        ∀ a ∈ A, ∀ y, ((a, y) ∈ F ∧ iRv y = t.val) ↔ g a = y := by
  let A : Set (Fin n → M) := {a | ∀ j, a j ∈ D j}
  have hc := lemma_2_26 h00 B D hball hinf hA F hF hfinite hrv
  refine ⟨vfRelationTags_finite A F hA.2.1 hc hfinite,
    vfRelationTags_definable B A F hA.1 hF, ?_⟩
  intro t ht
  obtain ⟨g, hg⟩ := vfTagBranch_function A F hc hrv t ht
  have hG : GammaParameters.DefinableOverBase (adjoinRV B t)
      (fun _ : Fin (n + 1) => .vf) (vfFunctionGraph A g) := by
    convert vfTagBranch_definable B A F hA.1 hF t using 1
    ext z
    change (Fin.init z ∈ A ∧ g (Fin.init z) = z (Fin.last n)) ↔
      (Fin.init z, z (Fin.last n)) ∈ vfTagBranch A F t
    constructor
    · rintro ⟨ha, hgy⟩
      exact (hg _ ha _).mpr hgy
    · intro hz
      exact ⟨hz.1, (hg _ hz.1 _).mp hz⟩
  refine ⟨g, hG, vf_function_image_atomic (adjoinRV B t) A g
    (lemma_2_24 h00 B D hball hinf hA t) hG, ?_⟩
  intro a ha y
  exact ⟨fun hy => (hg a ha y).mp ⟨ha, hy⟩,
    fun hy => ((hg a ha y).mpr hy).2⟩

end DiamondIntegral.Section2
