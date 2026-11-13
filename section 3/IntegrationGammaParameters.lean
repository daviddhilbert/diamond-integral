import IntegrationSection3ACVF.FullGammaAtomicity
import IntegrationSection3ACVF.AdjoinGamma
import «section 2».AtomicBaseChange
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Parameter-preserving reuse of [18, Lemma 3.3] from the pinned
integration-in-ACVF repository. The equivalence uses full code preimages;
no chosen Gamma representative is named. The original-base nontriviality
condition supplies the positive definable value used by the source proof. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section3ACVF.FullGammaSyntax
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def integrationGammaBase (B : GammaParameters.Base (M := M)) : FullBaseAtomicity.Base (M := M) :=
  ⟨B.real, Sum.inr '' B.gamma⟩

def integrationGammaRelation {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (R : GammaParameters.Relation S k n sn)
    (θ : Fin k → ParameterPresentation.Name (M := M)) : Set (Fin n → M) :=
  {b | ∃ η : Fin k → Values.Gamma (M := M), θ = (fun i => Sum.inr (η i)) ∧ b ∈ R.fibre η}

theorem integrationGammaRelation_pullback {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (R : GammaParameters.Relation S k n sn)
    (z : (Fin k × Fin 5) ⊕ Fin n → M) :
    z ∈ ImaginaryParameters.vectorPullback
      (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin k))
      (integrationGammaRelation R) ↔
      ((fun i => z (.inl (i, 0))), z ∘ Sum.inr) ∈ R.carrier ∧
        ∀ i, z (.inl (i, 4)) ≠ iVFZero := by
  constructor
  · rintro ⟨hz, η, hη, hb⟩
    have hf (i : Fin k) : z (.inl (i, 4)) ≠ iVFZero := by
      intro he
      have h := congrFun hη i
      change ParameterPresentation.decode ⟨fun j => z (.inl (i, j)), hz i⟩ = Sum.inr (η i) at h
      simp only [ParameterPresentation.decode, dite_eq_left he] at h
      cases h
    have hp (i : Fin k) : NonzeroRV (z (.inl (i, 0))) :=
      ((hz i).resolve_left (fun h => hf i h.1)).2
    let c : Fin k → GammaParameters.Code (M := M) := fun i => ⟨⟨_, (hp i).1⟩, (hp i).2⟩
    have hc : GammaParameters.values c = η := by
      funext i
      have h := congrFun hη i
      change ParameterPresentation.decode ⟨fun j => z (.inl (i, j)), hz i⟩ = Sum.inr (η i) at h
      simp only [ParameterPresentation.decode, dite_eq_right (hf i)] at h
      exact (codeValue_raw (c i)).symm.trans (Sum.inr.inj h)
    exact ⟨(R.mem_fibre_iff c η hc _).mp hb, hf⟩
  · rintro ⟨hR, hf⟩
    have hp := (R.proper _ hR).1
    let c := GammaParameters.ofRaw (fun i => z (.inl (i, 0))) hp
    have hz : ImaginaryParameters.tupleCodes (@ParameterPresentation.presentation M sM hM) (Fin k)
        (fun ij => z (.inl ij)) := fun i => Or.inr ⟨hf i, hp i⟩
    refine ⟨hz, GammaParameters.values c, ?_, (R.full_preimage c _).mpr ?_⟩
    · funext i
      change ParameterPresentation.decode ⟨fun j => z (.inl (i, j)), hz i⟩ = _
      simp only [ParameterPresentation.decode, dite_eq_right (hf i)]
      exact congrArg Sum.inr (codeValue_raw (c i))
    · exact hR

theorem integrationGammaRelation_definable {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (R : GammaParameters.Relation S k n sn) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ((Fin k × Fin 5) ⊕ Fin n)
      (ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin k))
        (integrationGammaRelation R)) := by
  have hRd := R.definable
  have hEd := AdjoinGamma.embedCode_definable (M := M) S
  have hpull := integrationGammaRelation_pullback R
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hr := hRd.preimage_comp (Sum.map (fun i : Fin k => (i, (0 : Fin 5))) id)
  have hf : @Set.Definable M S LRV N ((Fin k × Fin 5) ⊕ Fin n)
      {z | ∀ i, z (.inl (i, 4)) ≠ @iVFZero M sM} := by
    letI := N
    rw [Set.ofPred_forall]
    apply Set.definable_iInter_of_finite
    intro i
    have hz : S.DefinableFun LRV
        (fun _ : (Fin k × Fin 5) ⊕ Fin n → M => @iVFZero M sM) :=
      (hEd (1 : Fin 5)).comp
        (g := fun z : (Fin k × Fin 5) ⊕ Fin n → M => fun _ : Fin 1 => z (Sum.inl (i, 0)))
        (fun _ : Fin 1 => Set.DefinableFun.proj LRV (i := Sum.inl (i, (0 : Fin 5))))
    exact ((Set.DefinableFun.proj LRV (i := Sum.inl (i, (4 : Fin 5)))).ofPred_eq hz).compl
  letI := N
  convert hr.inter hf using 1
  ext z
  exact hpull z

theorem integrationGammaWith {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    {γ : Fin k → Values.Gamma (M := M)} {A : Set (Fin n → M)}
    (hA : GammaParameters.DefinableWith S γ sn A) :
    @ImaginaryParameters.WithTuple LRV M (CanonicalStructure.normalize (M := M))
      (ParameterPresentation.Name (M := M)) (Fin 5) (@ParameterPresentation.presentation M sM hM)
      S (Fin k) (Fin n) (fun i => Sum.inr (γ i)) A := by
  obtain ⟨R, rfl⟩ := hA
  refine ⟨integrationGammaRelation R, integrationGammaRelation_definable R, ?_⟩
  ext b
  constructor
  · rintro ⟨η, hη, hb⟩
    have he : γ = η := funext (fun i => Sum.inr.inj (congrFun hη i))
    exact he.symm ▸ hb
  · intro hb
    exact ⟨γ, rfl, hb⟩

theorem integrationGammaDefinable {B : GammaParameters.Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : GammaParameters.DefinableOverBase B sn A) : FullBaseAtomicity.OverBase (integrationGammaBase B) A := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  let F : Finset (ParameterPresentation.Name (M := M)) := Finset.univ.image (fun i => Sum.inr (γ i))
  have hF (i : Fin k) : Sum.inr (γ i) ∈ F := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  refine ⟨F, ?_, ?_⟩
  · rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨γ j, hγ j, rfl⟩
  · have hw := integrationGammaWith hA
    have hp := ParameterPresentation.codeDomain_definable B.real
    letI := CanonicalStructure.normalize (M := M)
    exact hw.reindex hp (fun i => (⟨Sum.inr (γ i), hF i⟩ : F)) rfl
end DiamondIntegral.Section3
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {ι : Type} [Fintype ι] {k n : ℕ}

def integrationGammaRecode (e : ι → Fin k) (z : Fin k ⊕ Fin n → M) : (ι × Fin 5) ⊕ Fin n → M :=
  Sum.elim (fun p => AdjoinGamma.embedCode ![z (.inl (e p.1))] p.2) (z ∘ Sum.inr)

theorem integrationGammaRecode_definable (S : Set M) (e : ι → Fin k) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin n)
      ((ι × Fin 5) ⊕ Fin n) S (integrationGammaRecode e) := by
  have he := AdjoinGamma.embedCode_definable (M := M) S
  letI := CanonicalStructure.normalize (M := M)
  intro j
  cases j with
  | inl p =>
    exact (he p.2).comp
      (fun _ : Fin 1 => Set.DefinableFun.proj LRV (i := Sum.inl (e p.1)))
  | inr j => exact Set.DefinableFun.proj LRV

theorem integrationGammaRecode_row (e : ι → Fin k)
    (R : (ι → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (t : Fin k → GammaParameters.Code (M := M)) (b : Fin n → M) :
    integrationGammaRecode e (Sum.elim (GammaParameters.rawTuple t) b) ∈
      ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) ι) R ↔
      b ∈ R (fun j => Sum.inr (GammaParameters.values t (e j))) := by
  let z := integrationGammaRecode e (Sum.elim (GammaParameters.rawTuple t) b)
  have hz : ImaginaryParameters.tupleCodes (@ParameterPresentation.presentation M sM hM) ι
      (z ∘ Sum.inl) := fun j =>
    (AdjoinGamma.embedCode_compatible ![GammaParameters.raw (t (e j))]
      ⟨GammaParameters.raw_rv _, GammaParameters.raw_ne_zero _⟩).choose
  have hdecode (h : (z ∘ Sum.inl) ∈ ImaginaryParameters.tupleCodes
      (@ParameterPresentation.presentation M sM hM) ι) :
      (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) ι).decode
        ⟨z ∘ Sum.inl, h⟩ = (fun j => Sum.inr (GammaParameters.values t (e j))) := by
    funext j
    exact (AdjoinGamma.embedCode_compatible ![GammaParameters.raw (t (e j))]
      ⟨GammaParameters.raw_rv _, GammaParameters.raw_ne_zero _⟩).choose_spec.trans
        (congrArg Sum.inr (codeValue_raw (t (e j))))
  constructor
  · rintro ⟨h, hb⟩
    exact hdecode h ▸ hb
  · intro hb
    exact ⟨hz, (hdecode hz).symm ▸ hb⟩

def integrationGammaRelationOfFull (S : Set M) (sn : Fin n → SortTag) (e : ι → Fin k)
    (R : (ι → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ((ι × Fin 5) ⊕ Fin n)
      (ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) ι) R)) :
    GammaParameters.Relation S k n sn where
  carrier := {p | GammaParameters.Proper p.1 ∧ (∀ i, sortEval (sn i) (p.2 i)) ∧
    integrationGammaRecode e (Sum.elim p.1 p.2) ∈
      ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) ι) R}
  definable := by
    have hp0 := GammaParameters.proper_normalized_definable (M := M) S (n := k)
    have hs0 := ((definableOver_iff_normalized_raw S sn (GammaParameters.sortedUniverse sn)).mp
      (GammaParameters.sortedUniverse_definable S sn)).1
    have hm := integrationGammaRecode_definable (M := M) S e (n := n)
    letI := CanonicalStructure.normalize (M := M)
    have hp := hp0.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n)
    have hs := hs0.preimage_comp (Sum.inr : Fin n → Fin k ⊕ Fin n)
    have hr := hR.preimage_map hm
    convert hp.inter (hs.inter hr) using 1
    ext z
    rfl
  proper p hp := ⟨hp.1, hp.2.1⟩
  invariant t u htu b := by
    change (Proper (rawTuple t) ∧ (∀ i, sortEval (sn i) (b i)) ∧ _) ↔
      (Proper (rawTuple u) ∧ (∀ i, sortEval (sn i) (b i)) ∧ _)
    rw [integrationGammaRecode_row, integrationGammaRecode_row, htu]
    simp only [rawTuple_proper]

theorem integrationGammaDefinable_iff {B : GammaParameters.Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hproper : ∀ b ∈ A, ∀ i, sortEval (sn i) (b i)) :
    GammaParameters.DefinableOverBase B sn A ↔ FullBaseAtomicity.OverBase (integrationGammaBase B) A := by
  constructor
  · exact integrationGammaDefinable
  · rintro ⟨F, hF, R, hR, hRA⟩
    have hnames (j : F) : ∃ γ ∈ B.gamma, j.val = Sum.inr γ := by
      obtain ⟨γ, hγ, he⟩ := hF j.val j.property
      exact ⟨γ, hγ, he.symm⟩
    choose γ hγ hname using hnames
    let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
    let δ : Fin (Fintype.card F) → Values.Gamma (M := M) := γ ∘ e.symm
    let Q := integrationGammaRelationOfFull B.real sn e R hR
    refine ⟨Fintype.card F, δ, (fun i => hγ (e.symm i)), Q, ?_⟩
    ext b
    change (Proper (rawTuple (representatives δ)) ∧ (∀ i, sortEval (sn i) (b i)) ∧ _) ↔ b ∈ A
    rw [integrationGammaRecode_row, representatives_values]
    have he : (fun j : F => Sum.inr (δ (e j))) = (Subtype.val : F → ParameterPresentation.Name (M := M)) := by
      funext j
      simp only [δ, Function.comp_apply, Equiv.symm_apply_apply]
      exact (hname j).symm
    rw [he, hRA]
    exact ⟨fun h => h.2.2, fun h => ⟨rawTuple_proper _, hproper b h, h⟩⟩
end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationGammaAtomic {B : GammaParameters.Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : Section2.IsAtomic B sn A) : FullGammaAtomicity.AtomicTuple (integrationGammaBase B) A := by
  refine ⟨integrationGammaDefinable hA.1, ?_⟩
  intro C hC
  have hs : GammaParameters.DefinableOverBase B sn (GammaParameters.sortedUniverse sn) :=
    GammaParameters.real_definableOverBase B sn _ (GammaParameters.sortedUniverse_definable B.real sn)
  have hcut := FullBaseAtomicity.OverBase.inter hC (integrationGammaDefinable hs)
  have hc : GammaParameters.DefinableOverBase B sn (C ∩ GammaParameters.sortedUniverse sn) :=
    (integrationGammaDefinable_iff (fun b hb => hb.2)).mpr hcut
  rcases hA.2.2.2 _ hc with hin | hd
  · exact Or.inl (fun b hb => (hin hb).1)
  · exact Or.inr (Set.disjoint_left.mpr (fun b hb hc =>
      Set.disjoint_left.mp hd hb ⟨hc,hA.2.2.1 hb⟩))

theorem integrationGammaAtomic_to_native {B : GammaParameters.Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : FullGammaAtomicity.AtomicTuple (integrationGammaBase B) A)
    (hne : A.Nonempty) (hp : A ⊆ GammaParameters.sortedUniverse sn) : Section2.IsAtomic B sn A := by
  refine ⟨(integrationGammaDefinable_iff (fun b hb => hp hb)).mpr hA.1,hne,hp,?_⟩
  intro C hC
  exact hA.2 C (integrationGammaDefinable hC)

theorem integrationGammaBase_adjoin (B : GammaParameters.Base (M := M))
    (γ : Values.Gamma (M := M)) :
    integrationGammaBase (Section2.adjoinGamma B γ) = (integrationGammaBase B).adjoin (Sum.inr γ) := by
  simp only [integrationGammaBase, Section2.adjoinGamma, ImaginaryParameters.Base.adjoin,
    Set.image_insert_eq]

/-- The formerly replaceable [18, Lemma 3.3] input is furnished by the
checked upstream theorem, under its original characteristic and definable
nontrivial-value hypotheses. No representative is added to the real base. -/
theorem integrationAtomicGammaBaseChangeInput (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (δ : Values.Gamma (M := M))
    (hδ : GammaParameters.GammaDefinableClosureAtBase B δ) (hδ1 : 1 < δ) :
    Section2.AtomicGammaBaseChangeInput B := by
  intro _ n sn A hA γ
  have hd : FullGammaSyntax.Scalar (integrationGammaBase B) {δ} := integrationGammaDefinable hδ
  have h := FullGammaAtomicity.lemma_3_3_one h00 (integrationGammaBase B) δ hd hδ1
    (integrationGammaAtomic hA) γ
  rw [← integrationGammaBase_adjoin] at h
  exact (integrationGammaAtomic_to_native h hA.2.1 hA.2.2.1).2

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationGammaDiv_definable (B : FullBaseAtomicity.Base (M := M))
    (γ δ : Values.Gamma (M := M))
    (hγ : FullGammaSyntax.Scalar B {γ}) (hδ : FullGammaSyntax.Scalar B {δ}) :
    FullGammaSyntax.Scalar B {δ / γ} := by
  have hp := ((FullGammaSyntax.unary_at hγ (Sum.inr (0 : Fin 2))).and
    (FullGammaSyntax.unary_at hδ (Sum.inr (1 : Fin 2)))).and
    (FullGammaSyntax.mul_definable B (Sum.inl (0 : Fin 1)) (Sum.inr 0) (Sum.inr 1))
  apply (FullGammaSyntax.scalar_definable_iff {δ / γ}).mp
  apply hp.exists_block.congr
  intro a
  change (∃ b : Fin 2 → Values.Gamma (M := M),
    (b 0 = γ ∧ b 1 = δ) ∧ a 0 * b 0 = b 1) ↔ a 0 = δ / γ
  constructor
  · rintro ⟨b,⟨hb0,hb1⟩,he⟩
    rw [hb0,hb1] at he
    exact (eq_div_iff_mul_eq').mpr he
  · intro he
    exact ⟨![γ,δ],⟨rfl,rfl⟩,(eq_div_iff_mul_eq').mp he⟩

theorem integrationPositiveGamma_of_nontrivial (B : GammaParameters.Base (M := M))
    (hΓ : Section2.NontrivialDefinableGamma B) :
    ∃ δ : Values.Gamma (M := M), FullGammaSyntax.Scalar (integrationGammaBase B) {δ} ∧ 1 < δ := by
  obtain ⟨γ,δ,hγ,hδ,hne⟩ := hΓ
  have hg : FullGammaSyntax.Scalar (integrationGammaBase B) {γ} := integrationGammaDefinable hγ
  have hd : FullGammaSyntax.Scalar (integrationGammaBase B) {δ} := integrationGammaDefinable hδ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨δ / γ,integrationGammaDiv_definable _ γ δ hg hd,one_lt_div'.mpr hlt⟩
  · exact ⟨γ / δ,integrationGammaDiv_definable _ δ γ hd hg,one_lt_div'.mpr hgt⟩

theorem integrationAtomicGammaBaseChangeInput_complete (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) : Section2.AtomicGammaBaseChangeInput B := by
  intro hΓ n sn A hA γ
  obtain ⟨δ,hd,hd1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  have h := FullGammaAtomicity.lemma_3_3_one h00 (integrationGammaBase B) δ hd hd1
    (integrationGammaAtomic hA) γ
  rw [← integrationGammaBase_adjoin] at h
  exact (integrationGammaAtomic_to_native h hA.2.1 hA.2.2.1).2
end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Diamond-integral Lemma 2.23, now using the compiled [18, Lemma 3.3]
proof rather than a replaceable geometric premise. -/
theorem integration_lemma_2_23 (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : Section2.IsAtomic B sn A) (γ : Values.Gamma (M := M)) :
    Section2.IsAtomic (Section2.adjoinGamma B γ) sn A :=
  Section2.lemma_2_23 B (integrationAtomicGammaBaseChangeInput_complete h00 B) hΓ sn A hA γ
end DiamondIntegral.Section3
