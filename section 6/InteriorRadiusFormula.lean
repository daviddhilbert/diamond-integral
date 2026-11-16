import «section 6».NeighborhoodRadii
import Section4.GammaMultiplicationSyntax
import Section8.GammaRadiusBase

/-! The original-base formula for every interior radius, and its least
element. No chosen RV or VF representative is adjoined to the base. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem gamma_ge_one_codes_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) : S.Definable LRV {z : Fin 1 → M |
      GammaParameters.NonzeroRV (z 0) ∧ (1 : Gamma M) ≤ GammaParameters.codeValue (z 0)} := by
  have h1 := GammaSyntax.unary_at (GammaSyntax.one_definable (M := M) S)
    (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1)
  have hle := (GammaSyntax.lt_definable (M := M) S
    (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1) (.inr 0)).not
  have h : GammaSyntax.Definable S (fun z : Fin 1 → Gamma M => 1 ≤ z 0) := by
    apply ((h1.and hle).exists_block).congr
    intro z
    change (∃ u : Fin 1 → Gamma M, u 0 ∈ ({1} : Set (Gamma M)) ∧ ¬ z 0 < u 0) ↔ 1 ≤ z 0
    constructor
    · rintro ⟨u,hu,hle⟩
      rw [show u 0 = 1 from hu] at hle
      exact le_of_not_gt hle
    · intro h
      exact ⟨fun _ => 1,rfl,not_lt_of_ge h⟩
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1)
    {z | GammaSyntax.Proper z ∧ (1 : Gamma M) ≤ GammaParameters.codeValue (z 0)} at h
  rw [normalize_eq_of_isCanonical hc] at h
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz,h⟩
    exact ⟨by intro i; fin_cases i; exact hz,h⟩
  · rintro ⟨hz,h⟩
    exact ⟨hz 0,h⟩

private def interiorBallIndex (n : ℕ) :
    (Fin n ⊕ Fin n) ⊕ Fin 1 → (Fin n ⊕ Fin 1) ⊕ Fin n :=
  Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)

def interiorRadiusCodes (A : Set (Fin n → VF M)) : Set (Fin n ⊕ Fin 1 → M) :=
  {z | z ∘ Sum.inl ∈ vfValues '' A ∧
    GammaParameters.NonzeroRV (z (.inr 0)) ∧
    (1 : Gamma M) ≤ GammaParameters.codeValue (z (.inr 0)) ∧
    ∀ y : Fin n → M, Sum.elim z y ∘ interiorBallIndex n ∈ rawGammaBallRelation n →
      y ∈ vfValues '' A}

theorem interiorRadiusCodes_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) :
    S.Definable LRV (interiorRadiusCodes A) := by
  have hbad := (((rawGammaBallRelation_definable S n).preimage_comp (interiorBallIndex n)).inter
    (hA.preimage_comp Sum.inr).compl).exists_of_finite
  have hbound := (gamma_ge_one_codes_definable hc S).preimage_comp
    (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)
  convert (hA.preimage_comp Sum.inl).inter (hbound.inter hbad.compl) using 1
  ext z
  change (_ ∧ _ ∧ _ ∧ ∀ y, _ → _) ↔ _ ∧ (_ ∧ _) ∧ ¬ ∃ y, _ ∧ ¬ _
  constructor
  · rintro ⟨ha,ht,hb,hall⟩
    exact ⟨ha,⟨ht,hb⟩,by rintro ⟨y,hy,hno⟩; exact hno (hall y hy)⟩
  · rintro ⟨ha,⟨ht,hb⟩,hno⟩
    refine ⟨ha,ht,hb,fun y hy => ?_⟩
    by_contra hn
    exact hno ⟨y,hy,hn⟩

theorem interiorRadiusCodes_at (A : Set (Fin n → VF M))
    (a : Fin n → VF M) (t : M) (ht : GammaParameters.NonzeroRV t) :
    Sum.elim (vfValues a) (fun _ : Fin 1 => t) ∈ interiorRadiusCodes A ↔
      a ∈ A ∧ GammaParameters.codeValue t ∈ InteriorRadii A a := by
  have hmem : vfValues a ∈ vfValues '' A ↔ a ∈ A := by
    constructor
    · rintro ⟨b,hb,he⟩
      exact vfValues_injective he ▸ hb
    · intro ha
      exact ⟨a,ha,rfl⟩
  change (vfValues a ∈ vfValues '' A ∧ GammaParameters.NonzeroRV t ∧ _ ∧ _) ↔ _
  rw [hmem,and_iff_right ht]
  constructor
  · rintro ⟨ha,hbound,hall⟩
    refine ⟨ha,hbound,fun x hx => ?_⟩
    have hball := (rawGammaBallRelation_iff a x t ht).mpr hx
    obtain ⟨y,hy,he⟩ := hall (vfValues x) hball
    exact vfValues_injective he ▸ hy
  · rintro ⟨ha,hbound,hall⟩
    refine ⟨ha,hbound,fun y hy => ?_⟩
    let x : Fin n → VF M := fun i => ⟨y i,hy.2.2.1 i⟩
    have hx : x ∈ vfBall a (GammaParameters.codeValue t) :=
      (rawGammaBallRelation_iff a x t ht).mp hy
    exact ⟨x,hall hx,rfl⟩

theorem interiorRadii_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (a : Fin n → VF M) (ha : a ∈ A) :
    GammaParameters.GammaDefinableOverBase
      (⟨S ∪ Set.range (vfValues a),∅⟩ : ParameterBase M) (InteriorRadii A a) := by
  let T := S ∪ Set.range (vfValues a)
  let f (z : Fin 1 → M) : Fin n ⊕ Fin 1 → M := Sum.elim (vfValues a) z
  have hf : T.DefinableMap LRV f := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have h := ((interiorRadiusCodes_definable hc A hA).mono Set.subset_union_left).preimage_map hf
  have hraw : T.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (InteriorRadii A a)} := by
    convert h using 1
    ext z
    constructor
    · intro hz
      let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
      exact (interiorRadiusCodes_at A a (z 0) ht).mpr
        ⟨ha,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz⟩
    · intro hz
      have ht : GammaParameters.NonzeroRV (z 0) := hz.2.1
      exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr
        ((interiorRadiusCodes_at A a (z 0) ht).mp hz).2
  apply GammaParameters.real_definableAtBase
  apply (definableAt_iff_normalized_raw T .rv _).mpr
  refine ⟨?_,fun _ hz => hz.1⟩
  rwa [normalize_eq_of_isCanonical hc]

theorem interiorRadii_has_least
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (a : Fin n → VF M) (ha : a ∈ A) (hne : (InteriorRadii A a).Nonempty) :
    ∃ γ : Gamma M, IsLeast (InteriorRadii A a) γ := by
  obtain ⟨γ,hγ⟩ := gamma_definable_exists_isGLB h00 _ _ (interiorRadii_definable hc A hA a ha)
    hne ⟨1,fun _ h => h.1⟩
  refine ⟨γ,interiorRadii_closed a γ ?_,hγ.1⟩
  intro δ hδ
  by_contra hn
  have hlower : δ ∈ lowerBounds (InteriorRadii A a) := by
    intro ε hε
    exact le_of_not_gt (fun h => hn (interiorRadii_upper hε h.le))
  exact (not_le_of_gt hδ) (hγ.2 hlower)

end DiamondIntegral.Section6
