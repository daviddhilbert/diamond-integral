import «section 3».GammaGroundParameters
import «section 3».RVFormGraphs

/-! The complete-code Gamma-ground definitions agree with the existing
GammaParameters.Base syntax on actual RV tuples. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k n : ℕ}

theorem gammaRelationPower_definable (R : GammaParameters.Relation S k n (fun _ => .rv)) :
    ((volumeGammaSpace hc).power (Fin k)).RelationDefinable (rawRVSpace n) S
      (fun γ t => rvValues t ∈ R.fibre γ) := by
  have hd := R.definable
  rw [canonical_normalize_eq hc] at hd
  let f : Fin k ⊕ Fin n → (Fin k × Fin 1) ⊕ Fin n :=
    Sum.elim (fun i => Sum.inl (i, 0)) Sum.inr
  have hdef := hd.preimage_comp f
  have he : ((volumeGammaSpace hc).power (Fin k)).relation (rawRVSpace n)
      (fun γ t => rvValues t ∈ R.fibre γ) =
      {z : (Fin k × Fin 1) ⊕ Fin n → M |
        ((fun i => z (.inl (i, 0))), z ∘ Sum.inr) ∈ R.carrier} := by
    ext z
    change (Fin k × Fin 1) ⊕ Fin n → M at z
    have hm (hg : z ∘ Sum.inl ∈ ((volumeGammaSpace hc).power (Fin k)).domain)
        (ht : z ∘ Sum.inr ∈ (rawRVSpace (M := M) n).domain) :
        rvValues ((rawRVSpace n).decode ⟨z ∘ Sum.inr, ht⟩) ∈
          R.fibre (((volumeGammaSpace hc).power (Fin k)).decode ⟨z ∘ Sum.inl, hg⟩) ↔
        ((fun i => z (.inl (i, 0))), z ∘ Sum.inr) ∈ R.carrier := by
      let c : Fin k → GammaParameters.Code (M := M) := fun i =>
        ⟨⟨z (.inl (i, 0)), (hg i).1⟩, (hg i).2⟩
      have hraw : GammaParameters.rawTuple c = fun i => z (.inl (i, 0)) := rfl
      have hvalue : GammaParameters.values c =
          ((volumeGammaSpace hc).power (Fin k)).decode ⟨z ∘ Sum.inl, hg⟩ := rfl
      rw [rvValues_decode, R.mem_fibre_iff c _ hvalue, hraw]
    constructor
    · rintro ⟨hg, ht, hR⟩
      exact (hm hg ht).mp hR
    · intro hR
      have hp := R.proper _ hR
      have hg : z ∘ Sum.inl ∈ ((volumeGammaSpace hc).power (Fin k)).domain := fun i => hp.1 i
      have ht : z ∘ Sum.inr ∈ (rawRVSpace (M := M) n).domain :=
        ⟨fun i => ⟨z (.inr i), hp.2 i⟩, rfl⟩
      exact ⟨hg, ht, (hm hg ht).mpr hR⟩
  change S.Definable LRV _
  rw [he]
  exact hdef

def gammaPowerRawRelation
    (T : Set ((((volumeGammaSpace hc).power (Fin k)).prod (rawRVSpace (M := M) n)).Carrier)) :
    Set ((Fin k → M) × (Fin n → M)) :=
  {p | Sum.elim (fun ij : Fin k × Fin 1 => p.1 ij.1) p.2 ∈
    (((volumeGammaSpace hc).power (Fin k)).prod (rawRVSpace (M := M) n)).preimage T}

theorem gammaPowerRawRelation_row
    (T : Set ((((volumeGammaSpace hc).power (Fin k)).prod (rawRVSpace (M := M) n)).Carrier))
    (t : Fin k → GammaParameters.Code (M := M)) (b : Fin n → M) :
    (GammaParameters.rawTuple t, b) ∈ gammaPowerRawRelation (hc := hc) T ↔
      ∃ hb : b ∈ (rawRVSpace (M := M) n).domain,
        (GammaParameters.values t, (rawRVSpace n).decode ⟨b, hb⟩) ∈ T := by
  constructor
  · rintro ⟨h, hT⟩
    exact ⟨h.2, hT⟩
  · rintro ⟨hb, hT⟩
    exact ⟨⟨fun i => ⟨(t i).val.property, (t i).property⟩, hb⟩, hT⟩

def gammaRelationOfPowerSet
    (T : DefSet (((volumeGammaSpace hc).power (Fin k)).prod (rawRVSpace (M := M) n)) S) :
    GammaParameters.Relation S k n (fun _ => .rv) where
  carrier := gammaPowerRawRelation (hc := hc) T.carrier
  definable := by
    rw [canonical_normalize_eq hc]
    exact T.definable.preimage_comp
      (Sum.elim (fun ij : Fin k × Fin 1 => Sum.inl ij.1) Sum.inr)
  proper p hp := by
    obtain ⟨h, _⟩ := hp
    refine ⟨fun i => h.1 i, ?_⟩
    obtain ⟨a, ha⟩ := h.2
    change rvValues a = p.2 at ha
    intro i
    change iRV (p.2 i)
    rw [← congrFun ha i]
    exact (a i).property
  invariant t u htu b := by
    rw [gammaPowerRawRelation_row (hc := hc), gammaPowerRawRelation_row (hc := hc), htu]

theorem gammaRelationOfPowerSet_fibre
    (T : DefSet (((volumeGammaSpace hc).power (Fin k)).prod (rawRVSpace (M := M) n)) S)
    (γ : Fin k → Values.Gamma (M := M)) (b : Fin n → M) :
    b ∈ (gammaRelationOfPowerSet (hc := hc) T).fibre γ ↔
      ∃ hb : b ∈ (rawRVSpace (M := M) n).domain, (γ, (rawRVSpace n).decode ⟨b, hb⟩) ∈ T.carrier := by
  change (GammaParameters.rawTuple (GammaParameters.representatives γ), b) ∈ gammaPowerRawRelation (hc := hc) T.carrier ↔ _
  rw [gammaPowerRawRelation_row, GammaParameters.representatives_values]

theorem GammaGroundDefinable.toRVBase {ground : GammaParameters.Base (M := M)}
    {A : Set (rawRVSpace (M := M) n).Carrier} (hA : GammaGroundDefinable hc ground (rawRVSpace n) A) :
    GammaParameters.DefinableOverBase ground (fun _ : Fin n => .rv) (rvValues '' A) := by
  obtain ⟨k, γ, hγ, T, hT, ht⟩ := hA
  let D : DefSet (((volumeGammaSpace hc).power (Fin k)).prod (rawRVSpace (M := M) n)) ground.real := ⟨T, hT⟩
  refine ⟨k, γ, hγ, gammaRelationOfPowerSet (hc := hc) D, ?_⟩
  ext b
  rw [gammaRelationOfPowerSet_fibre]
  constructor
  · rintro ⟨hb, hTb⟩
    exact ⟨(rawRVSpace n).decode ⟨b, hb⟩, (ht _).mpr hTb, rvValues_decode _⟩
  · rintro ⟨a, ha, hab⟩
    have hb : b ∈ (rawRVSpace (M := M) n).domain := ⟨a, hab⟩
    refine ⟨hb, (ht _).mp ?_⟩
    have he : (rawRVSpace n).decode ⟨b, hb⟩ = a := rvValues_injective ((rvValues_decode _).trans hab.symm)
    rw [he]
    exact ha

theorem gammaGroundDefinable_iff_rvBase {ground : GammaParameters.Base (M := M)}
    {A : Set (rawRVSpace (M := M) n).Carrier} :
    GammaGroundDefinable hc ground (rawRVSpace n) A ↔
      GammaParameters.DefinableOverBase ground (fun _ : Fin n => .rv) (rvValues '' A) := by
  constructor
  · exact GammaGroundDefinable.toRVBase
  · rintro ⟨k, γ, hγ, T, hT⟩
    refine ⟨k, γ, hγ, {z | rvValues z.2 ∈ T.fibre z.1}, ?_, ?_⟩
    · exact (relationDefinable_iff_product _).mp (gammaRelationPower_definable (hc := hc) T)
    · intro a
      change a ∈ A ↔ rvValues a ∈ T.fibre γ
      rw [hT]
      constructor
      · intro ha
        exact ⟨a, ha, rfl⟩
      · rintro ⟨b, hb, hba⟩
        exact rvValues_injective hba ▸ hb

end DiamondIntegral.Section3
