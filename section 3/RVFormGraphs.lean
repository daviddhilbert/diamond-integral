import «section 3».RVVolumeForms
import «section 3».GammaVolumeForms
import Section4.CanonicalNormalization
import Section4.RVCoordinates

/-! The invariant relation used for RV volume forms is exactly a genuine
definable map to the Gamma imaginary. This comparison keeps all real codes
and does not name a representative of a Gamma value in the parameter base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r k : ℕ}

theorem gammaRelation_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameters.Relation S 1 r (fun _ => .rv)) :
    (volumeGammaSpace hc).RelationDefinable (rawRVSpace r) S
      (fun γ t => rvValues t ∈ R.fibre ![γ]) := by
  have hd := R.definable
  rw [canonical_normalize_eq hc] at hd
  have he : (volumeGammaSpace hc).relation (rawRVSpace r)
      (fun γ t => rvValues t ∈ R.fibre ![γ]) =
      {z : Fin 1 ⊕ Fin r → M | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R.carrier} := by
    ext z
    change Fin 1 ⊕ Fin r → M at z
    have hm (hg : z ∘ Sum.inl ∈ (volumeGammaSpace hc).domain)
        (ht : z ∘ Sum.inr ∈ (rawRVSpace (M := M) r).domain) :
        rvValues ((rawRVSpace r).decode ⟨z ∘ Sum.inr, ht⟩) ∈
          R.fibre ![(volumeGammaSpace hc).decode ⟨z ∘ Sum.inl, hg⟩] ↔
        (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R.carrier := by
      let c : Fin 1 → GammaParameters.Code (M := M) :=
        fun _ => ⟨⟨z (.inl 0), hg.1⟩, hg.2⟩
      have hraw : GammaParameters.rawTuple c = z ∘ Sum.inl := by
        funext i
        fin_cases i
        rfl
      have hvalue : GammaParameters.values c =
          ![(volumeGammaSpace hc).decode ⟨z ∘ Sum.inl, hg⟩] := by
        funext i
        fin_cases i
        rfl
      rw [rvValues_decode, R.mem_fibre_iff c _ hvalue, hraw]
    constructor
    · rintro ⟨hg, ht, hR⟩
      exact (hm hg ht).mp hR
    · intro hR
      have hp := R.proper _ hR
      have hg : z ∘ Sum.inl ∈ (volumeGammaSpace hc).domain := hp.1 0
      have ht : z ∘ Sum.inr ∈ (rawRVSpace (M := M) r).domain :=
        ⟨fun i => ⟨z (.inr i), hp.2 i⟩, rfl⟩
      exact ⟨hg, ht, (hm hg ht).mpr hR⟩
  change S.Definable LRV _
  rw [he]
  exact hd

def RVVolumeForm.toGammaVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    {U : RVObject (M := M) S k} (ω : RVVolumeForm U) : GammaVolumeForm hc U.domain where
  toFun a := ⟨ω.toFun a, Set.mem_univ _⟩
  graph_definable :=
    ((gammaRelation_definable hc ω.graph).swap (volumeGammaSpace hc) (rawRVSpace U.arity)).congr
      (rawRVSpace U.arity) (volumeGammaSpace hc) (by
        intro t γ
        constructor
        · intro h
          obtain ⟨a, ha, hω⟩ := (ω.graph_spec γ (rvValues t)).mp h
          exact ⟨a, rvValues_injective ha, hω⟩
        · rintro ⟨a, ha, hω⟩
          exact (ω.graph_spec γ (rvValues t)).mpr ⟨a, congrArg rvValues ha, hω⟩)

@[simp] theorem RVVolumeForm.toGammaVolumeForm_value
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U : RVObject (M := M) S k} (ω : RVVolumeForm U) (a : U.domain) :
    gammaFormValue (ω.toGammaVolumeForm hc) a = ω.toFun a := rfl

def rvGammaNativeGraph {hc : CanonicalStructure.IsCanonical (M := M)}
    {U : RVObject (M := M) S k} (ω : GammaVolumeForm hc U.domain) :
    Set (Fin U.arity ⊕ Fin 1 → M) :=
  (rawRVSpace U.arity).relation (volumeGammaSpace hc) ω.graph

def rvGammaRawGraph {hc : CanonicalStructure.IsCanonical (M := M)}
    {U : RVObject (M := M) S k} (ω : GammaVolumeForm hc U.domain)
    (g : Fin 1 → M) (t : Fin U.arity → M) : Prop :=
  Sum.elim t g ∈ rvGammaNativeGraph ω

theorem rvGammaRawGraph_code_iff {hc : CanonicalStructure.IsCanonical (M := M)}
    {U : RVObject (M := M) S k} (ω : GammaVolumeForm hc U.domain)
    (c : Fin 1 → GammaParameters.Code (M := M)) (t : Fin U.arity → M) :
    rvGammaRawGraph ω (GammaParameters.rawTuple c) t ↔
      ∃ a : U.domain, rvValues a.val = t ∧ gammaFormValue ω a = GammaParameters.values c 0 := by
  constructor
  · rintro ⟨ht, hg, a, ha, hω⟩
    refine ⟨a, ?_, hω⟩
    have h := congrArg rvValues ha
    exact h.trans (rvValues_decode ⟨t, ht⟩)
  · rintro ⟨a, ha, hω⟩
    have ht : t ∈ (rawRVSpace (M := M) U.arity).domain := ⟨a.val, ha⟩
    have hg : GammaParameters.rawTuple c ∈ (volumeGammaSpace hc).domain :=
      ⟨(c 0).val.property, (c 0).property⟩
    refine ⟨ht, hg, a, ?_, hω⟩
    exact rvValues_injective (ha.trans (rvValues_decode ⟨t, ht⟩).symm)

def GammaVolumeForm.toRVVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    {U : RVObject (M := M) S k} (ω : GammaVolumeForm hc U.domain) : RVVolumeForm U where
  toFun := gammaFormValue ω
  graph := {
    carrier := {p | rvGammaRawGraph ω p.1 p.2}
    definable := by
      rw [canonical_normalize_eq hc]
      have hd : S.Definable LRV
          (rvGammaNativeGraph ω) := ω.graph_definable
      have hs := hd.preimage_comp
        (Sum.swap : Fin U.arity ⊕ Fin 1 → Fin 1 ⊕ Fin U.arity)
      have he : {z : Fin 1 ⊕ Fin U.arity → M |
          rvGammaRawGraph ω (z ∘ Sum.inl) (z ∘ Sum.inr)} =
          {z | z ∘ Sum.swap ∈ rvGammaNativeGraph ω} := by
        ext z
        change Sum.elim (z ∘ Sum.inr) (z ∘ Sum.inl) ∈ rvGammaNativeGraph ω ↔
          z ∘ Sum.swap ∈ rvGammaNativeGraph ω
        have hz : Sum.elim (z ∘ Sum.inr) (z ∘ Sum.inl) = z ∘ Sum.swap := by
          funext i
          cases i <;> rfl
        rw [hz]
      change S.Definable LRV {z : Fin 1 ⊕ Fin U.arity → M |
        rvGammaRawGraph ω (z ∘ Sum.inl) (z ∘ Sum.inr)}
      rw [he]
      exact hs
    proper := by
      rintro ⟨g, t⟩ ⟨ht, hg, _⟩
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i
        exact hg
      · obtain ⟨u, hu⟩ := ht
        intro i
        have hi : (u i).val = t i := congrFun hu i
        change iRV (t i)
        exact hi ▸ (u i).property
    invariant := by
      intro t u he b
      change rvGammaRawGraph ω (GammaParameters.rawTuple t) b ↔
        rvGammaRawGraph ω (GammaParameters.rawTuple u) b
      rw [rvGammaRawGraph_code_iff, rvGammaRawGraph_code_iff, congrFun he 0] }
  graph_spec γ t := by
    change rvGammaRawGraph ω (GammaParameters.rawTuple (GammaParameters.representatives ![γ])) t ↔ _
    rw [rvGammaRawGraph_code_iff, GammaParameters.representatives_values]
    rfl

@[simp] theorem GammaVolumeForm.toRVVolumeForm_value
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U : RVObject (M := M) S k} (ω : GammaVolumeForm hc U.domain) (a : U.domain) :
    (ω.toRVVolumeForm hc).toFun a = gammaFormValue ω a := rfl

theorem GammaVolumeForm.toRV_toGamma (hc : CanonicalStructure.IsCanonical (M := M))
    {U : RVObject (M := M) S k} (ω : GammaVolumeForm hc U.domain) :
    (ω.toRVVolumeForm hc).toGammaVolumeForm hc = ω := by
  apply Map.ext
  intro a
  apply Subtype.ext
  rfl

theorem gammaRelation_ext {R T : GammaParameters.Relation S 1 r (fun _ => .rv)}
    (h : ∀ γ, R.fibre γ = T.fibre γ) : R = T := by
  classical
  have he : R.carrier = T.carrier := by
    ext p
    by_cases hp : GammaParameters.Proper p.1
    · let c := GammaParameters.ofRaw p.1 hp
      have hR := R.full_preimage c p.2
      have hT := T.full_preimage c p.2
      rw [GammaParameters.rawTuple_ofRaw] at hR hT
      exact hR.symm.trans ((Set.ext_iff.mp (h (GammaParameters.values c)) p.2).trans hT)
    · have hR : p ∉ R.carrier := fun ht => hp (R.proper p ht).1
      have hT : p ∉ T.carrier := fun ht => hp (T.proper p ht).1
      simp only [hR, hT]
  cases R
  cases T
  cases he
  rfl

@[ext] theorem RVVolumeForm.ext {U : RVObject (M := M) S k} {ω σ : RVVolumeForm U}
    (h : ∀ a, ω.toFun a = σ.toFun a) : ω = σ := by
  have hf : ω.toFun = σ.toFun := funext h
  have hg : ω.graph = σ.graph := by
    apply gammaRelation_ext
    intro γ
    have he : γ = ![γ 0] := by funext i; fin_cases i; rfl
    ext t
    rw [he, ω.graph_spec, σ.graph_spec]
    constructor
    · rintro ⟨a, ha, hw⟩
      exact ⟨a, ha, (h a).symm.trans hw⟩
    · rintro ⟨a, ha, hs⟩
      exact ⟨a, ha, (h a).trans hs⟩
  cases ω
  cases σ
  cases hf
  cases hg
  rfl

theorem RVVolumeForm.toGamma_toRV (hc : CanonicalStructure.IsCanonical (M := M))
    {U : RVObject (M := M) S k} (ω : RVVolumeForm U) :
    (ω.toGammaVolumeForm hc).toRVVolumeForm hc = ω := by
  apply RVVolumeForm.ext
  intro a
  rfl

def rvVolumeFormEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (U : RVObject (M := M) S k) :
    RVVolumeForm U ≃ GammaVolumeForm hc U.domain where
  toFun := RVVolumeForm.toGammaVolumeForm hc
  invFun := GammaVolumeForm.toRVVolumeForm hc
  left_inv := RVVolumeForm.toGamma_toRV hc
  right_inv := GammaVolumeForm.toRV_toGamma hc

end DiamondIntegral.Section3
