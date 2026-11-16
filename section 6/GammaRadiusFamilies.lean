import «section 6».ClopenCriterion

/-! Uniform least-element formulas for definable closed upper-ray families.
This is the selection step for covariance radii; all proper codes are kept. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def vfGammaFamilyCodes (D : Set (Fin n → VF M))
    (P : (Fin n → VF M) → Set (Gamma M)) : Set (Fin n ⊕ Fin 1 → M) :=
  {z | GammaParameters.NonzeroRV (z (.inr 0)) ∧
    ∃ a ∈ D, vfValues a = z ∘ Sum.inl ∧ GammaParameters.codeValue (z (.inr 0)) ∈ P a}

theorem vfGammaFamilyCodes_at (D : Set (Fin n → VF M))
    (P : (Fin n → VF M) → Set (Gamma M))
    (a : Fin n → VF M) (t : M) (ht : GammaParameters.NonzeroRV t) :
    Sum.elim (vfValues a) (fun _ : Fin 1 => t) ∈ vfGammaFamilyCodes D P ↔
      a ∈ D ∧ GammaParameters.codeValue t ∈ P a := by
  constructor
  · rintro ⟨_,b,hb,he,hP⟩
    have hba := vfValues_injective he
    exact hba ▸ ⟨hb,hP⟩
  · rintro ⟨ha,hP⟩
    exact ⟨ht,a,ha,rfl,hP⟩

theorem vfGammaFamily_fibre_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (D : Set (Fin n → VF M)) (P : (Fin n → VF M) → Set (Gamma M))
    (hP : S.Definable LRV (vfGammaFamilyCodes D P))
    (a : Fin n → VF M) (ha : a ∈ D) :
    GammaParameters.GammaDefinableOverBase
      (⟨S ∪ Set.range (vfValues a),∅⟩ : ParameterBase M) (P a) := by
  let T := S ∪ Set.range (vfValues a)
  let f (z : Fin 1 → M) : Fin n ⊕ Fin 1 → M := Sum.elim (vfValues a) z
  have hf : T.DefinableMap LRV f := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  apply (gamma_real_codes_iff hc T _).mpr
  convert (hP.mono Set.subset_union_left).preimage_map hf using 1
  ext z
  constructor
  · intro hz
    let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    exact (vfGammaFamilyCodes_at D P a (z 0) ht).mpr
      ⟨ha,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz⟩
  · intro hz
    have ht : GammaParameters.NonzeroRV (z 0) := hz.1
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr
      ((vfGammaFamilyCodes_at D P a (z 0) ht).mp hz).2

theorem closed_upper_ray_has_least
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (P : Set (Gamma M))
    (hP : GammaParameters.GammaDefinableOverBase B P) (hne : P.Nonempty)
    (hbounded : BddBelow P)
    (hup : ∀ x ∈ P, ∀ y, x ≤ y → y ∈ P)
    (hclosed : ∀ x, (∀ y, x < y → y ∈ P) → x ∈ P) :
    ∃ x : Gamma M, IsLeast P x := by
  obtain ⟨x,hx⟩ := gamma_definable_exists_isGLB h00 B P hP hne hbounded
  refine ⟨x,hclosed x ?_,hx.1⟩
  intro y hy
  by_contra hn
  have hlower : y ∈ lowerBounds P := fun z hz =>
    le_of_not_gt (fun h => hn (hup z hz y h.le))
  exact (not_le_of_gt hy) (hx.2 hlower)

theorem least_family_graph_definable
    {S : Set M} (D : Set (Fin n → VF M)) (P : (Fin n → VF M) → Set (Gamma M))
    (hP : S.Definable LRV (vfGammaFamilyCodes D P))
    (p : (Fin n → VF M) → Gamma M) (hp : ∀ a ∈ D, IsLeast (P a) (p a)) :
    S.Definable LRV (vfGammaGraph D p) := by
  have hr : S.Definable₂ LRV {q : M × M | iLe q.2 q.1} := by
    change S.Definable LRV {z : Fin 2 → M | iLe (z 1) (z 0)}
    convert (GammaParameters.raw_le_definable S).preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
    ext z
    rfl
  have h := hP.inter (rawFibreForallCompare_definable S _ hP (fun u v => iLe v u) hr)
  convert h using 1
  ext z
  constructor
  · rintro ⟨ht,a,ha,he,hpa⟩
    refine ⟨⟨ht,a,ha,he,hpa.symm ▸ (hp a ha).1⟩,fun t htP => ?_⟩
    have htu : GammaParameters.NonzeroRV t := htP.1
    obtain ⟨b,hb,hbe,hPb⟩ := htP.2
    have hba : b = a := vfValues_injective (hbe.trans he.symm)
    subst b
    exact (GammaParameters.original_le_codeValue_iff _ _ ht htu).mpr
      (by rw [hpa]; exact (hp a ha).2 hPb)
  · rintro ⟨⟨ht,a,ha,he,hPa⟩,hall⟩
    have hleast : IsLeast (P a) (GammaParameters.codeValue (z (.inr 0))) := by
      refine ⟨hPa,fun γ hγ => ?_⟩
      obtain ⟨t,htP,het⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
      have htc : Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => t) ∈ vfGammaFamilyCodes D P :=
        ⟨htP,a,ha,he,het.symm ▸ hγ⟩
      have hle := (GammaParameters.original_le_codeValue_iff _ _ ht htP).mp (hall t htc)
      rwa [het] at hle
    exact ⟨ht,a,ha,he,hleast.unique (hp a ha)⟩

theorem exists_least_closed_upper_ray_family
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (D : Set (Fin n → VF M)) (P : (Fin n → VF M) → Set (Gamma M))
    (hP : S.Definable LRV (vfGammaFamilyCodes D P))
    (hne : ∀ a ∈ D, (P a).Nonempty) (hbounded : ∀ a ∈ D, BddBelow (P a))
    (hup : ∀ a ∈ D, ∀ x ∈ P a, ∀ y, x ≤ y → y ∈ P a)
    (hclosed : ∀ a ∈ D, ∀ x, (∀ y, x < y → y ∈ P a) → x ∈ P a) :
    ∃ p : (Fin n → VF M) → Gamma M,
      (∀ a ∈ D, IsLeast (P a) (p a)) ∧ S.Definable LRV (vfGammaGraph D p) := by
  classical
  have hex (a : Fin n → VF M) (ha : a ∈ D) :=
    closed_upper_ray_has_least h00 _ _ (vfGammaFamily_fibre_definable hc D P hP a ha)
      (hne a ha) (hbounded a ha) (hup a ha) (hclosed a ha)
  let p (a : Fin n → VF M) := if ha : a ∈ D then (hex a ha).choose else 1
  have hp (a : Fin n → VF M) (ha : a ∈ D) : IsLeast (P a) (p a) := by
    simpa only [p,dite_eq_left ha] using (hex a ha).choose_spec
  exact ⟨p,hp,least_family_graph_definable D P hP p hp⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem bounded_partition_has_named_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (D : Set (Fin n → VF M)) (hD : S.Definable LRV (vfValues '' D))
    (hclosed : IsClosed D)
    (hbounded : ∃ γ : Gamma M, ∀ x ∈ D, ∀ i, γ.val ≤ vfValue (x i))
    (p : (Fin n → VF M) → Gamma M) (hp : IsOpenDiscPartition D p)
    (hgraph : S.Definable LRV (vfGammaGraph D p)) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ a ∈ D, p a ≤ δ := by
  by_cases hne : D.Nonempty
  · have hvalues : GammaParameters.GammaDefinableOverBase (⟨S,∅⟩ : ParameterBase M) (p '' D) := by
      apply (gamma_real_codes_iff hc S _).mpr
      rw [← vfGammaGraph_image_codes D p]
      exact hgraph.image_comp Sum.inr
    obtain ⟨δ,hδ,hδdef⟩ := gamma_definable_supremum h00 _ _ hvalues (hne.image p)
      (lemma_2_53_vf h00 hc hκ hs hv D hD hclosed hbounded p hp hgraph).2
    exact ⟨δ,(gamma_real_codes_iff hc S _).mp hδdef,fun a ha => hδ.1 ⟨a,ha,rfl⟩⟩
  · refine ⟨1,?_,fun a ha => False.elim (hne ⟨a,ha⟩)⟩
    apply (gamma_real_codes_iff hc S _).mp
    exact GammaParameters.real_definableAtBase (⟨S,∅⟩ : ParameterBase M) .rv _
      (GammaSyntax.one_definable S)

end DiamondIntegral.Section6
