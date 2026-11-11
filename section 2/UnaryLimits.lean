import «section 2».FiniteLimits
import Section9.LimitCardinality
import Section8.GammaRadiusBase

/-!
# Finite limits of unary single-valued maps

The prequel cardinality theorem applies to the actual full VF graph. A
finite minimal affine limit has no more elements than a uniform bound for
the fibres. A bounded unary function therefore has a same-base singleton
limit whenever its punctured domain accumulates at the origin.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem HasMinimalLimitSet.to_projective
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (hL : HasMinimalLimitSet A a f L) :
    IsMinimalLimitSet A a f (finiteLimitPoint '' L) := by
  refine ⟨(hasLimitSet_iff_companion A a f L).mp hL.1, ?_⟩
  intro K hK hlim
  let U := finiteLimitPoint ⁻¹' K
  have himage : finiteLimitPoint '' U = K :=
    Set.image_preimage_eq_of_subset (hK.1.trans (Set.image_subset_range _ _))
  have hUL : U ⊆ L := by
    intro b hb
    obtain ⟨c, hc, hcb⟩ := hK.1 hb
    exact finiteLimitPoint_injective hcb ▸ hc
  have hproper : U ⊂ L := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hUL, ?_⟩
    intro he
    exact hK.ne (himage.symm.trans (congrArg (Set.image finiteLimitPoint) he))
  apply hL.2 U hproper
  apply (hasLimitSet_iff_companion A a f U).mpr
  change IsLimitSet A a f (finiteLimitPoint '' U)
  rw [himage]
  exact hlim

theorem HasMinimalLimitSet.card_le
    (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {A : Set (Fin 1 → VF M)} {a : Fin 1 → VF M}
    {f : (Fin 1 → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)} {k : ℕ}
    (hG : S.Definable LRV (unaryLimitGraph A f))
    (hfin : ∀ x ∈ A, (f x).Finite) (hk : ∀ x ∈ A, (f x).ncard ≤ k)
    (hL : HasMinimalLimitSet A a f L) (hLf : L.Finite) : L.ncard ≤ k := by
  have hGN : @Set.Definable M (Set.univ : Set M) LRV
      (CanonicalStructure.normalize (M := M)) (Fin 1 ⊕ Fin m) (unaryLimitGraph A f) := by
    rw [normalize_eq_of_isCanonical hc]
    exact hG.mono (Set.subset_univ S)
  have h := lemma_9_4 hGN hfin hk hL.to_projective (hLf.image finiteLimitPoint)
  rwa [Set.ncard_image_of_injective L finiteLimitPoint_injective] at h

/-- The singleton limit used at the start of the weak-concentricity proof.
The full graph and the resulting singleton are definable over exactly S;
the actual domain need only accumulate puncturedly at zero. -/
theorem exists_singleton_affine_limit
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin 1 → VF M)) (F : (Fin 1 → VF M) → Fin m → VF M)
    (hG : S.Definable LRV (unaryLimitGraph A (fun x => {F x})))
    (hbound : BoundedVFRange A (fun x => {F x}))
    (hacc : ∀ δ : Gamma M, ∃ x ∈ A \ {(0 : Fin 1 → VF M)}, x ∈ vfBall 0 δ) :
    ∃ b : Fin m → VF M, HasMinimalLimitSet A 0 (fun x => {F x}) {b} ∧
      S.Definable LRV (vfValues '' {b}) := by
  obtain ⟨L, hLf, hL, hLdef⟩ := exists_finite_affine_limit hc hs hsmall A
    (fun x => {F x}) hG (fun x _ => Set.finite_singleton _) hbound
  have hcard : L.ncard ≤ 1 := hL.card_le hc hG
    (fun x _ => Set.finite_singleton _) (fun x _ => by simp only [Set.ncard_singleton]; rfl) hLf
  have hne : L.Nonempty := hL.1.nonempty_of_frequent_values (fun δ => by
    obtain ⟨x, hx, hnear⟩ := hacc δ
    exact ⟨x, hx, hnear, Set.singleton_nonempty _⟩)
  have hone : L.ncard = 1 := by
    have hpos := (Set.ncard_pos hLf).mpr hne
    omega
  obtain ⟨b, rfl⟩ := Set.ncard_eq_one.mp hone
  exact ⟨b, hL, hLdef⟩

end DiamondIntegral.Section2
