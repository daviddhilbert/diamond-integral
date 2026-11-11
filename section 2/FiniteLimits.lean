import «section 2».FiniteBranchLimits
import Section9.LimitDefinability

/-!
# Lemma 2.45: finite affine limits in a closed bounded target

The checked prequel theorem first gives a same-base finite projective limit.
A finite valuative range bound excludes every infinite coordinate. The
resulting affine limit is minimal and ground-definable; closedness places it
in the target. The arbitrary finite VF output arity is kept explicit.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem HasMinimalLimitSet.frequently_hits
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (hL : HasMinimalLimitSet A a f L) {b : Fin m → VF M} (hb : b ∈ L)
    (ε δ : Gamma M) :
    ∃ x ∈ A \ {a}, x ∈ vfBall a δ ∧ ∃ y ∈ f x, y ∈ vfBall b ε := by
  classical
  by_contra hn
  have hproper : L \ {b} ⊂ L := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
    intro he
    have h : b ∈ L \ {b} := he.symm ▸ hb
    exact h.2 rfl
  apply hL.2 _ hproper
  intro ε'
  obtain ⟨δ', hδ'⟩ := hL.1 (max ε ε')
  refine ⟨max δ δ', fun x hx hnear y hy => ?_⟩
  obtain ⟨c, hc, hyc⟩ := hδ' x hx (vfBall_anti (le_max_right _ _) hnear) y hy
  refine ⟨c, ⟨hc, ?_⟩, vfBall_anti (le_max_right _ _) hyc⟩
  intro he
  subst c
  exact hn ⟨x, hx, vfBall_anti (le_max_left _ _) hnear,
    y, hy, vfBall_anti (le_max_left _ _) hyc⟩

theorem HasLimitSet.nonempty_of_frequent_values
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (hL : HasLimitSet A a f L)
    (hvalues : ∀ δ : Gamma M, ∃ x ∈ A \ {a}, x ∈ vfBall a δ ∧ (f x).Nonempty) :
    L.Nonempty := by
  obtain ⟨δ, hδ⟩ := hL 1
  obtain ⟨x, hx, hnear, y, hy⟩ := hvalues δ
  obtain ⟨b, hb, _⟩ := hδ x hx hnear y hy
  exact ⟨b, hb⟩

private theorem affine_minimal_of_bounded_projective
    (A : Set (Fin 1 → VF M)) (f : (Fin 1 → VF M) → Set (Fin m → VF M))
    (L : Set (Fin m → LimitPoint M)) (hL : IsMinimalLimitSet A 0 f L)
    (hfin : L.Finite) (hbound : BoundedVFRange A f) :
    ∃ K : Set (Fin m → VF M), K.Finite ∧ finiteLimitPoint '' K = L ∧
      HasMinimalLimitSet A 0 f K := by
  have hfinite (b : Fin m → LimitPoint M) (hb : b ∈ L) (i : Fin m) : b i ≠ none := by
    intro hi
    obtain ⟨γ, hγ⟩ := hbound
    obtain ⟨x, hx, _, y, hy, hyb⟩ := hL.frequently_hits hb γ⁻¹ 1
    have hinf := hyb i
    rw [hi] at hinf
    change vfValue (y i) < (γ⁻¹⁻¹).val at hinf
    have hlt : vfValue (y i) < γ.val := by
      simpa only [inv_inv] using hinf
    exact (not_lt_of_ge (hγ x hx.1 y hy i)) hlt
  let K : Set (Fin m → VF M) := {b | finiteLimitPoint b ∈ L}
  have hKfin : K.Finite := hfin.preimage finiteLimitPoint_injective.injOn
  have himage : finiteLimitPoint '' K = L := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hb
      let c : Fin m → VF M := fun i => (b i).getD 0
      have he : finiteLimitPoint c = b := by
        funext i
        cases hi : b i with
        | none => exact (hfinite b hb i hi).elim
        | some y => simp only [finiteLimitPoint, c, hi, Option.getD_some]
      exact ⟨c, by change finiteLimitPoint c ∈ L; rwa [he], he⟩
  refine ⟨K, hKfin, himage, ?_⟩
  have hKL : HasLimitSet A 0 f K := by
    apply (hasLimitSet_iff_companion A 0 f K).mpr
    change IsLimitSet A 0 f (finiteLimitPoint '' K)
    rw [himage]
    exact hL.1
  refine ⟨hKL, fun U hU hlim => ?_⟩
  have hproper : finiteLimitPoint '' U ⊂ L := by
    rw [← himage]
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hU.1, ?_⟩
    intro he
    obtain ⟨b, hb, hbU⟩ := Set.exists_of_ssubset hU
    have hbimage : finiteLimitPoint b ∈ finiteLimitPoint '' U := he.symm ▸ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hcb⟩ := hbimage
    have hcb' : c = b := finiteLimitPoint_injective hcb
    exact hbU (hcb' ▸ hc)
  exact hL.2 _ hproper ((hasLimitSet_iff_companion A 0 f U).mp hlim)

/-- The real-base finite affine-limit theorem, with arbitrary finite output
arity. The full graph is defined over exactly S. -/
theorem exists_finite_affine_limit
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin 1 → VF M)) (f : (Fin 1 → VF M) → Set (Fin m → VF M))
    (hG : S.Definable LRV (unaryLimitGraph A f)) (hfin : ∀ x ∈ A, (f x).Finite)
    (hbound : BoundedVFRange A f) :
    ∃ L : Set (Fin m → VF M), L.Finite ∧ HasMinimalLimitSet A 0 f L ∧
      S.Definable LRV (vfValues '' L) := by
  obtain ⟨K, hKfin, hK, hKdef⟩ := SpecialTransformations.Section9.lemma_9_5
    hc hs hsmall A f hG hfin
  obtain ⟨L, hLfin, himage, hL⟩ := affine_minimal_of_bounded_projective A f K hK hKfin hbound
  refine ⟨L, hLfin, hL, ?_⟩
  have he : {b : Fin m → VF M | finiteLimitPoint b ∈ K} = L := by
    rw [← himage]
    ext b
    constructor
    · rintro ⟨c, hc, hcb⟩
      have he : c = b := finiteLimitPoint_injective hcb
      exact he ▸ hc
    · intro hb
      exact ⟨b, hb, rfl⟩
  have hdef := hKdef (fun _ : Fin m => true)
  change S.Definable LRV (vfValues '' {b : Fin m → VF M | finiteLimitPoint b ∈ K}) at hdef
  rwa [he] at hdef

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem HasMinimalLimitSet.subset_closed
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Set (Fin m → VF M)} {L C : Set (Fin m → VF M)}
    (hL : HasMinimalLimitSet A a f L) (hC : IsClosed C)
    (hvalues : ∀ x ∈ A, f x ⊆ C) : L ⊆ C := by
  intro b hb
  have hcl : b ∈ vfClosure C := by
    intro ε
    obtain ⟨x, hx, _, y, hy, hyb⟩ := hL.frequently_hits hb ε 1
    exact ⟨y, hvalues x hx.1 hy, hyb⟩
  rw [vfClosure_eq_closure hv C, hC.closure_eq] at hcl
  exact hcl

/-- Lemma 2.45 over a real ground base. The domain is any unary VF set,
so the stated punctured maximal-ideal domain is included. A finite limit is
closed in the valuation topology, giving the manuscript's limit equality. -/
theorem lemma_2_45
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin 1 → VF M)) (f : (Fin 1 → VF M) → Set (Fin m → VF M))
    (C : Set (Fin m → VF M)) (hC : IsClosed C)
    (hbounded : ∃ γ : Gamma M, ∀ y ∈ C, ∀ i, γ.val ≤ vfValue (y i))
    (hG : S.Definable LRV (unaryLimitGraph A f)) (hfin : ∀ x ∈ A, (f x).Finite)
    (hvalues : ∀ x ∈ A, f x ⊆ C) :
    ∃ L : Set (Fin m → VF M), L.Finite ∧ L ⊆ C ∧ HasMinimalLimitSet A 0 f L ∧
      S.Definable LRV (vfValues '' L) := by
  obtain ⟨γ, hγ⟩ := hbounded
  have hb : BoundedVFRange A f := ⟨γ, fun x hx y hy i => hγ y (hvalues x hx hy) i⟩
  obtain ⟨L, hLfin, hL, hLdef⟩ := exists_finite_affine_limit hc hs hsmall A f hG hfin hb
  exact ⟨L, hLfin, hL.subset_closed hv hC hvalues, hL, hLdef⟩

end DiamondIntegral.Section2
