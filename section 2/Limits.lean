import «section 2».Boundedness
import Section9.LimitTopology

/-!
# Definition 2.42 and Lemma 2.43: affine limit sets

The approved local definition uses the whole candidate limit set and a
punctured source neighbourhood. Its exact formula agrees with the companion
library's finite-point limit predicate. No point at infinity is introduced
in this interface. Finite candidate limit sets imply local boundedness.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def HasLimitSet (A : Set (Fin n → VF M)) (a : Fin n → VF M)
    (f : (Fin n → VF M) → Set (Fin m → VF M)) (L : Set (Fin m → VF M)) : Prop :=
  ∀ ε : Gamma M, ∃ δ : Gamma M, ∀ x ∈ A \ {a}, x ∈ vfBall a δ →
    ∀ y ∈ f x, ∃ b ∈ L, y ∈ vfBall b ε

def HasMinimalLimitSet (A : Set (Fin n → VF M)) (a : Fin n → VF M)
    (f : (Fin n → VF M) → Set (Fin m → VF M)) (L : Set (Fin m → VF M)) : Prop :=
  HasLimitSet A a f L ∧ ∀ K ⊂ L, ¬ HasLimitSet A a f K

theorem hasLimitSet_iff_companion (A : Set (Fin n → VF M)) (a : Fin n → VF M)
    (f : (Fin n → VF M) → Set (Fin m → VF M)) (L : Set (Fin m → VF M)) :
    HasLimitSet A a f L ↔ IsVFLimitSet A a f L :=
  (isVFLimitSet_iff A a f L).symm

/-- The original optional subfamily is logically redundant, including
empty values and empty candidate limit sets. -/
theorem hasLimitSet_iff_subfamily (A : Set (Fin n → VF M)) (a : Fin n → VF M)
    (f : (Fin n → VF M) → Set (Fin m → VF M)) (L : Set (Fin m → VF M)) :
    HasLimitSet A a f L ↔
      ∀ ε : Gamma M, ∃ δ : Gamma M, ∀ x ∈ A \ {a}, x ∈ vfBall a δ →
        ∃ K : Set (Fin m → VF M), K ⊆ L ∧
          ∀ y ∈ f x, ∃ b ∈ K, y ∈ vfBall b ε := by
  constructor
  · intro h ε
    obtain ⟨δ, hδ⟩ := h ε
    exact ⟨δ, fun x hx hnear => ⟨L, Set.Subset.refl L, hδ x hx hnear⟩⟩
  · intro h ε
    obtain ⟨δ, hδ⟩ := h ε
    refine ⟨δ, fun x hx hnear y hy => ?_⟩
    obtain ⟨K, hKL, hK⟩ := hδ x hx hnear
    obtain ⟨b, hb, hball⟩ := hK y hy
    exact ⟨b, hKL hb, hball⟩

theorem hasMinimalLimitSet_iff_companion
    (A : Set (Fin n → VF M)) (a : Fin n → VF M)
    (f : (Fin n → VF M) → Set (Fin m → VF M)) (L : Set (Fin m → VF M)) :
    HasMinimalLimitSet A a f L ↔ IsMinimalVFLimitSet A a f L := by
  constructor
  · rintro ⟨hL, hmin⟩
    exact ⟨(hasLimitSet_iff_companion A a f L).mp hL,
      fun K hK hk => hmin K hK ((hasLimitSet_iff_companion A a f K).mpr hk)⟩
  · rintro ⟨hL, hmin⟩
    exact ⟨(hasLimitSet_iff_companion A a f L).mpr hL,
      fun K hK hk => hmin K hK ((hasLimitSet_iff_companion A a f K).mp hk)⟩

theorem HasMinimalLimitSet.isolated
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (hL : HasMinimalLimitSet A a f L) {b : Fin m → VF M} (hb : b ∈ L) :
    ∃ ε : Gamma M, ∀ c ∈ L \ {b}, c ∉ vfBall b ε :=
  ((hasMinimalLimitSet_iff_companion A a f L).mp hL).isolated hb

theorem lemma_2_43 {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Set (Fin m → VF M)} {L K : Set (Fin m → VF M)}
    (hL : HasMinimalLimitSet A a f L) (hK : HasMinimalLimitSet A a f K) :
    closure L = closure K :=
  lemma_9_2_topological hv ((hasMinimalLimitSet_iff_companion A a f L).mp hL)
    ((hasMinimalLimitSet_iff_companion A a f K).mp hK)

def BoundedVFRange (A : Set (Fin n → VF M))
    (f : (Fin n → VF M) → Set (Fin m → VF M)) : Prop :=
  ∃ γ : Gamma M, ∀ x ∈ A, ∀ y ∈ f x, ∀ i, γ.val ≤ vfValue (y i)

private theorem finite_centres_bound (L : Set (Fin m → VF M)) (hL : L.Finite)
    (ε : Gamma M) : ∃ γ : Gamma M, γ.val ≤ ε.val ∧
      ∀ b ∈ L, ∀ i, γ.val ≤ vfValue (b i) := by
  classical
  let F : Finset (GammaInfinity M) :=
    insert ε.val (hL.toFinset.biUnion (fun b => Finset.univ.image (fun i => vfValue (b i))))
  have hF : F.Nonempty := ⟨ε.val, Finset.mem_insert_self _ _⟩
  have hle : F.min' hF ≤ ε.val := F.min'_le _ (Finset.mem_insert_self _ _)
  have hfin : F.min' hF ≠ Values.infinity := by
    intro he
    rw [he] at hle
    exact ε.property (le_antisymm (Values.le_infinity _) hle)
  refine ⟨⟨F.min' hF, hfin⟩, hle, fun b hb i => ?_⟩
  apply F.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨b, hL.mem_toFinset.mpr hb, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

/-- A finite affine limit set already supplies the local boundedness
needed in the approved R038 clarification. No definability is needed. -/
theorem HasLimitSet.finite_locally_bounded
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (hL : HasLimitSet A a f L) (hfin : L.Finite) :
    ∃ δ : Gamma M, BoundedVFRange ((vfBall a δ ∩ A) \ {a}) f := by
  obtain ⟨δ, hδ⟩ := hL 1
  obtain ⟨γ, hγε, hγL⟩ := finite_centres_bound L hfin 1
  refine ⟨δ, γ, fun x hx y hy i => ?_⟩
  obtain ⟨b, hb, hnear⟩ := hδ x ⟨hx.1.2, hx.2⟩ hx.1.1 y hy
  have hv := vfValue_min_le_sub (y i - b i) (-b i)
  rw [show (y i - b i) - (-b i) = y i by abel, vfValue_neg] at hv
  exact (le_min (hγε.trans (hnear i).le) (hγL b hb i)).trans hv

/-- With no source coordinates, puncturing removes the only possible point. -/
theorem hasLimitSet_empty_zero_arity (A : Set (Fin 0 → VF M)) (a : Fin 0 → VF M)
    (f : (Fin 0 → VF M) → Set (Fin m → VF M)) : HasLimitSet A a f ∅ := by
  intro ε
  refine ⟨1, fun x hx _ => ?_⟩
  exact (hx.2 (Subsingleton.elim x a)).elim

theorem not_hasMinimalLimitSet_zero_arity (A : Set (Fin 0 → VF M)) (a : Fin 0 → VF M)
    (f : (Fin 0 → VF M) → Set (Fin m → VF M)) (L : Set (Fin m → VF M))
    (hne : L.Nonempty) : ¬ HasMinimalLimitSet A a f L := by
  intro hL
  exact hL.2 ∅ (Set.empty_ssubset.mpr hne) (hasLimitSet_empty_zero_arity A a f)

end DiamondIntegral.Section2
