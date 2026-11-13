import «section 4».GammaHigherPushforward
import «section 4».GammaBijectiveRelations

/-! Actual function-valued profiles are invariant under a definable
bijection preserving the Gamma weight. This is the fibrewise invariance
needed before descent to the graded Grothendieck categories. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaProfileBijections
open GammaDefinableEuler GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaIndicators
open GammaHigherPushforward GammaBijectiveRelations GammaParameterExtension GammaBaseExtension
open FiniteTupleBlocks GammaIteratedIntegral EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem indicator_fibre_membership (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (a : Values.Gamma (M := M)) (u : Fin n → Values.Gamma (M := M)) :
    (fibreFamily B T hT (indicatorFamily B I hI) a).val u = 1 ↔ u ∈ I ∧ T u = a := by
  rw [fibreFamily_eval]
  change (if T u = a then (if u ∈ I then (1 : ℤ) else 0) else 0) = 1 ↔ _
  by_cases ht : T u = a <;> by_cases hi : u ∈ I <;> simp [ht, hi]

theorem indicator_fibre_eq_indicator (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (a : Values.Gamma (M := M)) :
    let F := fibreFamily B T hT (indicatorFamily B I hI) a
    F = indicatorFamily (withGamma B (Set.range ![a])) {u | F.val u = 1} (F.property.2 1) := by
  let F := fibreFamily B T hT (indicatorFamily B I hI) a
  have hb (u) : F.val u = 0 ∨ F.val u = 1 := by
    have hv := fibreFamily_eval B T hT (indicatorFamily B I hI) a u
    by_cases ht : T u = a <;> by_cases hi : u ∈ I
    · right; exact hv.trans (by simp [ht, indicatorFamily, hi])
    · left; exact hv.trans (by simp [ht, indicatorFamily, hi])
    · left; exact hv.trans (by simp [ht])
    · left; exact hv.trans (by simp [ht])
  change F = indicatorFamily (withGamma B (Set.range ![a])) {u | F.val u = 1} (F.property.2 1)
  apply Subtype.ext
  funext u
  have hind : (indicatorFamily (withGamma B (Set.range ![a])) {u | F.val u = 1}
      (F.property.2 1)).val u = if F.val u = 1 then 1 else 0 := by
    by_cases h : F.val u = 1 <;> simp [indicatorFamily, h]
  rw [hind]
  rcases hb u with h | h <;> simp [h]

theorem profile_bijOn (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J)
    (T : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (m + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (hU : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = U (Fin.tail z)})
    (φ : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hφ : GammaDefinable B (graphOn I φ)) (hbij : Set.BijOn φ I J)
    (hweight : ∀ u ∈ I, T u = U (φ u)) :
    pushforward h00 hκ hs B hr hγ k T hT (indicatorFamily B I hI) =
      pushforward h00 hκ hs B hr hγ k U hU (indicatorFamily B J hJ) := by
  apply Subtype.ext
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (pushforward h00 hκ hs B hr hγ k T hT (indicatorFamily B I hI)).val (toPaperGamma a) =
    (pushforward h00 hκ hs B hr hγ k U hU (indicatorFamily B J hJ)).val (toPaperGamma a)
  rw [pushforward_eval, pushforward_eval]
  let C := withGamma B (Set.range ![a])
  have hγC : Cardinal.mk C.gamma < κ := finite_gamma_extension_small hκ B hγ ![a]
  have hΓC : Section2.NontrivialDefinableGamma C := nontrivial_extend B (Set.range ![a]) hΓ
  let F := fibreFamily B T hT (indicatorFamily B I hI) a
  let G := fibreFamily B U hU (indicatorFamily B J hJ) a
  let IF : Set (Fin m → Values.Gamma (M := M)) := {u | F.val u = 1}
  let JF : Set (Fin n → Values.Gamma (M := M)) := {y | G.val y = 1}
  have hIF (u) : u ∈ IF ↔ u ∈ I ∧ T u = a := indicator_fibre_membership B I hI T hT a u
  have hJF (y) : y ∈ JF ↔ y ∈ J ∧ U y = a := indicator_fibre_membership B J hJ U hU a y
  have hbijF : Set.BijOn φ IF JF := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨huI, hTu⟩ := (hIF u).mp hu
      exact (hJF (φ u)).mpr ⟨hbij.mapsTo huI, (hweight u huI).symm.trans hTu⟩
    · intro u hu v hv he
      exact hbij.injOn ((hIF u).mp hu).1 ((hIF v).mp hv).1 he
    · intro y hy
      obtain ⟨hyJ, hUy⟩ := (hJF y).mp hy
      obtain ⟨u, hu, he⟩ := hbij.surjOn hyJ
      refine ⟨u, (hIF u).mpr ⟨hu, ?_⟩, he⟩
      exact (hweight u hu).trans ((congrArg U he).trans hUy)
  have hgraphF : GammaDefinable C (graphOn IF φ) := by
    have h := GammaRelationLogic.inter_definable_base C _ _
      (gammaRelation_extend B (Set.range ![a]) hφ)
      (GammaRelationLogic.preimage_definable_base C IF (F.property.2 1) (headIndex n m))
    convert h using 1
    ext z
    change (z ∘ headIndex n m ∈ IF ∧ φ (z ∘ headIndex n m) = z ∘ tailIndex n m) ↔
      (z ∘ headIndex n m ∈ I ∧ φ (z ∘ headIndex n m) = z ∘ tailIndex n m) ∧ z ∘ headIndex n m ∈ IF
    constructor
    · rintro ⟨hu, he⟩
      exact ⟨⟨((hIF _).mp hu).1, he⟩, hu⟩
    · rintro ⟨⟨_, he⟩, hu⟩
      exact ⟨hu, he⟩
  have h := integrateAll_bijOn h00 linear hκ hs C hr hγC hΓC k n m
    IF (F.property.2 1) JF (G.property.2 1) φ hgraphF hbijF
  rw [← indicator_fibre_eq_indicator B I hI T hT a, ← indicator_fibre_eq_indicator B J hJ U hU a] at h
  exact h

end DiamondIntegral.Section4.GammaProfileBijections
