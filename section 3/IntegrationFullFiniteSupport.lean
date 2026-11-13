import «section 3».IntegrationDiscBases
import IntegrationSection3ACVF.CompleteTypeBallAtomicity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Finite real support retains every old imaginary. The checked [18]
small-real-base ball theorem can therefore decide each cut separately over
an arbitrary original real base. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationFullFiniteRealSupport (B : FullBaseAtomicity.Base (M := M))
    {α : Type} [Finite α] (A : Set (α → M)) (hA : FullBaseAtomicity.OverBase B A) :
    ∃ F : Finset M, (F : Set M) ⊆ B.real ∧
      FullBaseAtomicity.OverBase (⟨(F : Set M),B.imaginary⟩ : FullBaseAtomicity.Base (M := M)) A := by
  obtain ⟨G,hG,R,hR,hRA⟩ := hA
  letI := CanonicalStructure.normalize (M := M)
  obtain ⟨F,hFB,hRF⟩ := Set.definable_iff_finitely_definable.mp hR
  exact ⟨F,hFB,G,hG,R,hRF,hRA⟩

theorem integrationFullCompleteType_restrict {B C : FullBaseAtomicity.Base (M := M)}
    {A : Set M} (hA : FullBallCoset.CompleteType C A)
    (hr : B.real ⊆ C.real) (hi : B.imaginary ⊆ C.imaginary) : FullBallCoset.CompleteType B A := by
  intro T hT
  exact hA T (FullBaseAtomicity.OverBase.mono hT hr hi)

theorem integrationEmpty_small {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.mk (∅ : Set M) < κ := by
  simpa using (Cardinal.aleph0_pos.trans_le hκ)

theorem integrationFinset_small {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (F : Finset M) :
    Cardinal.mk (F : Set M) < κ := by
  have h := small_union_finite hκ (∅ : Set M) (integrationEmpty_small (M := M) hκ)
    (F : Set M) F.finite_toSet
  simpa only [Set.empty_union] using h

/-- Each cut has finite real support. Thus the checked small-base ball
atomicity theorem gives the same conclusion over any real parameter set,
with every old imaginary retained. -/
theorem integrationFullBallAtomicity {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M)) (ρ : Values.Gamma (M := M)) (hρ : 1 < ρ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (D : BallImaginaries.Ball M) (hsub : BallImaginaries.underlying D ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl D)) (BallImaginaries.underlying D) := by
  let C : FullBaseAtomicity.Base (M := M) := ⟨∅,B.imaginary⟩
  have hc : FullBallCoset.CompleteType C A :=
    integrationFullCompleteType_restrict hA (Set.empty_subset _) Set.Subset.rfl
  have hd := CompleteTypeBallAtomicity.lemma_3_4 hκ hs C (integrationEmpty_small (M := M) hκ)
    h00 ρ hρ hc D hsub
  refine ⟨FullBaseAtomicity.OverBase.mono hd.1 (Set.empty_subset _) Set.Subset.rfl,?_⟩
  intro U hU
  obtain ⟨F,hF,hUF⟩ := integrationFullFiniteRealSupport (B.adjoin (Sum.inl D)) {z : Fin 1 → M | z 0 ∈ U} hU
  let E : FullBaseAtomicity.Base (M := M) := ⟨(F : Set M),B.imaginary⟩
  have he : FullBallCoset.CompleteType E A :=
    integrationFullCompleteType_restrict hA hF Set.Subset.rfl
  have hb := CompleteTypeBallAtomicity.lemma_3_4 hκ hs E (integrationFinset_small (M := M) hκ F)
    h00 ρ hρ he D hsub
  exact hb.2 U hUF
end DiamondIntegral.Section3
