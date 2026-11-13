import «section 4».Section3GammaFamilyClasses
import «section 3».GammaGroundMeasuredGammaPartitions
import «section 3».GammaGroundGammaGradedComparison
import «section 3».GammaGroundMeasuredGammaGradedComparison
import «section 3».CompletionEquivalences

/-! Actual native Gamma cut relations give additive maps from the
categorical completions to chart rings. No cancellation is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3GammaChartAddMaps
open Section3GammaFamilyClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

@[simp] theorem ordinary_empty (k : ℕ) : ordinaryValue (GammaGroundGammaObject.empty hc B k) = 0 := by
  simp only [ordinaryValue, GammaOrdinaryFiniteFamilies.familyClass, GammaGroundGammaObject.empty,
    Finset.univ_eq_empty, Finset.sum_empty]
@[simp] theorem measured_empty (k : ℕ) : measuredValue (GammaGroundMeasuredGammaObject.empty hc B k) = 0 := by
  simp only [measuredValue, GammaRVFiniteFamilies.familyClass, GammaGroundMeasuredGammaObject.empty,
    GammaGroundGammaObject.empty, Finset.univ_eq_empty, Finset.sum_empty]

theorem cut_cover {n : ℕ} (U : GammaGroundGammaObject hc B n)
    (X : Fin U.tags → GammaGroundGammaPiece hc B n) (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) (i : Fin U.tags) :
    ((X i).union ((U.difference X) i)).carrier = (U.piece i).carrier := by
  ext t
  change (t ∈ (X i).carrier ∨ t ∈ (U.piece i).carrier ∧ t ∉ (X i).carrier) ↔ t ∈ (U.piece i).carrier
  exact ⟨fun h => h.elim (fun hx => hX i hx) (fun h => h.1), fun h => by
    by_cases hx : t ∈ (X i).carrier
    · exact Or.inl hx
    · exact Or.inr ⟨h, hx⟩⟩

theorem ordinary_cut {n : ℕ} (U : GammaGroundGammaObject hc B n)
    (X : Fin U.tags → GammaGroundGammaPiece hc B n) (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    ordinaryValue (U.restrict X) + ordinaryValue (U.restrict (U.difference X)) = ordinaryValue U := by
  have h := ordinary_iso (gammaGroundGammaPartitionHom U X (U.difference X) hX (fun _ _ h => h.1)
    (fun _ => Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)) (cut_cover U X hX))
  rw [ordinary_coprod] at h
  exact h

theorem measured_cut {n : ℕ} (U : GammaGroundMeasuredGammaObject hc B n)
    (X : Fin U.underlying.tags → GammaGroundGammaPiece hc B n)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier) :
    measuredValue (U.restrict X hX) + measuredValue (U.restrict (U.underlying.difference X) (fun _ _ h => h.1)) = measuredValue U := by
  have h := measured_iso (gammaGroundMeasuredGammaPartitionHom U X (U.underlying.difference X) hX (fun _ _ h => h.1)
    (fun _ => Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)) (cut_cover U.underlying X hX))
  rw [measured_coprod] at h
  exact h

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundGammaPresentation hc B k) (A := GammaOrdinaryRing.Ring B) where
  toFun := ordinaryValue
  iso h := by obtain ⟨e⟩ := h; exact ordinary_iso e.hom
  empty := ordinary_empty k
  scissor h := by
    obtain ⟨U, X, hX, hA, hD, hE, hF⟩ := h
    rw [hA, hD, hE, hF, ordinary_empty, add_zero]
    exact ordinary_cut U X hX

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundMeasuredGammaPresentation hc B k) (A := GammaRVChartPresentation.ChartRing B) where
  toFun := measuredValue
  iso h := by obtain ⟨e⟩ := h; exact measured_iso e.hom
  empty := measured_empty k
  scissor h := by
    obtain ⟨U, X, hX, hA, hD, hE, hF⟩ := h
    rw [hA, hD, hE, hF, measured_empty, add_zero]
    exact measured_cut U X hX

def ordinaryComponent (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    GammaGroundGammaKPlus hc B k →+ GammaOrdinaryRing.Ring B := PositiveAdditiveGrothendieck.lift _ (ordinaryInvariant hc B k)
def measuredComponent (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    GammaGroundMeasuredGammaKPlus hc B k →+ GammaRVChartPresentation.ChartRing B := PositiveAdditiveGrothendieck.lift _ (measuredInvariant hc B k)

theorem ordinaryComponent_class {n : ℕ} (U : GammaGroundGammaObject hc B n) :
    ordinaryComponent hc B n (gammaGroundGammaClass U) = ordinaryValue U := PositiveAdditiveGrothendieck.lift_of _ _ _
theorem measuredComponent_class {n : ℕ} (U : GammaGroundMeasuredGammaObject hc B n) :
    measuredComponent hc B n (gammaGroundMeasuredGammaClass U) = measuredValue U := PositiveAdditiveGrothendieck.lift_of _ _ _

def ordinaryDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundGammaDirectSum hc B →+ GammaOrdinaryRing.Ring B := DirectSum.toAddMonoid (ordinaryComponent hc B)
def measuredDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundMeasuredGammaDirectSum hc B →+ GammaRVChartPresentation.ChartRing B := DirectSum.toAddMonoid (measuredComponent hc B)

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundGammaGrothendieckRing hc B →+ GammaOrdinaryRing.Ring B :=
  (lift (ordinaryDirectSum hc B)).comp
    (ringCompletionCongr (gammaGroundGammaSemiringEquivDirectSum (hc := hc) (ground := B))).toAddEquiv.toAddMonoidHom
def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundMeasuredGammaGrothendieckRing hc B →+ GammaRVChartPresentation.ChartRing B :=
  (lift (measuredDirectSum hc B)).comp
    (ringCompletionCongr (gammaGroundMeasuredGammaSemiringEquivDirectSum (hc := hc) (ground := B))).toAddEquiv.toAddMonoidHom

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {n : ℕ} (U : GammaGroundGammaObject hc B n) : ordinary hc B (of (gammaGroundGammaSemiringClass U)) = ordinaryValue U := by
  change lift (ordinaryDirectSum hc B) (ringCompletionCongr _ (of (gammaGroundGammaSemiringClass U))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundGammaPresentationToDirectSum_class]
  rw [lift_apply_of, ordinaryDirectSum, gammaGroundGammaDirectSumClass, DirectSum.toAddMonoid_of, ordinaryComponent_class]

theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {n : ℕ} (U : GammaGroundMeasuredGammaObject hc B n) : measured hc B (of (gammaGroundMeasuredGammaSemiringClass U)) = measuredValue U := by
  change lift (measuredDirectSum hc B) (ringCompletionCongr _ (of (gammaGroundMeasuredGammaSemiringClass U))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundMeasuredGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundMeasuredGammaPresentationToDirectSum_class]
  rw [lift_apply_of, measuredDirectSum, gammaGroundMeasuredGammaDirectSumClass, DirectSum.toAddMonoid_of, measuredComponent_class]

end DiamondIntegral.Section4.Section3GammaChartAddMaps
