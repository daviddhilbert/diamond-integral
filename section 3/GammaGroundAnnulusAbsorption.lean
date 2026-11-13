import «section 3».GammaGroundTails
import «section 3».GammaNativeFinitePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- The positive tail splits into the half-open bounded annulus and
the translated tail, before any additive completion. -/
theorem gammaGroundGammaTail_positive_partition (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (hpos : 1 ≤ δ) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaAnnulus (hc := hc) δ hδ)) +
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaTail δ hδ)) =
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaPositiveTail (hc := hc) (B := B))) := by
  symm
  apply gammaGroundGammaSemiringClass_native_partition
  · exact fun _ h => h.1
  · intro γ h
    exact lt_of_le_of_lt hpos h
  · apply Set.disjoint_left.mpr
    intro γ hA hT
    exact hA.2 hT
  · ext γ
    change Fin 1 → Values.Gamma (M := M) at γ
    symm
    change (1 < γ 0) ↔ ((1 < γ 0 ∧ ¬ δ < γ 0) ∨ δ < γ 0)
    constructor
    · intro h
      by_cases ht : δ < γ 0
      · exact Or.inr ht
      · exact Or.inl ⟨h,ht⟩
    · rintro (⟨h,_⟩ | h)
      · exact h
      · exact lt_of_le_of_lt hpos h

/-- The strongest conclusion needed in the positive semiring is an
absorption equality. No cancellation of a positive tail is asserted. -/
theorem gammaGroundGammaAnnulus_positive_absorption (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (hpos : 1 ≤ δ)
    (c : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace 1) {c})
    (hcval : rvUnitValueHom (c 0) = δ) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaAnnulus (hc := hc) δ hδ)) +
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaPositiveTail (hc := hc) (B := B))) =
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaPositiveTail (hc := hc) (B := B))) := by
  have ht := gammaGroundGammaSemiringClass_iso (asIso (gammaGroundGammaTailTranslation δ hδ c hcdef hcval))
  have hp := gammaGroundGammaTail_positive_partition (hc := hc) δ hδ hpos
  rw [← ht] at hp
  exact hp
end DiamondIntegral.Section3
