import «section 5».ElementaryRESRestrictionRing
import «section 5».ElementaryValueFibreDescent
import «section 4».RESDimensionFreeReduction

/-! The actual elementary restriction descends to the intrinsic reduced
ungraded RES ring, since every definable full value fibre descends over
the same named coefficient field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M)
local notation "Bₙ" => EmptyGammaGround.base (Set.range (e ∘ c))
local notation "Bₘ" => EmptyGammaGround.base (Set.range c)

theorem elementaryRESChartValue_fibre (α : Values.Gamma (M := N))
    (hα : GammaDefinableClosureAtBase Bₙ α) (β : Values.Gamma (M := M))
    (hβ : GammaDefinableClosureAtBase Bₘ β) (he : elementaryGammaTopMap e β.val = α.val) :
    elementaryRESChartValue hcM hcN e c
      (RESFibreObjects.fibre Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ)) =
    RESDimensionFreeRing.objectClass
      (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ)) := by
  let V := Section3RVChartBridge.nativeRES hcM
    (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ))
  have h := nativeUngradedClass_bijection hcM
    (elementaryNativeRESRestriction hcM hcN e c (Section3RVChartBridge.nativeRES hcN
      (RESFibreObjects.fibre Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ)))) V
    (GammaGroundBijection.ofCarrierEq (by
      apply Set.ext
      intro (x : Fin 1 → CanonicalRV.RVSort M)
      change (e ∘ rvValues x ∈ rawDomain (ofRaw (hc := hcN)
          (RESFibreObjects.fibre Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ)).domain
          (RESFibreObjects.fibre Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ)).domain_definable)) ↔
        rvValues x ∈ (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ)).domain
      rw [rawDomain_ofRaw,fibre_domain_eq_full,fibre_domain_eq_full]
      exact elementary_full_fibre_preimage e α β he (rvValues x)))
  refine h.trans ?_
  change RESDimensionFreeRing.objectClass (Section3RVChartBridge.chartRES V) = _
  exact RESDimensionFreeRing.objectClass_iso _ _
    (RVUnderlyingIsomorphisms.ofFixed (Section3RVRoundtripBridge.chart_native _))

def elementaryRESOrdinaryReducedRestriction : RESOrdinaryRing.Ring Bₙ →+* RESDimensionFreeReduction.Ring Bₘ :=
  (RESDimensionFreeReduction.quotient Bₘ).comp (elementaryRESOrdinaryRestriction hcM hcN e c)

theorem elementaryRESRestriction_kills_fibres : RESOrdinaryReduction.fibreIdeal Bₙ ≤
    RingHom.ker (elementaryRESOrdinaryReducedRestriction hcM hcN e c) := by
  apply Ideal.span_le.mpr
  rintro x ⟨α,hα,rfl⟩
  obtain ⟨β,hβ,he,_⟩ := elementary_definable_value_descent hcM hcN e c α hα
  change elementaryRESOrdinaryReducedRestriction hcM hcN e c (_ - _) = 0
  rw [map_sub]
  change RESDimensionFreeReduction.quotient Bₘ
    (elementaryRESOrdinaryRestriction hcM hcN e c (RESOrdinaryRing.objectClass _)) -
    RESDimensionFreeReduction.quotient Bₘ
    (elementaryRESOrdinaryRestriction hcM hcN e c (RESOrdinaryRing.objectClass _)) = 0
  simp only [RESFibreObjects.torus]
  rw [elementaryRESOrdinaryRestriction_class,elementaryRESOrdinaryRestriction_class,
    elementaryRESChartValue_fibre hcM hcN e c α hα β hβ he,
    elementaryRESChartValue_fibre hcM hcN e c 1 (GammaGroupNames.one_definable_base Bₙ)
      1 (GammaGroupNames.one_definable_base Bₘ) (elementaryGammaTopMap_one e)]
  change RESDimensionFreeReduction.fromOrdinary Bₘ (RESOrdinaryRing.objectClass _) -
    RESDimensionFreeReduction.fromOrdinary Bₘ (RESOrdinaryRing.objectClass _) = 0
  exact sub_eq_zero.mpr (congrArg (RESDimensionFreeReduction.fromGradedReduced Bₘ)
    (RESOrdinaryReduction.fibre_class Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ)))

def elementaryRESUngradedReduced : RESDimensionFreeRing.Ring Bₙ →+* RESDimensionFreeReduction.Ring Bₘ :=
  (RESDimensionFreeReduction.quotient Bₘ).comp (elementaryRESUngradedRestriction hcM hcN e c)

theorem elementaryRESUngradedReduced_kills_fibres : RESDimensionFreeReduction.fibreIdeal Bₙ ≤
    RingHom.ker (elementaryRESUngradedReduced hcM hcN e c) := by
  apply Ideal.map_le_iff_le_comap.mpr
  exact elementaryRESRestriction_kills_fibres hcM hcN e c

def elementaryRESReducedRestriction : RESDimensionFreeReduction.Ring Bₙ →+* RESDimensionFreeReduction.Ring Bₘ :=
  Ideal.Quotient.lift (RESDimensionFreeReduction.fibreIdeal Bₙ) (elementaryRESUngradedReduced hcM hcN e c)
    (fun _ h => elementaryRESUngradedReduced_kills_fibres hcM hcN e c h)

end DiamondIntegral.Section5
