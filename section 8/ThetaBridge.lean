import «section 8».HmCharts
import FubiniTheorems.Fubini.InflatedFamilyFubiniVol
import FubiniTheorems.Comparison.RESSetOperations

/-! `Θ` of an ambient RES chart is `Θ` of its concrete trace.

For an RES chart `C` over a base of the ambient model whose real part is `ℂ((t))`, the ambient
comparison `Θ` of `[C]` is the concrete `Θ` of the RES class of the set of concrete RV tuples whose
image lies in the domain of `C` (`ambient_chart_class`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

local instance bridgeStructure : LRV.Structure Carrier := canonicalInterpret
local instance bridgeModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

theorem coefficient_resSetClass (S : Set Carrier) (hS : S = {c | baseCarrier c}) {n : ℕ}
    (D : DefSet (rawRVSpace (M := Carrier) n) S)
    (hD : (Set.range (fun u : D => fun i => Values.vrv (u.val i))).Finite) :
    ∃ (D' : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
      (hD' : (Set.range (fun u : D' => fun i => Values.vrv (u.val i))).Finite),
      D'.carrier = D.carrier ∧
      coefficientGroundComparison S hS (RESDimensionFreeReduction.quotient _
          (resSetClass canonicalInterpret_isCanonical D hD)) =
        theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
          (resSetClass canonicalInterpret_isCanonical D' hD')) := by
  subst hS
  exact ⟨D, hD, rfl, rfl⟩

variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]

/-- **`Θ` of an ambient RES chart.** -/
theorem ambient_chart_class (hcN : CanonicalStructure.IsCanonical (M := N)) (e : Carrier ↪ₑ[LRV] N)
    (B : Base (M := N)) (hB : B.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ B.gamma, GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ)
    {k : ℕ} (C : RESChart B k) :
    ∃ (D : DefSet (rawRVSpace (M := Carrier) C.arity) {c | baseCarrier c})
      (hD : (Set.range (fun u : D => fun i => Values.vrv (u.val i))).Finite),
      (∀ x, x ∈ D.carrier ↔ (fun i => e (x i).val) ∈ C.domain) ∧
      ambientPuiseuxComparison hcN e B hB hγ (nativeRESChartClass C) =
        theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
          (resSetClass canonicalInterpret_isCanonical D hD)) := by
  obtain ⟨real, gamma⟩ := B
  change real = _ at hB
  subst hB
  let C' := resGroundTransferObject (fun sn A h =>
    (realGammaGround_definable_iff (⟨Set.range (e ∘ laurentCoefficientEnumeration), gamma⟩ : Base (M := N))
      hγ sn A).mp h) C
  let R := elementaryNativeRESRestriction canonicalInterpret_isCanonical hcN e laurentCoefficientEnumeration
    (Section3RVChartBridge.nativeRES hcN C')
  have key : ambientPuiseuxComparison hcN e _ rfl hγ (nativeRESChartClass C) =
      coefficientGroundComparison _ laurentCoefficientEnumeration_range
        (RESDimensionFreeReduction.quotient _ (resSetClass canonicalInterpret_isCanonical
          (originalDomain canonicalInterpret_isCanonical R)
          (originalDomain_finite_values canonicalInterpret_isCanonical R))) := by
    change ambientRealPuiseuxComparison hcN e
      (eliminateRealGammaRES _ hγ (RESDimensionFreeReduction.fromOrdinary _ (RESOrdinaryRing.objectClass C))) = _
    unfold eliminateRealGammaRES
    rw [resGroundTransferReduced_objectClass]
    change coefficientGroundComparison _ laurentCoefficientEnumeration_range
      (elementaryRESReducedRestriction canonicalInterpret_isCanonical hcN e laurentCoefficientEnumeration
        (RESDimensionFreeReduction.fromOrdinary _ (RESOrdinaryRing.objectClass C'))) = _
    rw [elementaryRESReducedRestriction_class, resSetClass_originalDomain]
    rfl
  obtain ⟨D', hD', hcar, heq⟩ := coefficient_resSetClass _ laurentCoefficientEnumeration_range _
    (originalDomain_finite_values canonicalInterpret_isCanonical R)
  refine ⟨D', hD', fun x => ?_, key.trans heq⟩
  rw [hcar]
  change x ∈ (elementaryNativeRVRestriction canonicalInterpret_isCanonical hcN e laurentCoefficientEnumeration
    (Section3RVChartBridge.nativeRES hcN C').obj.domain).carrier ↔ _
  rw [elementaryNativeRVRestriction_mem]
  rfl

end DiamondIntegral.Section8.Truncation
