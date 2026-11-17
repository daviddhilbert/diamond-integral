import «section 3».GammaMeasuredIndexedElementaryChart
import «section 3».GammaNativeElementaryRelations

/-! Indexed assembly respects an actual elementary measured relation
in the originally stated semiring congruence, before groupification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaMeasuredRVSchema.indexedElementaryRaw_relation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)) (A N : ℕ)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hAd : ∀ t ∈ T, (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) A).valid (rvValues t))
    (hE : ∀ t ∈ T, (F.elementaryFormula.withBound N).valid (rvValues t))
    (P : F.object.IndexedPresentation BP)
    (Q : (F.elementaryFormula.withBound N).object.IndexedPresentation BP) :
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (F.indexedObject BP hF P))
      (gammaGroundMeasuredRVSemiringClass ((F.elementaryFormula.withBound N).indexedObject BP hE Q)) := by
  let U := gammaUniversalObject P.toGamma
  let Ad : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv) := ⟨F.object,Fin.last k,A⟩
  let hAP := gammaUniversalObject_admissible P.toGamma (Ad.indexed_admissible BP hAd P)
  let ω := F.indexedForm BP hF P
  have hNative := gammaNativeElementary_congruence hκ hs h00 hr U ω (Fin.natAdd d (Fin.last k)) hAP
  obtain ⟨f⟩ := F.indexedElementaryChart hκ hs h00 hr A N BP hF hAd hE P Q
  have hTarget := gammaGroundMeasuredRVSemiringClass_iso (asIso f)
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  apply (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mp
  exact ((gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr hNative).trans (congrArg q hTarget.symm)

end DiamondIntegral.Section3
