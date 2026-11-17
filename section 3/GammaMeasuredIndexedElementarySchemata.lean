import «section 3».GammaMeasuredIndexedElementaryRelation
import «section 3».GammaMeasuredIndexedEssential
import «section 3».GammaMeasuredIndexedAgreements
import «section 3».GammaMeasuredUniformBounds

/-! A uniformly valid elementary proof schema is sound after indexed
assembly. Intermediate numeric bounds are supplied by compactness; the
output is the original essential elementary formula at its stated bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
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

theorem GammaMeasuredRVSchema.indexedElementary_relation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)) (A L : ℕ)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hValid : ∀ t ∈ T, (GammaMeasuredRelationSchema.elementary F L A).valid (rvValues t))
    (P : F.object.IndexedPresentation BP)
    (Q : (F.elementaryFormula.essential.withBound L).object.IndexedPresentation BP) :
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (F.indexedObject BP (fun t ht => (hValid t ht).1) P))
      (gammaGroundMeasuredRVSemiringClass ((F.elementaryFormula.essential.withBound L).indexedObject BP
        (fun t ht => (hValid t ht).2.1) Q)) := by
  let hF := fun t ht => (hValid t ht).1
  let hAd := fun t ht => (hValid t ht).2.2
  let hTarget := fun t ht => (hValid t ht).2.1
  obtain ⟨N,hN⟩ := F.exists_uniform_elementary_bound hκ hs h00 hr hg A BP hF hAd
  let E := F.elementaryFormula.withBound N
  let EP := E.object.indexedPresentation BP (fun t ht => (hN t ht).1)
  let hES := fun t ht => E.essential_valid (rvValues t) (hN t ht)
  let SP := E.essential.object.indexedPresentation BP (fun t ht => (hES t ht).1)
  have hRel := F.indexedElementaryRaw_relation hκ hs h00 hr A N BP hF hAd hN P EP
  obtain ⟨e⟩ := E.indexedEssential BP hN EP SP
  have hRows : ∀ t ∈ T, E.essential.toRVTemplate.sameRow
      (F.elementaryFormula.essential.withBound L).toRVTemplate (rvValues t) := by
    intro t ht
    have hsRV : ∀ j, sortEval SortTag.rv (rvValues t j) := fun j => (t j).property
    exact ⟨⟨hsRV,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩,
      ⟨hsRV,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩⟩
  obtain ⟨f⟩ := E.essential.indexedAgreement (F.elementaryFormula.essential.withBound L) BP
    hES hTarget hRows SP Q
  have hClass := gammaGroundMeasuredRVSemiringClass_iso (asIso (f.comp e))
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  apply (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mp
  exact ((gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr hRel).trans (congrArg q hClass)

end DiamondIntegral.Section3
