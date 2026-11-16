import «section 4».VariableApertureAnnularDomains
import «section 4».Section3LinkedRetractionStatements
import «section 4».PositiveIdealDegreeZero
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! Native Section 4 compatibility of bounded variable annular relations.
The endpoint is a retained coordinate, obtained by keeping the graph of
the aperture function. Source and endpoint carry the exact normalized
weights. Actual ray cancellation proves vanishing already in the full
ordinary RV ring; the established bounded retraction then factors.
This does not assert the revised VF kernel theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4

namespace DiamondIntegral.Section4.VariableApertureCompatibility
open RVMeasuredCharts RVChartDisjointUnion VariableApertureRayCancellation

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Presentation (B : Base (M := M)) (k : ℕ) where
  base : RVBoundedCharts.BoundedChart B k
  apertureIndex : Fin base.arity
  aperture_nonzero : ∀ u ∈ base.domain, NonzeroRV (u apertureIndex)
  aperture_nonnegative : ∀ u ∈ base.domain, 1 ≤ codeValue (u apertureIndex)
  upperBound : Values.Gamma (M := M)
  aperture_bounded : ∀ u ∈ base.domain, codeValue (u apertureIndex) ≤ upperBound
  source : Data B base.arity (1+k)
  endpoint : Data B base.arity (1+k)
  source_domain : source.domain=base.domain
  endpoint_domain : endpoint.domain=base.domain
  source_weight : ∀ u ∈ base.domain, source.toChart.correctedWeight u=base.correctedWeight u
  endpoint_weight : ∀ u ∈ base.domain,
    endpoint.toChart.correctedWeight u=base.correctedWeight u*codeValue (u apertureIndex)

variable {B : Base (M := M)} {k : ℕ}

def Presentation.sourceBounded (P : Presentation B k) : RVBoundedCharts.BoundedChart B (1+k) :=
  ⟨P.source.toChart,by
    obtain ⟨β,hβ⟩ := P.base.domain_bounded
    exact ⟨β,fun u hu i hi => hβ u (P.source_domain ▸ hu) i hi⟩⟩

def Presentation.endpointBounded (P : Presentation B k) : RVBoundedCharts.BoundedChart B (1+k) :=
  ⟨P.endpoint.toChart,by
    obtain ⟨β,hβ⟩ := P.base.domain_bounded
    exact ⟨β,fun u hu i hi => hβ u (P.endpoint_domain ▸ hu) i hi⟩⟩

def Presentation.shell (P : Presentation B k) : RVBoundedCharts.BoundedChart B (1+k) :=
  boundedAnnularChart P.base P.apertureIndex P.aperture_nonzero P.upperBound P.aperture_bounded

def Presentation.relation (P : Presentation B k) : RVBoundedRing.Ring B :=
  RVBoundedRing.objectClass P.shell + RVBoundedRing.objectClass P.endpointBounded -
    RVBoundedRing.objectClass P.sourceBounded

def Presentation.endpointSourceIso (P : Presentation B k) :
    RVForgetScissors.UnderlyingIso P.endpoint.toChart P.source.toChart := by
  refine RVForgetScissors.ofMap P.endpoint.toChart P.source.toChart
    (id : (Fin P.base.arity → M) → (Fin P.base.arity → M)) ?_ ?_
  · exact RVSharpCharts.identity_graph_definable B P.endpoint.domain P.endpoint.domain_definable
  refine ⟨?_,(fun _ _ _ _ h => h),?_⟩
  · intro u hu
    change u ∈ P.source.domain
    rw [P.source_domain]
    exact P.endpoint_domain ▸ hu
  · intro u hu
    refine ⟨u,?_,rfl⟩
    change u ∈ P.endpoint.domain
    rw [P.endpoint_domain]
    exact P.source_domain ▸ hu

theorem Presentation.forget_relation (P : Presentation B k) :
    RVOrdinaryMaps.boundedForget B P.relation=0 := by
  simp only [Presentation.relation,map_sub,map_add,RVOrdinaryMaps.boundedForget_class]
  change RVOrdinaryRing.objectClass (annularChart P.base.toChart P.apertureIndex)+
    RVOrdinaryRing.objectClass P.endpoint.toChart-RVOrdinaryRing.objectClass P.source.toChart=0
  rw [annular_class_zero P.base.toChart P.apertureIndex P.aperture_nonzero P.aperture_nonnegative,
    RVOrdinaryRing.objectClass_iso P.endpointSourceIso,zero_add,sub_self]

def ideal (B : Base (M := M)) : Ideal (RVBoundedRing.Ring B) :=
  Ideal.span {x | ∃ k, ∃ P : Presentation B k, x=P.relation}

theorem ideal_le_forget_kernel (B : Base (M := M)) :
    ideal B ≤ RingHom.ker (RVOrdinaryMaps.boundedForget B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨k,P,rfl⟩
  exact P.forget_relation

theorem Presentation.relation_mem_degree (P : Presentation B k) :
    P.relation ∈ RVBoundedGrading.gradedPiece B (1+k) :=
  (RVBoundedGrading.gradedPiece B (1+k)).sub_mem
    ((RVBoundedGrading.gradedPiece B (1+k)).add_mem
      (RVBoundedGrading.class_mem B _) (RVBoundedGrading.class_mem B _))
    (RVBoundedGrading.class_mem B _)

theorem ideal_homogeneous (B : Base (M := M)) :
    (ideal B).IsHomogeneous (RVBoundedGrading.gradedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨k,P,rfl⟩
  exact ⟨1+k,P.relation_mem_degree⟩

theorem ideal_le_zeroProjection_kernel (B : Base (M := M)) :
    ideal B ≤ RingHom.ker (RVBoundedGrading.gradingCoaction B).zeroProjection := by
  apply Ideal.span_le.mpr
  rintro x ⟨k,P,rfl⟩
  exact (RVBoundedGrading.gradingCoaction B).zeroProjection_of_positive_mem
    (by omega : 1+k≠0) P.relation_mem_degree

theorem quotient_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (Ideal.Quotient.mk (ideal B)) (RVBoundedGrading.gradedPiece B 0) :=
  (RVBoundedGrading.gradingCoaction B).quotient_injective_on_zero (ideal B)
    (ideal_le_zeroProjection_kernel B)

theorem section4_compatibility (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    ideal B ≤ RingHom.ker
      (RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ
        (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) EulerKind.bounded) := by
  intro x hx
  change RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) EulerKind.bounded
      (RVOrdinaryMaps.boundedForget B x)=0
  rw [show RVOrdinaryMaps.boundedForget B x=0 from ideal_le_forget_kernel B hx,map_zero]

end DiamondIntegral.Section4.VariableApertureCompatibility
