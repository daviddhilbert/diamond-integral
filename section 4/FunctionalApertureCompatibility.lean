import «section 4».VariableApertureCompatibility
import «section 4».RVDefinableGraphExtension

/-! Arbitrary original-base definable aperture functions are retained by
their complete RV graphs. The graph has constructed bounds and preserves
the actual measured object. This includes infinite-image apertures and
reduces their compatibility to the native coordinate presentation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4

namespace DiamondIntegral.Section4.FunctionalApertureCompatibility
open RVMeasuredCharts RVChartDisjointUnion RVRealProducts FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Presentation (B : Base (M := M)) (k : ℕ) where
  base : RVBoundedCharts.BoundedChart B k
  aperture : (Fin base.arity → M) → M
  graph_definable : DefinableOverBase B (fun _ : Fin (1+base.arity) => .rv)
    (RVDefinableGraphExtension.domain base.toChart aperture)
  aperture_nonzero : ∀ u ∈ base.domain, NonzeroRV (aperture u)
  aperture_nonnegative : ∀ u ∈ base.domain, 1 ≤ codeValue (aperture u)
  upperBound : Values.Gamma (M := M)
  aperture_bounded : ∀ u ∈ base.domain, codeValue (aperture u) ≤ upperBound
  source : Data B base.arity (1+k)
  endpoint : Data B base.arity (1+k)
  source_domain : source.domain=base.domain
  endpoint_domain : endpoint.domain=base.domain
  source_weight : ∀ u ∈ base.domain, source.toChart.correctedWeight u=base.correctedWeight u
  endpoint_weight : ∀ u ∈ base.domain,
    endpoint.toChart.correctedWeight u=base.correctedWeight u*codeValue (aperture u)

variable {B : Base (M := M)} {k : ℕ}

def Presentation.graphChart (P : Presentation B k) : Chart B k :=
  RVDefinableGraphExtension.chart P.base.toChart P.aperture P.graph_definable

theorem Presentation.aperture_at_graph (P : Presentation B k)
    (u : Fin (1+P.base.arity) → M) (hu : u ∈ P.graphChart.domain) :
    u (tailIndex 1 P.base.arity 0)=P.aperture (u ∘ headIndex 1 P.base.arity) := by
  exact (congrFun hu.2 0).symm

theorem Presentation.graph_domain_bounded (P : Presentation B k) :
    RVMeasuredBounds.DomainBounded P.graphChart := by
  obtain ⟨β,hβ⟩ := P.base.domain_bounded
  let η := max β (max P.upperBound 1)
  have hβη : β ≤ η := le_max_left _ _
  have hΔη : P.upperBound ≤ η := (le_max_left _ _).trans (le_max_right _ _)
  have h1η : (1 : Values.Gamma (M := M)) ≤ η := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨η,?_⟩
  intro u hu i hi
  have hall : ∀ i : Fin (1+P.base.arity), NonzeroRV (u i) →
      η⁻¹ ≤ codeValue (u i) ∧ codeValue (u i) ≤ η := by
    apply GammaBoundedProducts.all_coordinates 1 P.base.arity
      (fun t => NonzeroRV t → η⁻¹ ≤ codeValue t ∧ codeValue t ≤ η) u
    · intro l hl
      have hb := hβ (u ∘ headIndex 1 P.base.arity) hu.1 l hl
      exact ⟨(inv_le_inv_iff.mpr hβη).trans hb.1,hb.2.trans hβη⟩
    · intro l _
      fin_cases l
      change η⁻¹ ≤ codeValue (u (tailIndex 1 P.base.arity 0)) ∧
        codeValue (u (tailIndex 1 P.base.arity 0)) ≤ η
      rw [P.aperture_at_graph u hu]
      have hl : η⁻¹ ≤ 1 := by simpa only [inv_one] using inv_le_inv_iff.mpr h1η
      exact ⟨hl.trans (P.aperture_nonnegative _ hu.1),(P.aperture_bounded _ hu.1).trans hΔη⟩
  exact hall i hi

def Presentation.graphBase (P : Presentation B k) : RVBoundedCharts.BoundedChart B k :=
  ⟨P.graphChart,P.graph_domain_bounded⟩

theorem Presentation.source_graph_definable (P : Presentation B k) :
    DefinableOverBase B (fun _ : Fin (1+P.base.arity) => .rv)
      (RVDefinableGraphExtension.domain P.source.toChart P.aperture) := by
  have he : RVDefinableGraphExtension.domain P.source.toChart P.aperture=
      RVDefinableGraphExtension.domain P.base.toChart P.aperture := by
    change graphOn P.source.domain (fun u => ![P.aperture u])=
      graphOn P.base.domain (fun u => ![P.aperture u])
    rw [P.source_domain]
  rw [he]
  exact P.graph_definable

theorem Presentation.endpoint_graph_definable (P : Presentation B k) :
    DefinableOverBase B (fun _ : Fin (1+P.base.arity) => .rv)
      (RVDefinableGraphExtension.domain P.endpoint.toChart P.aperture) := by
  have he : RVDefinableGraphExtension.domain P.endpoint.toChart P.aperture=
      RVDefinableGraphExtension.domain P.base.toChart P.aperture := by
    change graphOn P.endpoint.domain (fun u => ![P.aperture u])=
      graphOn P.base.domain (fun u => ![P.aperture u])
    rw [P.endpoint_domain]
  rw [he]
  exact P.graph_definable

def Presentation.sourceGraph (P : Presentation B k) : Chart B (1+k) :=
  RVDefinableGraphExtension.chart P.source.toChart P.aperture P.source_graph_definable

def Presentation.endpointGraph (P : Presentation B k) : Chart B (1+k) :=
  RVDefinableGraphExtension.chart P.endpoint.toChart P.aperture P.endpoint_graph_definable

def Presentation.toCoordinate (P : Presentation B k) :
    VariableApertureCompatibility.Presentation B k where
  base := P.graphBase
  apertureIndex := tailIndex 1 P.base.arity 0
  aperture_nonzero := by
    intro u hu
    rw [P.aperture_at_graph u hu]
    exact P.aperture_nonzero _ hu.1
  aperture_nonnegative := by
    intro u hu
    rw [P.aperture_at_graph u hu]
    exact P.aperture_nonnegative _ hu.1
  upperBound := P.upperBound
  aperture_bounded := by
    intro u hu
    rw [P.aperture_at_graph u hu]
    exact P.aperture_bounded _ hu.1
  source := ofChart P.sourceGraph
  endpoint := ofChart P.endpointGraph
  source_domain := by
    change RVDefinableGraphExtension.domain P.source.toChart P.aperture=
      RVDefinableGraphExtension.domain P.base.toChart P.aperture
    change graphOn P.source.domain (fun u => ![P.aperture u])=
      graphOn P.base.domain (fun u => ![P.aperture u])
    rw [P.source_domain]
  endpoint_domain := by
    change RVDefinableGraphExtension.domain P.endpoint.toChart P.aperture=
      RVDefinableGraphExtension.domain P.base.toChart P.aperture
    change graphOn P.endpoint.domain (fun u => ![P.aperture u])=
      graphOn P.base.domain (fun u => ![P.aperture u])
    rw [P.endpoint_domain]
  source_weight := fun u hu => P.source_weight _ hu.1
  endpoint_weight := by
    intro u hu
    change P.endpoint.toChart.correctedWeight (u ∘ headIndex 1 P.base.arity)=
      P.base.correctedWeight (u ∘ headIndex 1 P.base.arity)*codeValue (u (tailIndex 1 P.base.arity 0))
    rw [P.aperture_at_graph u hu]
    exact P.endpoint_weight _ hu.1

def Presentation.relation (P : Presentation B k) : RVBoundedRing.Ring B := P.toCoordinate.relation

theorem Presentation.forget_relation (P : Presentation B k) :
    RVOrdinaryMaps.boundedForget B P.relation=0 := P.toCoordinate.forget_relation

def ideal (B : Base (M := M)) : Ideal (RVBoundedRing.Ring B) :=
  Ideal.span {x | ∃ k, ∃ P : Presentation B k, x=P.relation}

theorem ideal_le_coordinate_ideal (B : Base (M := M)) :
    ideal B ≤ VariableApertureCompatibility.ideal B := by
  apply Ideal.span_le.mpr
  rintro x ⟨k,P,rfl⟩
  exact Ideal.subset_span ⟨k,P.toCoordinate,rfl⟩

theorem ideal_le_forget_kernel (B : Base (M := M)) :
    ideal B ≤ RingHom.ker (RVOrdinaryMaps.boundedForget B) :=
  (ideal_le_coordinate_ideal B).trans (VariableApertureCompatibility.ideal_le_forget_kernel B)

theorem ideal_homogeneous (B : Base (M := M)) :
    (ideal B).IsHomogeneous (RVBoundedGrading.gradedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨k,P,rfl⟩
  exact ⟨1+k,P.toCoordinate.relation_mem_degree⟩

theorem quotient_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (Ideal.Quotient.mk (ideal B)) (RVBoundedGrading.gradedPiece B 0) :=
  (RVBoundedGrading.gradingCoaction B).quotient_injective_on_zero (ideal B)
    ((ideal_le_coordinate_ideal B).trans
      (VariableApertureCompatibility.ideal_le_zeroProjection_kernel B))

theorem section4_compatibility (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    ideal B ≤ RingHom.ker
      (RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ
        (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) EulerKind.bounded) :=
  (ideal_le_coordinate_ideal B).trans
    (VariableApertureCompatibility.section4_compatibility hc h00 linear hκ hs B hr hγ hΓ)

end DiamondIntegral.Section4.FunctionalApertureCompatibility
