import «section 4».EulerEndpointProjection
import «section 4».GammaPointAlgebra

/-! The endpoint projection of an original-base definable Euler function
lies in the actual point group ring over that same base. This constructs
the ring character p_a -> [a], q_a -> -[a], line -> 0 without adding names. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaEndpointProjection
open GammaDefinableEuler GammaDefinableConvolution GammaPointAlgebra GammaNamesSubgroup EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pointValueEmbedding (B : Base (M := M)) (k : EulerKind) :
    DefinableGammaGroupRing B →+* EulerFunction k (PaperGamma (M := M)) :=
  (baseSubring B k).subtype.comp (pointGroupRing B k)

theorem pointValueEmbedding_injective (B : Base (M := M)) (k : EulerKind) :
    Function.Injective (pointValueEmbedding B k) := by
  intro a b h
  apply pointGroupRing_injective B k
  exact Subtype.ext h

theorem pointValueEmbedding_single (B : Base (M := M)) (k : EulerKind) (a : additiveNames B) (n : ℤ) :
    pointValueEmbedding B k (AddMonoidAlgebra.single a n) = n • point k a.val := by
  change (baseSubring B k).subtype (pointGroupRing B k (AddMonoidAlgebra.single a n)) = _
  rw [pointGroupRing_single, map_zsmul]
  rfl

theorem point_mem_range (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M))
    (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    point k a ∈ (pointValueEmbedding B k).range := by
  refine ⟨AddMonoidAlgebra.single (⟨a, ha⟩ : additiveNames B) 1, ?_⟩
  rw [pointValueEmbedding_single, one_zsmul]

theorem endpointProjection_mem_range (B : Base (M := M)) (k : EulerKind) (f : baseSubring B k) :
    endpointProjection k f.val ∈ (pointValueEmbedding B k).range := by
  let H := ((pointValueEmbedding B k).range.comap (endpointProjection k)).toAddSubgroup
  have hline : line k ∈ H := by
    change endpointProjection k (line k) ∈ (pointValueEmbedding B k).range
    rw [endpointProjection_line]
    exact (pointValueEmbedding B k).range.zero_mem
  have hpoint (a : PaperGamma (M := M)) (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
      point k a ∈ H := by
    change endpointProjection k (point k a) ∈ (pointValueEmbedding B k).range
    rw [endpointProjection_point]
    exact point_mem_range B k a ha
  have hray (a : PaperGamma (M := M)) (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
      ray k a ∈ H := by
    change endpointProjection k (ray k a) ∈ (pointValueEmbedding B k).range
    rw [endpointProjection_ray]
    exact (pointValueEmbedding B k).range.neg_mem (point_mem_range B k a ha)
  exact base_generator_induction B k H hline hpoint hray f.val f.property

def pointRangeEquiv (B : Base (M := M)) (k : EulerKind) :
    DefinableGammaGroupRing B ≃+* (pointValueEmbedding B k).range :=
  RingEquiv.ofBijective (pointValueEmbedding B k).rangeRestrict
    ⟨(fun _ _ h => pointValueEmbedding_injective B k
      (congrArg (fun q : (pointValueEmbedding B k).range => q.val) h)),
      (pointValueEmbedding B k).rangeRestrict_surjective⟩

def endpointToRange (B : Base (M := M)) (k : EulerKind) :
    baseSubring B k →+* (pointValueEmbedding B k).range :=
  ((endpointProjection k).comp (baseSubring B k).subtype).codRestrict
    (pointValueEmbedding B k).range (endpointProjection_mem_range B k)

def namedEndpoint (B : Base (M := M)) (k : EulerKind) : baseSubring B k →+* DefinableGammaGroupRing B :=
  (pointRangeEquiv B k).symm.toRingHom.comp (endpointToRange B k)

theorem namedEndpoint_spec (B : Base (M := M)) (k : EulerKind) (f : baseSubring B k) :
    pointValueEmbedding B k (namedEndpoint B k f) = endpointProjection k f.val := by
  have h := (pointRangeEquiv B k).apply_symm_apply (endpointToRange B k f)
  exact congrArg (fun q : (pointValueEmbedding B k).range => q.val) h

theorem namedEndpoint_point (B : Base (M := M)) (k : EulerKind) (a : additiveNames B) :
    namedEndpoint B k (pointMonoidHom B k (Multiplicative.ofAdd a)) = AddMonoidAlgebra.single a 1 := by
  apply pointValueEmbedding_injective B k
  rw [namedEndpoint_spec, pointValueEmbedding_single, one_zsmul]
  exact endpointProjection_point k a.val

theorem namedEndpoint_ray (B : Base (M := M)) (k : EulerKind) (a : additiveNames B) :
    namedEndpoint B k (⟨ray k a.val, ray_mem_base B k a.val a.property⟩ : baseSubring B k) =
      -AddMonoidAlgebra.single a 1 := by
  apply pointValueEmbedding_injective B k
  rw [namedEndpoint_spec, map_neg, pointValueEmbedding_single, one_zsmul]
  exact endpointProjection_ray k a.val

theorem namedEndpoint_line (B : Base (M := M)) (k : EulerKind) :
    namedEndpoint B k (⟨line k, line_mem_base B k⟩ : baseSubring B k) = 0 := by
  apply pointValueEmbedding_injective B k
  rw [namedEndpoint_spec, map_zero]
  exact endpointProjection_line k

end DiamondIntegral.Section4.GammaEndpointProjection
