import «section 3».GammaCanonicalMeasuredContractions
import «section 3».GammaNativeEndpointRawClasses
import «section 3».GammaMeasuredNormalizationRows
import «section 3».GammaGroundMeasuredRVFinitePartitions
import Integration7.CanonicalFiniteRVObjects
import Integration7.LiteralVolumeLiftMaps
import Integration7.VolumeLiftFullDimension

/-! A contraction of a VF-small native source has empty full-weight
RV domain, independently of its density. The existing literal lift
bijection and full-dimension polydisc theorem prove this directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaSmall_dimension_contraction_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (hsmall : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rawSpecialSet hc A) < n+1)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) = 0 := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let RF : @RVFiniteObject M N (C.base : Set M) (n+1) :=
    ⟨T.normalizedObject,(gammaFiniteContraction C.uncountable.le C.saturated hr hBC hA hfin T hT).finite_volume⟩
  let Z : PositiveRVVolumeObject (M := M) (C.base : Set M) n :=
    ⟨canonicalFiniteRVObject hc RF,VolumeForm.one _⟩
  let f : Map (rawSpecialSet hc A) (rvVolumeLift Z).domain :=
    (literalVolumeLiftMap hc Z.underlying.obj (typedLift T.normalizedObject)
      (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
      (rawSpecialMap hc (typedContractionNaturalMap T))
  have hf : Function.Bijective f :=
    (literalVolumeLiftMap_bijective hc Z.underlying.obj (typedLift T.normalizedObject)
      (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
      (typedContractionNaturalMap_bijective T)
  have hDim : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rvVolumeLift Z).domain =
      vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rawSpecialSet hc A) :=
    (vfDim_eq_of_bijective (SpecialTransformations.Section4.rawRVSpace (M := M) 1) f hf).symm
  have hEmpty := essential_empty_of_volume_lift_small_dimension hc C Z (hDim ▸ hsmall)
  let V := gammaNativeFiniteAt (gammaFiniteContraction C.uncountable.le C.saturated hr hBC hA hfin T hT)
  let η := gammaNativeTotalRVForm V (contractionOldLabelIndex T) ω
  have hVEmpty : (gammaNativeMeasuredNormalization V η).underlying.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨u,rfl,hn⟩ := (gammaNativeHigh_domain_nonzero V r).mp hr
    let v : Z.underlying.obj.domain := ⟨u.val,(Section5.nativeRVGroundDomain_carrier (hc := hc) V).le u.property⟩
    have hv : u.val ∈ Z.essential.obj.domain.carrier := by
      apply (mem_rvEssentialLabels Z.underlying.obj v).mpr
      intro i
      have hi := hn i
      rw [gammaNativeRVGroundVolume_value] at hi
      exact hi
    exact (Set.eq_empty_iff_forall_notMem.mp hEmpty) u.val hv
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  have hZero : gammaMeasuredPrincipalValue (gammaNativeMeasuredNormalization V η) = 0 :=
    (congrArg q (gammaGroundMeasuredRVSemiringClass_of_empty _ hVEmpty)).trans q.map_zero
  exact (gammaMeasuredPrincipalValue_iso (gammaRaw_normalization_measured_contraction C hBC A hA hfin T hT ω)).trans hZero

end DiamondIntegral.Section3
