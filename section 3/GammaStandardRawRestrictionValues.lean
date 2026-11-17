import «section 3».GammaStandardRawLabelCutComparisons
import «section 3».GammaGroundCarrierBijections

/-! A specified target restriction has exactly the literal restricted
Gamma measured class of the parent raw contraction. Its label domain,
full structural volume and entire retained density are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaStandard_raw_restriction_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {A H : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A)) (hH : GammaSetDefinable B (carrier H))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfinH : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 T.arity}
    (P : StandardTargetRestrictionPresentation (G := B) T H D)
    (hSubset : carrier D ⊆ carrier T.target)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let U := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hA hfinA T hT)
    let V := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hH hfinH P.contraction P.gamma)
    let K := rvObjectDomain V.object.obj
    ∃ hK : (@DefSet.carrier LRV M N _ Set.univ K) ⊆
        (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj)),
      let R := gammaRestrictAt U K hK V.domain_graph
      let Ω := gammaNativeTotalRVForm U (suffixIndex T.program.rvArity_le) ω
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hH hfinH P.contraction P.gamma ω) =
        gammaMeasuredPrincipalValue (gammaNativeMeasuredNormalization R
          (Ω.comp (gammaNativeRestrictedLabelInclusion U K hK V.domain_graph))) := by
  intro hr U V K
  have hK : (@DefSet.carrier LRV M N _ Set.univ K) ⊆
      (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj)) := by
    intro r hr
    have hV : r ∈ (Section5.nativeRVGroundDomain (hc := hc) V).carrier :=
      (Section5.nativeRVGroundDomain_carrier (hc := hc) V).ge hr
    have hp := (gammaNative_raw_contraction_mem (hc := hc) C hBC hH hfinH P.contraction P.gamma r).mp hV
    apply (Section5.nativeRVGroundDomain_carrier (hc := hc) U).le
    apply (gammaNative_raw_contraction_mem (hc := hc) C hBC hA hfinA T hT r).mpr
    exact hSubset hp
  refine ⟨hK,?_⟩
  let R := gammaRestrictAt U K hK V.domain_graph
  let Ω := gammaNativeTotalRVForm U (suffixIndex T.program.rvArity_le) ω
  let η := Ω.comp (gammaNativeRestrictedLabelInclusion U K hK V.domain_graph)
  let ζ := gammaNativeTotalRVForm V (suffixIndex P.contraction.program.rvArity_le) ω
  have hDom : (Section5.nativeRVGroundDomain (hc := hc) V).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) R).carrier := by
    rw [Section5.nativeRVGroundDomain_carrier,Section5.nativeRVGroundDomain_carrier]
    rfl
  let f := GammaGroundBijection.ofCarrierEq hDom
  apply gammaMeasuredPrincipalValue_iso
  apply gammaNativeGroundCoordinateHom ζ η f
  · intro u
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    change u.val ∘ T.volumeIndex = u.val ∘ P.contraction.volumeIndex
    rw [P.volumeIndex]
  · intro u
    apply congrArg ω
    apply Subtype.ext
    rfl

end DiamondIntegral.Section3
