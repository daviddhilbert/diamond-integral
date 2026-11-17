import «section 3».GammaMixedContractionValues
import «section 3».GammaGroundMeasuredRVFinitePartitions

/-! Empty mixed domains have zero contraction value. Actual
surjectivity of the chosen presentations and programs proves emptiness
of the literal RV endpoint before its measured class is taken. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMixed_empty_contraction_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hNames : commonRealNames B ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase B)
    (U : GammaGroundMeasuredVFData hc B (n+1)) (hU : U.domain.carrier = ∅) :
    gammaMixedContractionValue C hBC hv hNames hGenerated U = 0 := by
  let P := gammaMixedRetainedRepresentation C hBC hv U
  let A := P.data.nativeSet C hNames
  let T := P.data.contraction C hBC hNames hGenerated
  let hT := P.data.contraction_gamma C hBC hNames hGenerated
  have hTarget (q : T.target) : False := by
    obtain ⟨p,_⟩ := (T.program.surjective.comp (vfPermutationBijection_bijective A (Equiv.refl _)).2) q
    obtain ⟨u,_⟩ := P.map.map.bijective.2 ⟨p.val,p.property⟩
    exact Set.notMem_empty u.val (hU ▸ u.property)
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let V := gammaNativeFiniteAt (gammaRawFiniteContraction (U := A) C.uncountable.le C.saturated hr hBC
    P.data.point_definable P.data.finite T hT)
  let W := gammaNativeMeasuredNormalization V
    (gammaNativeTotalRVForm V (suffixIndex T.program.rvArity_le) P.data.form.extendByOne)
  have hW : W.underlying.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    let u : W.underlying.domain := ⟨r,hr⟩
    let v := gammaNativeHighLabelInclusion V u
    exact hTarget ⟨(Fin.elim0,v.val),
      (gammaNative_raw_contraction_mem (hc := hc) C hBC (A := A) P.data.point_definable P.data.finite T hT v.val).mp v.property⟩
  change (gammaGroundMeasuredRVSpecialCongruence hc B).mk' (gammaGroundMeasuredRVSemiringClass W) = 0
  rw [gammaGroundMeasuredRVSemiringClass_of_empty W hW]
  exact (gammaGroundMeasuredRVSpecialCongruence hc B).mk'.map_zero

end DiamondIntegral.Section3
