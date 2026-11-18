import «section 3».GammaNativeMeasuredRestrictions
import «section 3».GammaMeasuredRestrictionCarrierEq

/-! The native full-weight normalization respects literal finite cuts
with their original Gamma forms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativeComplement_domain
    (U : GammaObjectAt B Set.univ (n+1))
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ)
    (hA : (@DefSet.carrier LRV M N _ Set.univ A) ⊆ (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj)))
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @DefSet.carrier LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A}) :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaComplementAt U A hAΓ)).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) U).carrier \
        (Section5.nativeRVGroundDomain (hc := hc) (gammaRestrictAt U A hA hAΓ)).carrier := by
  rw [Section5.nativeRVGroundDomain_carrier,Section5.nativeRVGroundDomain_carrier,
    Section5.nativeRVGroundDomain_carrier]
  rfl

theorem gammaNativeMeasuredClass_scissor
    (U : GammaObjectAt B Set.univ (n+1))
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ)
    (hA : (@DefSet.carrier LRV M N _ Set.univ A) ⊆ (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj)))
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @DefSet.carrier LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A})
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    let R := gammaRestrictAt U A hA hAΓ
    let C := gammaComplementAt U A hAΓ
    let ωR := ω.comp (gammaNativeRestrictedLabelInclusion U A hA hAΓ)
    let ωC := ω.comp (gammaNativeRestrictedLabelInclusion U
      (@complement M N Set.univ (n+1) U.object.obj A)
      (@complement_subset M N hN Set.univ (n+1) U.object.obj A)
      ((gammaLogicInput B).sdiff U.domain_graph hAΓ))
    gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization R ωR) +
      gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization C ωC) =
        gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization U ω) := by
  let R := gammaRestrictAt U A hA hAΓ
  let C := gammaComplementAt U A hAΓ
  let ωR := ω.comp (gammaNativeRestrictedLabelInclusion U A hA hAΓ)
  let ωC := ω.comp (gammaNativeRestrictedLabelInclusion U
    (@complement M N Set.univ (n+1) U.object.obj A)
    (@complement_subset M N hN Set.univ (n+1) U.object.obj A)
    ((gammaLogicInput B).sdiff U.domain_graph hAΓ))
  let W := gammaNativeMeasuredNormalization U ω
  let X := W.underlying.domain.inter (Section5.nativeRVGroundDomain (hc := hc) R)
  let Y := W.underlying.domain.inter (Section5.nativeRVGroundDomain (hc := hc) C)
  have hX : X.carrier ⊆ W.underlying.domain.carrier := fun _ h => h.1
  have hY : Y.carrier ⊆ W.underlying.domain.carrier := fun _ h => h.1
  have hHigh : W.underlying.domain.carrier ⊆ (Section5.nativeRVGroundDomain (hc := hc) U).carrier := by
    intro x hx
    exact (Section5.nativeRVGroundDomain_carrier U).ge
      (((Section5.nativeRVGroundDomain_carrier (gammaHighRestrictionAt U)).le hx).1)
  have hXY : (W.underlying.domain.sdiff X).carrier = Y.carrier := by
    have hC := gammaNativeComplement_domain (hc := hc) U A hA hAΓ
    change W.underlying.domain.carrier \ (W.underlying.domain.carrier ∩
      (Section5.nativeRVGroundDomain (hc := hc) R).carrier) = W.underlying.domain.carrier ∩
        (Section5.nativeRVGroundDomain (hc := hc) C).carrier
    rw [hC]
    ext x
    constructor
    · rintro ⟨hx,hn⟩
      exact ⟨hx,hHigh hx,fun h => hn ⟨hx,h⟩⟩
    · rintro ⟨hx,_,hn⟩
      exact ⟨hx,fun h => hn h.2⟩
  have fR := gammaNativeMeasuredRestrictionHom U A hA hAΓ ω
  have fC := gammaNativeMeasuredRestrictionHom U
    (@complement M N Set.univ (n+1) U.object.obj A)
    (@complement_subset M N hN Set.univ (n+1) U.object.obj A)
    ((gammaLogicInput B).sdiff U.domain_graph hAΓ) ω
  have g := gammaMeasuredRestrictionCarrierEqHom W (W.underlying.domain.sdiff X) Y
    (fun _ h => h.1) hY hXY
  have hR := gammaGroundMeasuredRVClass_iso (asIso (show W.restrict X hX ⟶ gammaNativeMeasuredNormalization R ωR from fR))
  have hC := gammaGroundMeasuredRVClass_iso (asIso (show W.restrict (W.underlying.domain.sdiff X) (fun _ h => h.1) ⟶
    gammaNativeMeasuredNormalization C ωC from fC.comp g))
  change gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization R ωR) +
    gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization C ωC) = gammaGroundMeasuredRVClass W
  rw [← hR,← hC]
  exact gammaGroundMeasuredRVClass_scissor W X hX

end DiamondIntegral.Section3
