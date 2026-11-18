import «section 3».GammaNativeUnaryChainComparison

/-! The density produced by the unary chain induction is exactly the
original density evaluated at the explicit retained source labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativeUnarySpecial_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ 1)
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ 1 (rvObjectArity U.object.obj)}
    {l : ℕ} {C : SpecialTransformations.Section5.DefSet (M := M) Set.univ 1 l}
    (h : @PresentsLift M N hN Set.univ 1 U.object.obj (normalizedPointSet A))
    (T : SpecialBijection A C) (hΓ : GammaChainDefinable B T.chain)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    ∃ hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)),
      gammaNativeSpecialClass U ω = gammaNativeSpecialClass
        (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T.chain hΓ) hCF)
        (ω.comp (gammaPreparedRVLabelMap U h T hΓ hCF)) := by
  obtain ⟨hCF,η,H,hη⟩ := (gammaNativeUnaryChain_comparison_pair hκ hs h00 hr T.chain hΓ).1
    (@SpecialTransformations.Section4.RVObject.domain M N Set.univ 1 U.object.obj)
    (@SpecialTransformations.Section4.RVObject.volume M N Set.univ 1 U.object.obj)
    U.object.property h T.alternating ω
  let hC := GammaChainDefinable.target B T.chain hΓ
  let K := gammaPreparedRVLabelMap (hc := hc) U h T hΓ hCF
  have he : η = ω.comp K := by
    apply GammaGroundMap.ext
    intro q
    obtain ⟨p,hp⟩ := gammaNativePullbackKeyMap_surjective C hC hCF q
    let b : C := ⟨p.val,p.property⟩
    let a := T.inverseMap b
    have ha : T.toMap a = b := T.apply_inverse b
    have hb : gammaNativePullbackKeyAt C hC hCF b = q := hp
    have Hq := hη a
    change η (gammaNativePullbackKeyAt C hC hCF (T.toMap a)) =
      ω (gammaPresentationLabelAt U h a) at Hq
    rw [ha,hb] at Hq
    change η q = ω (K q)
    apply Hq.trans
    congr 1
    apply Subtype.ext
    rw [gammaPresentationLabelAt_val,gammaPreparedRVLabelMap_val]
    have hq : q.val = Fin.append (Section2.tupleRV M b.val.1) b.val.2 :=
      (congrArg Subtype.val hb).symm
    rw [hq]
    funext j
    exact (congrFun (gammaSpecial_inverse_old_labels T b) j).trans (Fin.append_right (Section2.tupleRV M b.val.1) b.val.2 (gammaChainOldLabelIndex T.chain j)).symm
  refine ⟨hCF,?_⟩
  rw [he] at H
  exact H

end DiamondIntegral.Section3
