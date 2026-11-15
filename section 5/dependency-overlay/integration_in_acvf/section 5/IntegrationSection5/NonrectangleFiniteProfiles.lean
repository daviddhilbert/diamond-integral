import IntegrationSection5.NonrectangleInverseProfile
import IntegrationSection5.NonrectangleTransverseWitness
import IntegrationSection5.GammaFiniteCombinations
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}
variable {T : PositionedCellLabelInjection G A}

theorem profile_hom_first_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (Q : NonrectangleMatchedHeads T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (z : Fin 2 → RV (M := M)) :
    {t : RV (M := M) | ∃ a : rvObjectDomain (pullbackObject Q.unary.targetA),
      (Q.profileA a).val = z ∧ (Q.profileB (unaryIsoHomMap Q.unary.iso a)).val 0 = t}.Finite := by
  obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective (z 0)
  obtain ⟨v,hv⟩ := CanonicalRV.encodedRv_surjective (z 1)
  let passive := Q.recoverA.trans (gammaLogicInput G) Q.first.passiveLeft
  let centre := passive.trans (gammaLogicInput G) (Q.first.position.symm (gammaLogicInput G))
  have hFin := gammaIso_finite_coordinate_combinations hκ hs hsmall centre passive Q.first.position
    (fun c => c-u) (fun y y' => rv (y'-y)) v
  apply hFin.subset
  rintro t ⟨a,ha,ht⟩
  have hvA : rv v = (rvObjectVolume (pullbackObject Q.unary.targetA) a).val 0 :=
    hv.trans ((congrFun ha 1).symm.trans (Q.profileA_one a))
  obtain ⟨p,hpv,hpa⟩ := unary_key_fixed_representative Q.unary.targetA Q.unary.pullbackA a v hvA
  have huHead : rv u = (Q.recoverA.equiv p).val.2 0 := by
    rw [← Q.profileA_key_recover,hpa]
    exact hu.trans (congrFun ha 0).symm
  obtain ⟨d,hd,hVol⟩ := Q.first.forward_transverse_witness δ hδ (Q.recoverA.equiv p) u huHead
  refine ⟨p,hpv,d,hd,?_⟩
  exact hVol.trans ((Q.profileB_hom_key p).symm.trans (by rw [hpa]; exact ht))

theorem profile_inv_first_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (Q : NonrectangleMatchedHeads T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (z : Fin 2 → RV (M := M)) :
    {t : RV (M := M) | ∃ b : rvObjectDomain (pullbackObject Q.unary.targetB),
      (Q.profileB b).val = z ∧ (Q.profileA (unaryIsoInvMap Q.unary.iso b)).val 0 = t}.Finite := by
  obtain ⟨v,hv⟩ := CanonicalRV.encodedRv_surjective (z 0)
  obtain ⟨w,hw⟩ := CanonicalRV.encodedRv_surjective (z 1)
  let passive := Q.recoverB.trans (gammaLogicInput G) Q.first.passiveRight
  let centre := passive.trans (gammaLogicInput G) Q.first.position
  have hFin := gammaIso_finite_coordinate_combinations hκ hs hsmall centre passive
    (Q.first.position.symm (gammaLogicInput G))
    (fun y => y+v) (fun c x' => rv (c-x')) w
  apply hFin.subset
  rintro t ⟨b,hb,ht⟩
  have hwB : rv w = (rvObjectVolume (pullbackObject Q.unary.targetB) b).val 0 :=
    hw.trans ((congrFun hb 1).symm.trans (Q.profileB_one b))
  obtain ⟨p,hpv,hpb⟩ := unary_key_fixed_representative Q.unary.targetB Q.unary.pullbackB b w hwB
  have hvHead : rv v = (Q.recoverB.equiv p).val.2 0 := by
    rw [← Q.profileB_key_recover,hpb]
    exact hv.trans (congrFun hb 0).symm
  obtain ⟨d,hd,hVol⟩ := Q.first.inverse_transverse_witness δ hδ (Q.recoverB.equiv p) v hvHead
  refine ⟨p,hpv,d,hd,?_⟩
  exact hVol.trans ((Q.profileA_inv_key p).symm.trans (by rw [hpb]; exact ht))

end IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads
