import «section 3».GammaNativeMeasuredVolumePermutations
import «section 3».GammaNativeLiftMembership
import «section 5».NativeMixedCoordinateMaps

/-! Structural RV volume reindexing is realized by the actual VF
coordinate permutation on full native lifts. Every RV label is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable (U : GammaObjectAt B Set.univ (n+1)) (σ : Equiv.Perm (Fin (n+1)))

def gammaNativeLiftPermutationMap :
    GammaGroundMap (gammaNativeUnitLift (hc := hc) U.toGamma).domain
      (gammaNativeUnitLift (hc := hc) (U.reindexVolume σ).toGamma).domain :=
  (Section5.nativeMixedCoordinateMap (gammaNativeUnitLift (hc := hc) U.toGamma).domain σ id).corestrict (fun q => by
    change (q.val.1 ∘ σ,q.val.2) ∈ (gammaNativeUnitLift (hc := hc) (U.reindexVolume σ).toGamma).domain.carrier
    obtain ⟨u,hu,hv⟩ := (gammaNativeLift_membership U q.val).mp q.property
    apply (gammaNativeLift_membership (U.reindexVolume σ) (q.val.1 ∘ σ,q.val.2)).mpr
    exact ⟨(gammaNativeVolumePermutation U σ).map u,(gammaNativeVolumePermutation_label U σ u).trans hu,
      (gammaNativeVolumePermutation_volume U σ u).trans (congrArg (fun v => v ∘ σ) hv)⟩)

theorem gammaNativeLiftPermutationMap_value
    (q : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
    (gammaNativeLiftPermutationMap U σ q).val = (q.val.1 ∘ σ,q.val.2) := rfl

theorem gammaNativeLiftPermutationMap_bijective : Function.Bijective (gammaNativeLiftPermutationMap (hc := hc) U σ) := by
  constructor
  · intro q r h
    have hraw : (q.val.1 ∘ σ,q.val.2) = (r.val.1 ∘ σ,r.val.2) :=
      (gammaNativeLiftPermutationMap_value U σ q).symm.trans
        ((congrArg Subtype.val h).trans (gammaNativeLiftPermutationMap_value U σ r))
    have hVF := congrArg Prod.fst hraw
    have hRV := congrArg Prod.snd hraw
    apply Subtype.ext
    refine Prod.ext (funext (fun j => ?_)) hRV
    obtain ⟨i,rfl⟩ := σ.surjective j
    exact congrFun hVF i
  · intro q
    obtain ⟨v,hv,hV⟩ := (gammaNativeLift_membership (U.reindexVolume σ) q.val).mp q.property
    let E := gammaNativeVolumePermutation (hc := hc) U σ
    let u := E.symm.map v
    have hUV : E.map u = v := E.map.apply_inverse E.bijective v
    have hu : u.val = q.val.2 := (gammaNativeVolumePermutation_label U σ u).symm.trans
      ((congrArg Subtype.val hUV).trans hv)
    have hVol : (Section5.nativeRVGroundVolume U u).val ∘ σ = @Section2.tupleRV M sM hM (n+1) q.val.1 :=
      (gammaNativeVolumePermutation_volume U σ u).symm.trans
        ((congrArg (fun w => (Section5.nativeRVGroundVolume (U.reindexVolume σ) w).val) hUV).trans hV)
    have hOld : (Section5.nativeRVGroundVolume U u).val = @Section2.tupleRV M sM hM (n+1) (q.val.1 ∘ σ.symm) := by
      funext j
      exact (congrArg ((Section5.nativeRVGroundVolume U u).val) (σ.apply_symm_apply j)).symm.trans
        (congrFun hVol (σ.symm j))
    let p : (gammaNativeUnitLift (hc := hc) U.toGamma).domain :=
      ⟨(q.val.1 ∘ σ.symm,q.val.2),(gammaNativeLift_membership U _).mpr ⟨u,hu,hOld⟩⟩
    refine ⟨p,Subtype.ext (Prod.ext ?_ rfl)⟩
    funext j
    exact congrArg q.val.1 (σ.symm_apply_apply j)

def gammaNativeLiftPermutation :
    GammaGroundBijection (gammaNativeUnitLift (hc := hc) U.toGamma).domain
      (gammaNativeUnitLift (hc := hc) (U.reindexVolume σ).toGamma).domain :=
  ⟨gammaNativeLiftPermutationMap U σ,gammaNativeLiftPermutationMap_bijective U σ⟩

theorem gammaNativeLiftPermutation_inverse_value
    (q : (gammaNativeUnitLift (hc := hc) (U.reindexVolume σ).toGamma).domain) :
    ((gammaNativeLiftPermutation U σ).symm.map q).val = (q.val.1 ∘ σ.symm,q.val.2) := by
  let E := gammaNativeLiftPermutation (hc := hc) U σ
  let p := E.symm.map q
  have h := congrArg Subtype.val (E.map.apply_inverse E.bijective q)
  have hval : (p.val.1 ∘ σ,p.val.2) = q.val :=
    (gammaNativeLiftPermutationMap_value U σ p).symm.trans h
  have hVF : p.val.1 ∘ σ = q.val.1 := congrArg Prod.fst hval
  have hRV := congrArg Prod.snd hval
  refine Prod.ext (funext (fun j => ?_)) hRV
  exact (congrArg p.val.1 (σ.apply_symm_apply j)).symm.trans (congrFun hVF (σ.symm j))

theorem gammaNativeLiftPermutation_label
    (q : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
    gammaNativeLiftLabel (U.reindexVolume σ) ((gammaNativeLiftPermutation U σ).map q) =
      (gammaNativeVolumePermutation U σ).map (gammaNativeLiftLabel U q) := by
  apply Subtype.ext
  exact (gammaNativeVolumePermutation_label U σ (gammaNativeLiftLabel U q)).symm

end DiamondIntegral.Section3
