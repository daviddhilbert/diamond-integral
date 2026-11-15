import «section 5».NativeMixedKeyMaps
import «section 5».NativeRVFiniteLiftLabels
import «section 5».NativeRVObjectEvaluation
import «section 3».GammaGroundRVFamilyObjects
import «section 3».GammaGroundCarrierBijections

/-! A native RV-pullback with nonzero VF coordinates and finite RV fibres
has an actual original-ground RV presentation. The finite label map is
proved from its full VF lift, and no RV section is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def nativePullbackRVLabels (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    GammaGroundMap (nativeMixedFullKeyMap A).image (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) n)) :=
  gammaGroundRVSelectCoordinates (Fin.castAdd r) (nativeMixedFullKeyMap A).image

theorem nativePullbackRVLabels_value (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (u : (nativeMixedFullKeyMap A).image) : ((nativePullbackRVLabels A) u).val = u.val ∘ Fin.castAdd r := rfl

theorem nativePullback_attach_image
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier) :
    (nativeAttachSelectedVFKeys A id).image.carrier =
      (nativeRVLabelLift (nativeMixedFullKeyMap A).image (nativePullbackRVLabels A)).carrier := by
  ext w
  constructor
  · rintro ⟨a,ha⟩
    have hw : w = (a.val.1,Fin.append (Section2.tupleRV M a.val.1) a.val.2) :=
      ha.symm.trans (nativeAttachSelectedVFKeys_value A id a)
    rw [hw]
    refine ⟨⟨((nativeMixedFullKeyMap A) a).val,⟨a,rfl⟩⟩,rfl,?_⟩
    change Fin.append (Section2.tupleRV M a.val.1) a.val.2 ∘ Fin.castAdd r = Section2.tupleRV M a.val.1
    exact funext (fun i => Fin.append_left _ _ i)
  · rintro ⟨u,hu,hv⟩
    obtain ⟨a,ha⟩ := u.property
    have haKey : (flatKey a.val).2 = u.val := ha
    have hvolume : u.val ∘ Fin.castAdd r = Section2.tupleRV M w.1 := hv
    let z : Point (M := M) n r := (w.1,u.val ∘ Fin.natAdd n)
    have hzKey : (flatKey z).2 = u.val := by
      change Fin.append (Section2.tupleRV M w.1) (u.val ∘ Fin.natAdd n) = u.val
      rw [←hvolume]
      exact Fin.append_castAdd_natAdd
    have he : flatKey a.val = flatKey z :=
      Prod.ext (Subsingleton.elim _ _) (haKey.trans hzKey.symm)
    have hz : z ∈ A.carrier := (mem_iff_sameRV hpull ((flatKey_eq_iff a.val z).mp he)).mp a.property
    refine ⟨⟨z,hz⟩,?_⟩
    change ((nativeAttachSelectedVFKeys A id) ⟨z,hz⟩).val = w
    rw [nativeAttachSelectedVFKeys_value]
    exact Prod.ext rfl (hzKey.trans hu)

def nativePullbackLiftBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier) :
    GammaGroundBijection A (nativeRVLabelLift (nativeMixedFullKeyMap A).image (nativePullbackRVLabels A)) :=
  (GammaGroundBijection.ofCarrierEq (nativePullback_attach_image A hpull)).comp
    (nativeAttachSelectedVFKeysBijection A id)

theorem nativePullbackRVLabels_nonzero
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (hnz : ∀ a : A,∀ i : Fin n,a.val.1 i ≠ 0)
    (u : (nativeMixedFullKeyMap A).image) (i : Fin n) :
    (((nativePullbackRVLabels A) u).val i).val ≠ iRVZero := by
  obtain ⟨a,ha⟩ := u.property
  have ha' : ((nativeMixedFullKeyMap A) a).val = u.val := ha
  have hu : u.val = Fin.append (Section2.tupleRV M a.val.1) a.val.2 :=
    ha'.symm.trans (nativeMixedFullKeyMap_value A a)
  rw [nativePullbackRVLabels_value]
  change (u.val (Fin.castAdd r i)).val ≠ iRVZero
  rw [hu,Fin.append_left]
  exact fun h => hnz a i ((rvValues_tupleRV_zero_iff a.val.1 i).mp h)

def nativePullbackRVObject
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite)
    (hnz : ∀ a : A,∀ i : Fin n,a.val.1 i ≠ 0) : GammaGroundRVObject hc B n :=
  nativeRVObjectOfLiftBijection hκ hs h00 hr (nativeMixedFullKeyMap A).image (nativePullbackRVLabels A)
    ⟨n,r,A,hf⟩ (nativePullbackLiftBijection A hpull) (nativePullbackRVLabels_nonzero A hnz)

def nativePullbackRVObject_lift_bijection
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite)
    (hnz : ∀ a : A,∀ i : Fin n,a.val.1 i ≠ 0) :
    GammaGroundBijection A (gammaGroundObjectLift (nativePullbackRVObject hκ hs h00 hr A hpull hf hnz)) :=
  nativePullbackLiftBijection A hpull

theorem nativePullbackRVObject_bounded_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite)
    (hnz : ∀ a : A,∀ i : Fin n,a.val.1 i ≠ 0) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ .bounded
      (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (nativePullbackRVObject hκ hs h00 hr A hpull hf hnz))) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .bounded (nativeMixedFullKeyMap A).image := by
  let U := nativePullbackRVObject hκ hs h00 hr A hpull hf hnz
  exact ((nativeRVSetValue_object h00 linear hκ hs hc B hr hγ hΓ .bounded U).trans
    (nativeGroundRVEvaluation_class h00 linear hκ hs hc B hr hγ hΓ .bounded U)).symm

end DiamondIntegral.Section5
