import «section 5».NativeVFKeyAttachments
import «section 5».NativePreparedKeyLifting
import «section 3».GammaGroundMapPreimages

/-! The full mixed RV key map is an actual original-Gamma map. Its raw
coordinates agree with the prepared key, and its VF zero pattern is
detected exactly by the selected RV coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

def nativeMixedRVProjection (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) r)) :=
  GammaGroundMap.ofGlobal A _ (universalProductSnd (SpecialTransformations.Section4.rawVFSpace n)
    (SpecialTransformations.Section4.rawRVSpace r) B.real) (fun _ => Set.mem_univ _)

def nativeMixedFullKeyMap (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) (n+r))) :=
  (nativeMixedRVProjection (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) n (n+r)))).comp
    (nativeAttachSelectedVFKeys A id)

theorem nativeMixedFullKeyMap_value (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (a : A) :
    ((nativeMixedFullKeyMap A) a).val = Fin.append (Section2.tupleRV M a.val.1) a.val.2 := rfl

theorem nativeMixedFullKeyMap_raw_value (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (a : A) :
    rvValues (((nativeMixedFullKeyMap A) a).val) = rawPreparedKey a.val := by
  rw [nativeMixedFullKeyMap_value,rvValues_append]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using (rawPreparedKey_first a.val j).symm
  · simpa only [Fin.append_right] using (rawPreparedKey_last a.val j).symm

theorem rvValues_tupleRV_zero_iff (x : Fin n → Section2.VF M) (i : Fin n) :
    rvValues (Section2.tupleRV M x) i = iRVZero ↔ x i = 0 := by
  constructor
  · intro h
    apply (Section2.rv_eq_zero_iff (x i)).mp
    exact Subtype.ext h
  · intro h
    change (Section2.rv M (x i)).val = iRVZero
    rw [h,Section2.rv_zero]
    rfl

theorem nativeMixedFullKeyMap_vf_zero_iff
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (a : A) (i : Fin n) :
    rvValues (((nativeMixedFullKeyMap A) a).val) (Fin.castAdd r i) = iRVZero ↔ a.val.1 i = 0 := by
  rw [nativeMixedFullKeyMap_raw_value,rawPreparedKey_first]
  exact rvValues_tupleRV_zero_iff a.val.1 i

end DiamondIntegral.Section5
