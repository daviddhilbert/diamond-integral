import «section 5».NativeRVCoordinateMaps
import «section 5».NativeVFZeroStrata
import «section 3».GammaGroundCarrierBijections

/-! The full RV key commutes with deletion of fixed VF coordinates.
Its zero strata are exactly the corresponding strata of the RV image.
All old RV coordinates remain in these actual original-ground maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r d : ℕ}

theorem nativeFullKeySelection_commute
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n) (a : A) :
    ((nativeRVZeroBlockMap (nativeMixedFullKeyMap A).image j) ((nativeMixedFullKeyMap A).toImage a)).val =
      ((nativeMixedFullKeyMap (nativeVFCoordinateSelection A j).image)
        ((nativeVFCoordinateSelection A j).toImage a)).val := by
  have hk : ((nativeMixedFullKeyMap A).toImage a).val =
      Fin.append (Section2.tupleRV M a.val.1) a.val.2 := nativeMixedFullKeyMap_value A a
  have hv : ((nativeVFCoordinateSelection A j).toImage a).val =
      (a.val.1 ∘ j,a.val.2) := nativeVFCoordinateSelection_value A j a
  rw [nativeRVZeroBlockMap_value,nativeMixedFullKeyMap_value,hk,hv]
  funext i
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i <;>
    simp only [Fin.append_left,Fin.append_right,Function.comp_apply]
  rfl

theorem nativeFullKeySelection_image
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n) :
    (nativeRVZeroBlockMap (nativeMixedFullKeyMap A).image j).image.carrier =
      (nativeMixedFullKeyMap (nativeVFCoordinateSelection A j).image).image.carrier := by
  ext w
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨a,ha⟩ := u.property
    have he : (nativeMixedFullKeyMap A).toImage a = u := Subtype.ext ha
    refine ⟨(nativeVFCoordinateSelection A j).toImage a,?_⟩
    exact (nativeFullKeySelection_commute A j a).symm.trans
      ((congrArg (fun z => ((nativeRVZeroBlockMap (nativeMixedFullKeyMap A).image j) z).val) he).trans hu)
  · rintro ⟨b,hb⟩
    obtain ⟨a,ha⟩ := b.property
    have he : (nativeVFCoordinateSelection A j).toImage a = b := Subtype.ext ha
    refine ⟨(nativeMixedFullKeyMap A).toImage a,?_⟩
    exact (nativeFullKeySelection_commute A j a).trans
      ((congrArg (fun z => ((nativeMixedFullKeyMap (nativeVFCoordinateSelection A j).image) z).val) he).trans hb)

theorem nativeFullKeyZeroStratum_image
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (I : Finset (Fin n)) :
    (nativeMixedFullKeyMap (nativeVFZeroStratum A I)).image.carrier =
      (nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r) I).carrier := by
  ext w
  constructor
  · rintro ⟨a,ha⟩
    have hp := (nativeVFZeroStratum_mem A I a.val).mp a.property
    let b : A := ⟨a.val,hp.1⟩
    have hk : ((nativeMixedFullKeyMap A) b).val = w := ha
    refine (nativeRVZeroPatternBase_mem _ _ _ w).mpr ⟨⟨b,hk⟩,?_⟩
    intro i
    have hz := nativeMixedFullKeyMap_vf_zero_iff A b i
    rw [hk] at hz
    exact (hp.2 i).trans (not_congr hz).symm
  · intro hw
    obtain ⟨⟨a,ha⟩,hp⟩ := (nativeRVZeroPatternBase_mem _ _ _ w).mp hw
    have hk : ((nativeMixedFullKeyMap A) a).val = w := ha
    have hI : nativeVFZeroPattern I a.val := by
      intro i
      have hz := nativeMixedFullKeyMap_vf_zero_iff A a i
      rw [hk] at hz
      exact (hp i).trans (not_congr hz)
    exact ⟨⟨a.val,(nativeVFZeroStratum_mem A I a.val).mpr ⟨a.property,hI⟩⟩,ha⟩

def nativeFullKeyDropBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n)
    (hz : ∀ a : A,∀ i : Fin n,i ∉ Set.range j → a.val.1 i = 0) :
    GammaGroundBijection (nativeMixedFullKeyMap A).image
      (nativeMixedFullKeyMap (nativeVFCoordinateSelection A j).image).image :=
  (GammaGroundBijection.ofCarrierEq (nativeFullKeySelection_image A j)).comp
    (nativeRVZeroBlockBijection (nativeMixedFullKeyMap A).image j (by
      intro u i hi
      obtain ⟨a,ha⟩ := u.property
      have hk : ((nativeMixedFullKeyMap A) a).val = u.val := ha
      exact hk ▸ ((nativeMixedFullKeyMap_vf_zero_iff A a i).mpr (hz a i hi))))

end DiamondIntegral.Section5
