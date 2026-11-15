import «section 5».NativeVFZeroStrata
import «section 5».NativePullbackRVPresentation

/-! Fixed zero VF strata and removal of their zero coordinates preserve
the actual RV-pullback property. Consequently every finite-RV-fibre
RV-pullback has finite original-ground positive RV lift presentations,
with degree equal to the number of remaining nonzero VF coordinates. -/
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
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r d : ℕ}

theorem nativeVFZeroPattern_sameRV (I : Finset (Fin n)) {x y : Point (M := M) n r} (h : SameRV x y) :
    nativeVFZeroPattern I x ↔ nativeVFZeroPattern I y := by
  have hz (i : Fin n) : x.1 i = 0 ↔ y.1 i = 0 := by
    have hr : rvValues (Section2.tupleRV M x.1) i = rvValues (Section2.tupleRV M y.1) i :=
      congrArg Subtype.val (((sameRV_iff x y).mp h).1 i)
    rw [←rvValues_tupleRV_zero_iff x.1 i,←rvValues_tupleRV_zero_iff y.1 i,hr]
  exact forall_congr' (fun i => iff_congr Iff.rfl (not_congr (hz i)))

theorem nativeVFZeroStratum_pullback
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (I : Finset (Fin n)) : IsRVPullback (nativeVFZeroStratum A I).carrier := by
  apply (isRVPullback_iff _).mpr
  intro x hx y hsame
  have h := (nativeVFZeroStratum_mem A I x).mp hx
  exact (nativeVFZeroStratum_mem A I y).mpr
    ⟨(mem_iff_sameRV hpull hsame).mp h.1,(nativeVFZeroPattern_sameRV I hsame).mp h.2⟩

def nativeVFFillCoordinates (j : Fin d ↪ Fin n) (x : Fin d → Section2.VF M) (i : Fin n) : Section2.VF M :=
  if h : ∃ t : Fin d,j t = i then x h.choose else 0

theorem nativeVFFillCoordinates_selected (j : Fin d ↪ Fin n) (x : Fin d → Section2.VF M) (i : Fin d) :
    nativeVFFillCoordinates j x (j i) = x i := by
  unfold nativeVFFillCoordinates
  have h : ∃ t : Fin d,j t = j i := ⟨i,rfl⟩
  rw [dif_pos h,j.injective h.choose_spec]

theorem nativeVFFillCoordinates_zero (j : Fin d ↪ Fin n) (x : Fin d → Section2.VF M) (i : Fin n)
    (hi : i ∉ Set.range j) : nativeVFFillCoordinates j x i = 0 := by
  exact dif_neg hi

theorem nativeDropZeroVF_pullback
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (j : Fin d ↪ Fin n) (hzero : ∀ a : A,∀ i : Fin n,i ∉ Set.range j → a.val.1 i = 0) :
    IsRVPullback (nativeVFCoordinateSelection A j).image.carrier := by
  apply (isRVPullback_iff _).mpr
  rintro x ⟨a,ha⟩ y hsame
  have hxa : (a.val.1 ∘ j,a.val.2) = x :=
    (nativeVFCoordinateSelection_value A j a).symm.trans ha
  have hs : SameRV (a.val.1 ∘ j,a.val.2) y := hxa.symm ▸ hsame
  let z : Point (M := M) n r := (nativeVFFillCoordinates j y.1,y.2)
  have hsz : SameRV a.val z := by
    obtain ⟨hv,hr⟩ := (sameRV_iff _ _).mp hs
    apply (sameRV_iff _ _).mpr
    refine ⟨?_,hr⟩
    intro i
    by_cases hi : i ∈ Set.range j
    · obtain ⟨t,rfl⟩ := hi
      change rv (a.val.1 (j t)) = rv (nativeVFFillCoordinates j y.1 (j t))
      rw [nativeVFFillCoordinates_selected]
      exact hv t
    · change rv (a.val.1 i) = rv (nativeVFFillCoordinates j y.1 i)
      rw [hzero a i hi,nativeVFFillCoordinates_zero j y.1 i hi]
  have hz : z ∈ A.carrier := (mem_iff_sameRV hpull hsz).mp a.property
  refine ⟨⟨z,hz⟩,?_⟩
  change ((nativeVFCoordinateSelection A j) ⟨z,hz⟩).val = y
  rw [nativeVFCoordinateSelection_value]
  exact Prod.ext (funext (fun i => nativeVFFillCoordinates_selected j y.1 i)) rfl

theorem nativeVFZeroStratumDrop_pullback
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (I : Finset (Fin n)) :
    IsRVPullback (nativeVFCoordinateSelection (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I)).image.carrier :=
  nativeDropZeroVF_pullback (nativeVFZeroStratum A I) (nativeVFZeroStratum_pullback A hpull I)
    (nativeVFZeroPatternIndex I) (by
      intro a i hi
      by_contra hn
      exact hi ((nativeVFZeroPatternIndex_range I i).mpr
        ((((nativeVFZeroStratum_mem A I a.val).mp a.property).2 i).mpr hn)))

def nativeVFZeroStratumRVObject
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) (I : Finset (Fin n)) :
    GammaGroundRVObject hc B (Fintype.card I) :=
  nativePullbackRVObject hκ hs h00 hr
    (nativeVFCoordinateSelection (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I)).image
    (nativeVFZeroStratumDrop_pullback A hpull I) (nativeVFZeroStratumDrop_finite hκ hs h00 hr A hf I)
    (nativeVFZeroStratumDrop_nonzero A I)

def nativeVFZeroStratum_lift_bijection
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) (I : Finset (Fin n)) :
    GammaGroundBijection (nativeVFZeroStratum A I)
      (gammaGroundObjectLift (nativeVFZeroStratumRVObject hκ hs h00 hr A hpull hf I)) :=
  (nativePullbackRVObject_lift_bijection hκ hs h00 hr
    (nativeVFCoordinateSelection (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I)).image
    (nativeVFZeroStratumDrop_pullback A hpull I) (nativeVFZeroStratumDrop_finite hκ hs h00 hr A hf I)
    (nativeVFZeroStratumDrop_nonzero A I)).comp (nativeVFZeroStratumDropBijection A I)

end DiamondIntegral.Section5
