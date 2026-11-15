import «section 5».NativeVFZeroStrata
import «section 5».NativeZeroStrataPullbacks
import «section 5».NativeFullKeySelections

/-! Zero strata in selected VF coordinates form an actual original-ground
finite partition. Their full RV keys are exactly the matching selected RV
zero strata, and RV-pullbacks stay RV-pullbacks. -/
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

def nativeVFSelectedZeroStratum (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (I : Finset (Fin d)) : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r) :=
  (nativeMixedFullKeyMap A).preimage
    (nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r ∘ j) I)

theorem nativeVFSelectedZeroStratum_mem (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (I : Finset (Fin d)) (q : Section2.Mixed M n r) :
    q ∈ (nativeVFSelectedZeroStratum A j I).carrier ↔
      q ∈ A.carrier ∧ ∀ i : Fin d,i ∈ I ↔ q.1 (j i) ≠ 0 := by
  constructor
  · rintro ⟨a,ha,hI⟩
    have hk := (nativeRVZeroPatternBase_mem _ _ I _).mp hI
    have hp : ∀ i : Fin d,i ∈ I ↔ a.val.1 (j i) ≠ 0 := fun i =>
      (hk.2 i).trans (not_congr (nativeMixedFullKeyMap_vf_zero_iff A a (j i)))
    exact ⟨ha ▸ a.property,ha ▸ hp⟩
  · rintro ⟨hq,hp⟩
    let a : A := ⟨q,hq⟩
    refine ⟨a,rfl,(nativeRVZeroPatternBase_mem _ _ I _).mpr ⟨⟨a,rfl⟩,?_⟩⟩
    intro i
    exact (hp i).trans (not_congr (nativeMixedFullKeyMap_vf_zero_iff A a (j i))).symm

theorem nativeVFSelectedZeroStratum_subset (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (I : Finset (Fin d)) : (nativeVFSelectedZeroStratum A j I).carrier ⊆ A.carrier :=
  fun q hq => ((nativeVFSelectedZeroStratum_mem A j I q).mp hq).1

theorem nativeVFSelectedZeroStratum_disjoint (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (I J : Finset (Fin d)) (hne : I ≠ J) :
    Disjoint (nativeVFSelectedZeroStratum A j I).carrier (nativeVFSelectedZeroStratum A j J).carrier := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hi := ((nativeVFSelectedZeroStratum_mem A j I x).mp hx).2
  have hj := ((nativeVFSelectedZeroStratum_mem A j J x).mp hy).2
  exact hne (Finset.ext (fun i => (hi i).trans (hj i).symm))

theorem nativeVFSelectedZeroStratum_cover (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (x : Section2.Mixed M n r) :
    x ∈ A.carrier ↔ ∃ I : Finset (Fin d),x ∈ (nativeVFSelectedZeroStratum A j I).carrier := by
  constructor
  · intro hx
    let I := Finset.univ.filter (fun i : Fin d => x.1 (j i) ≠ 0)
    refine ⟨I,(nativeVFSelectedZeroStratum_mem A j I x).mpr ⟨hx,?_⟩⟩
    intro i
    simp only [I,Finset.mem_filter,Finset.mem_univ,true_and]
  · rintro ⟨I,hI⟩
    exact nativeVFSelectedZeroStratum_subset A j I hI

theorem nativeVFSelectedZeroStratum_pullback (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (hpull : IsRVPullback A.carrier) (j : Fin d → Fin n) (I : Finset (Fin d)) :
    IsRVPullback (nativeVFSelectedZeroStratum A j I).carrier := by
  apply (isRVPullback_iff _).mpr
  intro x hx y hs
  obtain ⟨hA,hI⟩ := (nativeVFSelectedZeroStratum_mem A j I x).mp hx
  have hselect : SameRV (x.1 ∘ j,x.2) (y.1 ∘ j,y.2) :=
    (sameRV_iff _ _).mpr ⟨fun i => ((sameRV_iff x y).mp hs).1 (j i),((sameRV_iff x y).mp hs).2⟩
  exact (nativeVFSelectedZeroStratum_mem A j I y).mpr
    ⟨(mem_iff_sameRV hpull hs).mp hA,(nativeVFZeroPattern_sameRV I hselect).mp hI⟩

theorem nativeFullKeySelectedZeroStratum_image
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n) (I : Finset (Fin d)) :
    (nativeMixedFullKeyMap (nativeVFSelectedZeroStratum A j I)).image.carrier =
      (nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r ∘ j) I).carrier := by
  ext w
  constructor
  · rintro ⟨a,ha⟩
    have hp := (nativeVFSelectedZeroStratum_mem A j I a.val).mp a.property
    let b : A := ⟨a.val,hp.1⟩
    have hk : ((nativeMixedFullKeyMap A) b).val = w := ha
    refine (nativeRVZeroPatternBase_mem _ _ I w).mpr ⟨⟨b,hk⟩,?_⟩
    intro i
    have hz := nativeMixedFullKeyMap_vf_zero_iff A b (j i)
    rw [hk] at hz
    exact (hp.2 i).trans (not_congr hz).symm
  · intro hw
    obtain ⟨⟨a,ha⟩,hp⟩ := (nativeRVZeroPatternBase_mem _ _ I w).mp hw
    have hk : ((nativeMixedFullKeyMap A) a).val = w := ha
    have hI : ∀ i : Fin d,i ∈ I ↔ a.val.1 (j i) ≠ 0 := by
      intro i
      have hz := nativeMixedFullKeyMap_vf_zero_iff A a (j i)
      rw [hk] at hz
      exact (hp i).trans (not_congr hz)
    exact ⟨⟨a.val,(nativeVFSelectedZeroStratum_mem A j I a.val).mpr ⟨a.property,hI⟩⟩,ha⟩

end DiamondIntegral.Section5
