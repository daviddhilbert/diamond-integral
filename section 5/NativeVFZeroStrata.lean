import «section 5».NativeMixedKeyMaps
import «section 5».NativeRVZeroPatternBases
import «section 5».NativeVFCoordinateSelection
import «section 3».GammaGroundFiniteFibreInvariance

/-! Actual mixed VF domains split into finitely many original-ground
zero strata. Dropping precisely the fixed zero VF coordinates gives an
actual native bijection, retains every RV label and leaves all displayed
VF coordinates nonzero. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def nativeVFZeroPattern (I : Finset (Fin n)) (q : Section2.Mixed M n r) : Prop :=
  ∀ i : Fin n,i ∈ I ↔ q.1 i ≠ 0

def nativeVFZeroStratum (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (I : Finset (Fin n)) : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r) :=
  (nativeMixedFullKeyMap A).preimage
    (nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r) I)

theorem nativeVFZeroStratum_mem (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (I : Finset (Fin n)) (q : Section2.Mixed M n r) :
    q ∈ (nativeVFZeroStratum A I).carrier ↔ q ∈ A.carrier ∧ nativeVFZeroPattern I q := by
  constructor
  · rintro ⟨a,ha,hI⟩
    have hkey := (nativeRVZeroPatternBase_mem (nativeMixedFullKeyMap A).image (Fin.castAdd r) I _).mp hI
    have hp : nativeVFZeroPattern I a.val := fun i =>
      (hkey.2 i).trans (not_congr (nativeMixedFullKeyMap_vf_zero_iff A a i))
    exact ⟨ha ▸ a.property,ha ▸ hp⟩
  · rintro ⟨hq,hp⟩
    let a : A := ⟨q,hq⟩
    refine ⟨a,rfl,(nativeRVZeroPatternBase_mem (nativeMixedFullKeyMap A).image (Fin.castAdd r) I _).mpr
      ⟨⟨a,rfl⟩,?_⟩⟩
    intro i
    exact (hp i).trans (not_congr (nativeMixedFullKeyMap_vf_zero_iff A a i)).symm

theorem nativeVFZeroStratum_subset (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (I : Finset (Fin n)) : (nativeVFZeroStratum A I).carrier ⊆ A.carrier :=
  fun q hq => ((nativeVFZeroStratum_mem A I q).mp hq).1

theorem nativeVFZeroStratum_disjoint (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (I J : Finset (Fin n)) (hne : I ≠ J) : Disjoint (nativeVFZeroStratum A I).carrier (nativeVFZeroStratum A J).carrier := by
  apply Set.disjoint_left.mpr
  intro q hI hJ
  have hi := ((nativeVFZeroStratum_mem A I q).mp hI).2
  have hj := ((nativeVFZeroStratum_mem A J q).mp hJ).2
  exact hne (Finset.ext (fun i => (hi i).trans (hj i).symm))

theorem nativeVFZeroStratum_cover (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (q : Section2.Mixed M n r) : q ∈ A.carrier ↔ ∃ I : Finset (Fin n),q ∈ (nativeVFZeroStratum A I).carrier := by
  constructor
  · intro hq
    let I := Finset.univ.filter (fun i : Fin n => q.1 i ≠ 0)
    refine ⟨I,(nativeVFZeroStratum_mem A I q).mpr ⟨hq,?_⟩⟩
    intro i
    simp only [I,Finset.mem_filter,Finset.mem_univ,true_and]
  · rintro ⟨I,hI⟩
    exact nativeVFZeroStratum_subset A I hI

def nativeVFZeroPatternIndex (I : Finset (Fin n)) : Fin (Fintype.card I) ↪ Fin n where
  toFun i := ((Fintype.equivFin I).symm i).val
  inj' := fun i j h => (Fintype.equivFin I).symm.injective (Subtype.ext h)

theorem nativeVFZeroPatternIndex_range (I : Finset (Fin n)) (i : Fin n) :
    i ∈ Set.range (nativeVFZeroPatternIndex I) ↔ i ∈ I := by
  constructor
  · rintro ⟨j,rfl⟩
    exact ((Fintype.equivFin I).symm j).property
  · intro hi
    refine ⟨(Fintype.equivFin I) ⟨i,hi⟩,?_⟩
    change ((Fintype.equivFin I).symm ((Fintype.equivFin I) ⟨i,hi⟩)).val = i
    rw [Equiv.symm_apply_apply]

def nativeVFZeroStratumDropBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (I : Finset (Fin n)) :
    GammaGroundBijection (nativeVFZeroStratum A I)
      (nativeVFCoordinateSelection (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I)).image :=
  nativeDropZeroVFBijection (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I) (by
    intro a i hi
    by_contra hn
    exact hi ((nativeVFZeroPatternIndex_range I i).mpr
      ((((nativeVFZeroStratum_mem A I a.val).mp a.property).2 i).mpr hn)))

theorem nativeVFZeroStratumDrop_nonzero
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (I : Finset (Fin n))
    (a : (nativeVFCoordinateSelection (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I)).image)
    (i : Fin (Fintype.card I)) : a.val.1 i ≠ 0 :=
  nativeDropZeroVF_nonzero (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I)
    (fun a i => (((nativeVFZeroStratum_mem A I a.val).mp a.property).2 _).mp
      ((nativeVFZeroPatternIndex_range I _).mp ⟨i,rfl⟩)) a i

theorem nativeVFZeroStratumDrop_finite
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite)
    (I : Finset (Fin n)) :
    ∀ x : Fin (Fintype.card I) → Section2.VF M,
      {t | (x,t) ∈ (nativeVFCoordinateSelection (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I)).image.carrier}.Finite :=
  (gammaGroundFiniteRVFibres_iff (nativeVFZeroStratumDropBijection A I) hκ hs h00 hr).mp
    (fun x => (hf x).subset (fun _ ht => nativeVFZeroStratum_subset A I ht))

end DiamondIntegral.Section5
