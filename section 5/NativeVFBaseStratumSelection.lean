import «section 5».NativeSelectedVFStrata
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Embedding.Basic

/-! On a prepared base zero stratum, retain its nonzero base coordinates
and every fibre VF coordinate. Deleting only the fixed zero coordinates
gives a genuine native bijection of degree card(I)+k. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k r : ℕ}

def nativeVFBaseStratumSelection (I : Finset (Fin p)) (k : ℕ) : Fin (Fintype.card I+k) ↪ Fin (p+k) :=
  (((finSumFinEquiv : Fin (Fintype.card I) ⊕ Fin k ≃ Fin (Fintype.card I+k)).symm.toEmbedding).trans
    ((nativeVFZeroPatternIndex I).sumMap (Function.Embedding.refl (Fin k)))).trans
      (finSumFinEquiv : Fin p ⊕ Fin k ≃ Fin (p+k)).toEmbedding

theorem nativeVFBaseStratumSelection_left (I : Finset (Fin p)) (k : ℕ) (i : Fin (Fintype.card I)) :
    nativeVFBaseStratumSelection I k (Fin.castAdd k i) = Fin.castAdd k (nativeVFZeroPatternIndex I i) := by
  simp [nativeVFBaseStratumSelection]

theorem nativeVFBaseStratumSelection_right (I : Finset (Fin p)) (k : ℕ) (i : Fin k) :
    nativeVFBaseStratumSelection I k (Fin.natAdd (Fintype.card I) i) = Fin.natAdd p i := by
  simp [nativeVFBaseStratumSelection]

theorem nativeVFBaseStratum_omitted_zero
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r)) (I : Finset (Fin p))
    (a : nativeVFSelectedZeroStratum A (Fin.castAdd k) I) (i : Fin (p+k))
    (hi : i ∉ Set.range (nativeVFBaseStratumSelection I k)) : a.val.1 i = 0 := by
  revert hi
  refine Fin.addCases (fun b => ?_) (fun f => ?_) i
  · intro hi
    have hb : b ∉ I := by
      intro hb
      obtain ⟨j,hj⟩ := (nativeVFZeroPatternIndex_range I b).mpr hb
      exact hi ⟨Fin.castAdd k j,(nativeVFBaseStratumSelection_left I k j).trans (congrArg (Fin.castAdd k) hj)⟩
    by_contra hn
    exact hb ((((nativeVFSelectedZeroStratum_mem A (Fin.castAdd k) I a.val).mp a.property).2 b).mpr hn)
  · intro hi
    exact False.elim (hi ⟨Fin.natAdd (Fintype.card I) f,nativeVFBaseStratumSelection_right I k f⟩)

def nativeVFBaseStratumDropBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r)) (I : Finset (Fin p)) :
    GammaGroundBijection (nativeVFSelectedZeroStratum A (Fin.castAdd k) I)
      (nativeVFCoordinateSelection (nativeVFSelectedZeroStratum A (Fin.castAdd k) I)
        (nativeVFBaseStratumSelection I k)).image :=
  nativeDropZeroVFBijection _ (nativeVFBaseStratumSelection I k) (nativeVFBaseStratum_omitted_zero A I)

theorem nativeVFBaseStratumDrop_pullback
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r)) (hpull : IsRVPullback A.carrier)
    (I : Finset (Fin p)) :
    IsRVPullback (nativeVFCoordinateSelection (nativeVFSelectedZeroStratum A (Fin.castAdd k) I)
      (nativeVFBaseStratumSelection I k)).image.carrier :=
  nativeDropZeroVF_pullback _ (nativeVFSelectedZeroStratum_pullback A hpull (Fin.castAdd k) I)
    (nativeVFBaseStratumSelection I k) (nativeVFBaseStratum_omitted_zero A I)

theorem nativeVFBaseStratumDrop_nonzero
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r))
    (hfib : ∀ a : A,∀ i : Fin k,a.val.1 (Fin.natAdd p i) ≠ 0) (I : Finset (Fin p))
    (a : (nativeVFCoordinateSelection (nativeVFSelectedZeroStratum A (Fin.castAdd k) I)
      (nativeVFBaseStratumSelection I k)).image) (i : Fin (Fintype.card I+k)) : a.val.1 i ≠ 0 := by
  apply nativeDropZeroVF_nonzero _ (nativeVFBaseStratumSelection I k) ?_ a i
  intro b j
  refine Fin.addCases (fun t => ?_) (fun t => ?_) j
  · rw [nativeVFBaseStratumSelection_left]
    exact (((nativeVFSelectedZeroStratum_mem A (Fin.castAdd k) I b.val).mp b.property).2 _).mp
      ((nativeVFZeroPatternIndex_range I _).mp ⟨t,rfl⟩)
  · rw [nativeVFBaseStratumSelection_right]
    exact hfib ⟨b.val,nativeVFSelectedZeroStratum_subset A (Fin.castAdd k) I b.property⟩ t

end DiamondIntegral.Section5
