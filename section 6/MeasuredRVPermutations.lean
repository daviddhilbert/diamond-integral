import «section 6».MeasuredRVTranspositions
import «section 6».FiniteRVReplacementBounds
import Mathlib.GroupTheory.Perm.Sign

/-! Every structural coordinate permutation has an actual measured
relatively unary factorization, in arbitrary positive degree and without
a finite-label hypothesis. Double bounds hold throughout the chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def measuredReindexVolumeCompIso (U : MeasuredRVObject (M := M) S n)
    (e f : Equiv.Perm (Fin n)) :
    MeasuredRVIso ((U.reindexVolume e).reindexVolume f) (U.reindexVolume (e*f)) where
  iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id (fun _ => rfl)
  balance u := ((U.reindexVolume e).reindexVolume_totalWeight f u).trans
    ((U.reindexVolume_totalWeight e u).trans (U.reindexVolume_totalWeight (e*f) u).symm)

theorem exists_measured_rv_permutation_chain (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) (U : MeasuredRVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    ∃ T : MeasuredRVUnaryChain S n U (U.reindexVolume e),
      (∀ u, T.iso.iso.hom.map u = u) ∧ (U.doublyBounded → T.doublyBounded) := by
  induction e using Equiv.Perm.swap_induction_on' with
  | one =>
    let d : MeasuredRVIso U (U.reindexVolume 1) := {
      iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id (fun _ => rfl)
      balance u := (U.reindexVolume_totalWeight 1 u).symm }
    let i : Fin n := ⟨0,hn⟩
    have hd : RVUnaryRelativeAt d.iso.hom.map i := by intro u k hk; rfl
    exact ⟨.step i d hd (.identity _),fun _ => rfl,
      fun hU => ⟨hU,rvReindexVolume_doublyBounded U.object _ hU⟩⟩
  | mul_swap e i j hij ih =>
    obtain ⟨T,hT,hTB⟩ := ih
    obtain ⟨H,hH,hHB⟩ := exists_measured_rv_transposition_chain hc (U.reindexVolume e) i j hij
    let d := measuredReindexVolumeCompIso U e (Equiv.swap i j)
    have hd : RVUnaryRelativeAt d.iso.hom.map i := by intro u k hk; rfl
    let K : MeasuredRVUnaryChain S n ((U.reindexVolume e).reindexVolume (Equiv.swap i j))
        (U.reindexVolume (e * Equiv.swap i j)) := .step i d hd (.identity _)
    refine ⟨(T.comp H).comp K,fun u => ?_,fun hU => ?_⟩
    · rw [MeasuredRVUnaryChain.comp_map,MeasuredRVUnaryChain.comp_map,hT,hH]
      rfl
    · have heB : (U.reindexVolume e).doublyBounded := rvReindexVolume_doublyBounded U.object e hU
      have hefB : ((U.reindexVolume e).reindexVolume (Equiv.swap i j)).doublyBounded :=
        rvReindexVolume_doublyBounded (U.reindexVolume e).object _ heB
      exact (T.comp H).comp_doublyBounded K (T.comp_doublyBounded H (hTB hU) (hHB heB))
        ⟨hefB,rvReindexVolume_doublyBounded U.object _ hU⟩

end DiamondIntegral.Section6
