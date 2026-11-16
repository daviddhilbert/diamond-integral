import «section 6».MeasuredVFTranspositions
import «section 6».MeasuredRVPermutations

/-! Every VF coordinate permutation has an actual everywhere measured
relatively unary VF chain. All intermediate double bounds are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_vf_permutation_chain (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) (U : MeasuredRVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    ∃ T : MeasuredVFUnaryLiftChain S n U (U.reindexVolume e),
      (∀ u,T.iso.iso.hom.map u=u) ∧ (U.doublyBounded → T.doublyBounded) := by
  induction e using Equiv.Perm.swap_induction_on' with
  | one =>
    let d : MeasuredRVIso U (U.reindexVolume 1) := {
      iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id (fun _ => rfl)
      balance u := (U.reindexVolume_totalWeight 1 u).symm }
    let i : Fin n := ⟨0,hn⟩
    let F := volumePreservingMeasuredRVLift d (fun _ => rfl)
    exact ⟨.step i F (volumePreservingMeasuredRVLift_unary d _ i) (.identity _),fun _ => rfl,
      fun hU => ⟨hU,rvReindexVolume_doublyBounded U.object _ hU⟩⟩
  | mul_swap e i j hij ih =>
    obtain ⟨T,hT,hTB⟩ := ih
    obtain ⟨H,hH,hHB⟩ := exists_measured_vf_transposition_chain hc (U.reindexVolume e) i j hij
    let d := measuredReindexVolumeCompIso U e (Equiv.swap i j)
    let F := volumePreservingMeasuredRVLift d (fun _ => rfl)
    let K : MeasuredVFUnaryLiftChain S n ((U.reindexVolume e).reindexVolume (Equiv.swap i j))
        (U.reindexVolume (e*Equiv.swap i j)) :=
      .step i F (volumePreservingMeasuredRVLift_unary d _ i) (.identity _)
    refine ⟨(T.comp H).comp K,fun u => ?_,fun hU => ?_⟩
    · rw [MeasuredVFUnaryLiftChain.comp_map,MeasuredVFUnaryLiftChain.comp_map,hT,hH]
      rfl
    · have heB := rvReindexVolume_doublyBounded U.object e hU
      have hefB := rvReindexVolume_doublyBounded (U.reindexVolume e).object (Equiv.swap i j) heB
      exact (T.comp H).comp_doublyBounded K (T.comp_doublyBounded H (hTB hU) (hHB heB))
        ⟨hefB,rvReindexVolume_doublyBounded U.object _ hU⟩

theorem exists_measured_vf_inverse_permutation_chain (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) (U : MeasuredRVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    ∃ T : MeasuredVFUnaryLiftChain S n (U.reindexVolume e) U,
      (∀ u,T.iso.iso.hom.map u=u) ∧ (U.doublyBounded → T.doublyBounded) := by
  obtain ⟨T,hT,hTB⟩ := exists_measured_vf_permutation_chain hc hn (U.reindexVolume e) e.symm
  let d : MeasuredRVIso ((U.reindexVolume e).reindexVolume e.symm) U := {
    iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id (fun u => by
      funext k
      change U.object.value u k=U.object.value u (e (e.symm k))
      rw [e.apply_symm_apply])
    balance u := ((U.reindexVolume e).reindexVolume_totalWeight e.symm u).trans
      (U.reindexVolume_totalWeight e u) }
  have hVol (u : U.object.domain) : U.object.value u=
      ((U.reindexVolume e).reindexVolume e.symm).object.value u := by
    funext k
    change U.object.value u k=U.object.value u (e (e.symm k))
    rw [e.apply_symm_apply]
  let F := volumePreservingMeasuredRVLift d hVol
  let i : Fin n := ⟨0,hn⟩
  let H : MeasuredVFUnaryLiftChain S n ((U.reindexVolume e).reindexVolume e.symm) U :=
    .step i F (volumePreservingMeasuredRVLift_unary d hVol i) (.identity _)
  refine ⟨T.comp H,fun u => ?_,fun hU => ?_⟩
  · rw [MeasuredVFUnaryLiftChain.comp_map,hT]
    rfl
  · have hB := rvReindexVolume_doublyBounded U.object e hU
    exact T.comp_doublyBounded H (hTB hB)
      ⟨rvReindexVolume_doublyBounded (U.reindexVolume e).object e.symm hB,hU⟩

end DiamondIntegral.Section6
