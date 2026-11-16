import «section 6».RVIndexRouteEndpoints

/-! Permutation edges of a finite certified route have actual measured
relatively unary chains; every intermediate remains doubly bounded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n p : ℕ}

theorem exists_measured_rvRoute_permutation_chain (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) (U : MeasuredRVObject (M := M) S n)
    (pool : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p U.object.arity a b)
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero)
    (v : Fin n → Fin p) (e : Equiv.Perm (Fin n))
    (hv : v ∈ C.route.vertices) (hw : v ∘ e ∈ C.route.vertices) :
    ∃ L : MeasuredRVUnaryChain S n (measuredRVRouteVertex hc U pool C hPool v hv)
        (measuredRVRouteVertex hc U pool C hPool (v ∘ e) hw),
      (∀ u, L.iso.iso.hom.map u = u) ∧
        ((U.doublyBounded ∧ RVValueDoublyBounded (Set.range (fun u : U.object.domain => (pool u).val))) →
          L.doublyBounded) := by
  let A := measuredRVRouteVertex hc U pool C hPool v hv
  let B := measuredRVRouteVertex hc U pool C hPool (v ∘ e) hw
  obtain ⟨T,hT,hTB⟩ := exists_measured_rv_permutation_chain hc hn A e
  let d : MeasuredRVIso (A.reindexVolume e) B := {
    iso := rvIsoOfVolumePreservingBijection (Map.id (C.domain pool)) Function.bijective_id (fun _ => rfl)
    balance u := (A.reindexVolume_totalWeight e u).trans
      ((measuredRVRouteVertex_totalWeight hc U pool C hPool v hv u).trans
        (measuredRVRouteVertex_totalWeight hc U pool C hPool (v ∘ e) hw u).symm) }
  let i : Fin n := ⟨0,hn⟩
  have hd : RVUnaryRelativeAt d.iso.hom.map i := by intro u k hk; rfl
  let H : MeasuredRVUnaryChain S n (A.reindexVolume e) B := .step i d hd (.identity _)
  refine ⟨T.comp H,fun u => ?_,fun hB => ?_⟩
  · rw [MeasuredRVUnaryChain.comp_map,hT]
    rfl
  · have hA := measuredRVRouteVertex_doublyBounded hc U pool C hPool v hv hB.1 hB.2
    exact T.comp_doublyBounded H (hTB hA)
      ⟨rvReindexVolume_doublyBounded A.object e hA,
        measuredRVRouteVertex_doublyBounded hc U pool C hPool (v ∘ e) hw hB.1 hB.2⟩

end DiamondIntegral.Section6
