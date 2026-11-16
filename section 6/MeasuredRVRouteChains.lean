import «section 6».MeasuredRVRoutePermutations

/-! Compile a finite certified route into an actual relatively unary
measured category chain, with the identity label map and conditional
double bounds at every intermediate object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n p : ℕ}

theorem exists_measured_rvRoute_subchain (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) (U : MeasuredRVObject (M := M) S n)
    (pool : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p U.object.arity a b)
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero)
    {v w : Fin n → Fin p} (T : RVIndexRoute n p v w) :
    ∀ hSub : T.vertices ⊆ C.route.vertices,
    ∃ L : MeasuredRVUnaryChain S n
        (measuredRVRouteVertex hc U pool C hPool v (hSub T.start_mem))
        (measuredRVRouteVertex hc U pool C hPool w (hSub T.end_mem)),
      (∀ u, L.iso.iso.hom.map u = u) ∧
        ((U.doublyBounded ∧ RVValueDoublyBounded (Set.range (fun u : U.object.domain => (pool u).val))) →
          L.doublyBounded) := by
  induction T with
  | identity v =>
    intro hSub
    exact ⟨.identity _,fun _ => rfl,fun hB =>
      measuredRVRouteVertex_doublyBounded hc U pool C hPool v _ hB.1 hB.2⟩
  | coordinate v i q T ih =>
    intro hSub
    have hTail : T.vertices ⊆ C.route.vertices := fun z hz => hSub (Finset.mem_insert_of_mem hz)
    obtain ⟨L,hL,hLB⟩ := ih hTail
    let d := measuredRVRouteVertexIso hc U pool C hPool v (Function.update v i q)
      (hSub (Finset.mem_insert_self _ _)) (hTail T.start_mem)
    have hd : RVUnaryRelativeAt d.iso.hom.map i :=
      measuredRVRouteVertexIso_unary hc U pool C hPool v (Function.update v i q) _ _ i
        (fun k hk => Function.update_of_ne hk q v)
    refine ⟨.step i d hd L,fun u => hL u,fun hB => ?_⟩
    exact ⟨measuredRVRouteVertex_doublyBounded hc U pool C hPool v _ hB.1 hB.2,hLB hB⟩
  | reindex v e T ih =>
    intro hSub
    have hTail : T.vertices ⊆ C.route.vertices := fun z hz => hSub (Finset.mem_insert_of_mem hz)
    obtain ⟨L,hL,hLB⟩ := ih hTail
    obtain ⟨H,hH,hHB⟩ := exists_measured_rvRoute_permutation_chain hc hn U pool C hPool v e
      (hSub (Finset.mem_insert_self _ _)) (hTail T.start_mem)
    refine ⟨H.comp L,fun u => ?_,fun hB => H.comp_doublyBounded L (hHB hB) (hLB hB)⟩
    rw [MeasuredRVUnaryChain.comp_map,hH,hL]

end DiamondIntegral.Section6
