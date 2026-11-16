import «section 6».MeasuredRVRouteEndpoints

/-! Actual measured relatively unary factorizations on the finite
original-base route cover. Every local chain has the prescribed label
map and retains all intermediate bounds when the endpoints are bounded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_rv_factorization_on_route (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n)) :
    ∃ L : MeasuredRVUnaryChain S n
        (U.restrict (C.domain (rvVolumePoolMap e.iso.hom.map)) (C.domain_subset _))
        (V.restrict (e.iso.hom.map.restrict (C.domain_subset (rvVolumePoolMap e.iso.hom.map))).image
          (rvLabelImage_subset e.iso _ (C.domain_subset _))),
      L.iso.iso.hom.map = (e.restrict (C.domain (rvVolumePoolMap e.iso.hom.map)) (C.domain_subset _)).iso.hom.map ∧
        ((U.doublyBounded ∧ V.doublyBounded) → L.doublyBounded) := by
  let pool := rvVolumePoolMap e.iso.hom.map
  let hPool := rvVolumePoolMap_nonzero e.iso.hom.map U.nonzero V.nonzero
  obtain ⟨T,hT,hTB⟩ := exists_measured_rvRoute_subchain hc hn U pool C hPool C.route (Finset.Subset.refl _)
  let i : Fin n := ⟨0,hn⟩
  let a := measuredRVRouteSourceIso hc e C
  let b := measuredRVRouteTargetIso hc e C
  let H : MeasuredRVUnaryChain S n
      (measuredRVIsomorphismRouteVertex hc e C (productRight n n) C.route.end_mem) _ :=
    .step i b (measuredRVRouteTargetIso_unary hc e C i) (.identity _)
  let L : MeasuredRVUnaryChain S n _ _ :=
    .step i a (measuredRVRouteSourceIso_unary hc e C i) (T.comp H)
  refine ⟨L,?_,fun hB => ?_⟩
  · apply Map.ext
    intro u
    change (T.comp H).iso.iso.hom.map u = _
    rw [MeasuredRVUnaryChain.comp_map,hT]
    rfl
  · have hPB := rvVolumePoolMap_doublyBounded e.iso.hom.map hB.1 hB.2
    refine ⟨U.restrict_doublyBounded _ _ hB.1,T.comp_doublyBounded H (hTB ⟨hB.1,hPB⟩) ?_⟩
    exact ⟨measuredRVRouteVertex_doublyBounded hc U pool C hPool _ _ hB.1 hPB,
      V.restrict_doublyBounded _ _ hB.2⟩

theorem exists_measured_rv_factorizations_on_finite_cover
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hn : 0 < n) {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) :
    ∃ r : ℕ, ∃ D : Fin r → DefSet (rawRVSpace (M := M) U.object.arity) S,
      ∃ hD : ∀ j, (D j).carrier ⊆ U.object.domain.carrier,
      (∀ u : U.object.domain, ∃ j, u.val ∈ (D j).carrier) ∧
      ∀ j, ∃ L : MeasuredRVUnaryChain S n (U.restrict (D j) (hD j))
          (V.restrict (e.iso.hom.map.restrict (hD j)).image (rvLabelImage_subset e.iso (D j) (hD j))),
        L.iso.iso.hom.map = (e.restrict (D j) (hD j)).iso.hom.map ∧
          ((U.doublyBounded ∧ V.doublyBounded) → L.doublyBounded) := by
  obtain ⟨r,C,hCover⟩ := exists_finite_rvIso_route_cover hc h00 hκ hs hsmall e.iso U.finiteVolume V.finiteVolume
  exact ⟨r,fun j => (C j).domain (rvVolumePoolMap e.iso.hom.map),
    fun j => (C j).domain_subset _,hCover,fun j => exists_measured_rv_factorization_on_route hc hn e (C j)⟩

end DiamondIntegral.Section6
