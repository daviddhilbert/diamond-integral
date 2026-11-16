import «section 6».RVRouteFiniteData
import «section 6».FinitePresentedCovers

/-! Finite original-base route covers for arbitrary finite-volume RV
isomorphisms. Every selected volume along every route has actual finite
fibres on its corresponding definable piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvVolumePoolMap {U V : RVObject (M := M) S n} (F : Map U.domain V.domain) :
    Map U.domain (DefSet.univ (rawRVSpace (M := M) (n+n)) S) := (volumePairMap F).toUniv

theorem rvVolumePoolMap_value {U V : RVObject (M := M) S n}
    (F : Map U.domain V.domain) (u : U.domain) :
    (rvVolumePoolMap F u).val = productTuple (U.value u) (V.value (F u)) := volumePairMap_apply F u

theorem exists_rvIsoRouteFiniteData_at (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres) (u : U.domain) :
    ∃ C : RVRouteFiniteData (M := M) S n (n+n) U.arity (productLeft n n) (productRight n n),
      u.val ∈ (C.domain (rvVolumePoolMap e.hom.map)).carrier := by
  let pool := productTuple (U.value u) (V.value (e.hom.map u))
  obtain ⟨T,hT⟩ := exists_rvIndexRoute_of_span_path hc hex S pool
    (rvIso_pointwise_volume_span_path hc hex e hU hV u)
  have hBase : pool ∘ productLeft n n = U.value u := funext (productTuple_left _ _)
  have hAlg : ∀ v ∈ T.vertices, ∀ j,
      AlgebraicAt (S ∪ Set.range (rvValues (((rvVolumePoolMap e.hom.map) u).val ∘ v))) .rv (u.val j).val := by
    intro v hv j
    rw [rvVolumePoolMap_value]
    apply (rv_algebraic_iff_mem_tuple_closure hc hex S (pool ∘ v) (u.val j)).mpr
    have hCl := (T.all_iff _).mp hT v hv
    rw [hBase] at hCl
    change u.val j ∈ rvTupleClosure hc hex S (pool ∘ v)
    rw [hCl]
    exact (rv_algebraic_iff_mem_tuple_closure hc hex S (U.value u) (u.val j)).mp
      (finite_map_rv_coordinate_algebraic hc U.volume hU u j)
  obtain ⟨C,hC,hu⟩ := exists_rvRouteFiniteData_at (rvVolumePoolMap e.hom.map) T u hAlg
  exact ⟨C,hu⟩

theorem exists_finite_rvIso_route_cover (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) {U V : RVObject (M := M) S n}
    (e : U ≅ V) (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres) :
    ∃ r : ℕ, ∃ C : Fin r → RVRouteFiniteData (M := M) S n (n+n) U.arity (productLeft n n) (productRight n n),
      ∀ u : U.domain, ∃ j, u.val ∈ ((C j).domain (rvVolumePoolMap e.hom.map)).carrier := by
  exact exists_finite_presented_subcover hs hsmall U.domain
    (fun C : RVRouteFiniteData (M := M) S n (n+n) U.arity (productLeft n n) (productRight n n) =>
      C.domain (rvVolumePoolMap e.hom.map))
    (exists_rvIsoRouteFiniteData_at hc (rvExchangeInput_of_earlier hκ hs h00) e hU hV)

end DiamondIntegral.Section6
