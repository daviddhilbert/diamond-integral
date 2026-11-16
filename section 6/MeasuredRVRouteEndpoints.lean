import «section 6».MeasuredRVRouteChains
import «section 6».MeasuredRVRestrictionBounds

/-! Actual endpoint identifications join a certified measured route to
the literal restricted original isomorphism. Both identifications are
volume preserving and relatively unary in any available coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

abbrev measuredRVIsomorphismRouteVertex (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n))
    (v : Fin n → Fin (n+n)) (hv : v ∈ C.route.vertices) :=
  measuredRVRouteVertex hc U (rvVolumePoolMap e.iso.hom.map) C
    (rvVolumePoolMap_nonzero e.iso.hom.map U.nonzero V.nonzero) v hv

theorem measuredRVIsomorphismRouteVertex_source_value (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n))
    (u : C.domain (rvVolumePoolMap e.iso.hom.map)) :
    (measuredRVIsomorphismRouteVertex hc e C (productLeft n n) C.route.start_mem).object.value u =
      U.object.value ⟨u.val,C.domain_subset _ u.property⟩ := by
  funext k
  change ((rvVolumePoolMap e.iso.hom.map ⟨u.val,C.domain_subset _ u.property⟩).val (productLeft n n k)) = _
  rw [rvVolumePoolMap_value,productTuple_left]

theorem measuredRVIsomorphismRouteVertex_target_value (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n))
    (u : C.domain (rvVolumePoolMap e.iso.hom.map)) :
    (measuredRVIsomorphismRouteVertex hc e C (productRight n n) C.route.end_mem).object.value u =
      V.object.value (e.iso.hom.map ⟨u.val,C.domain_subset _ u.property⟩) := by
  funext k
  change ((rvVolumePoolMap e.iso.hom.map ⟨u.val,C.domain_subset _ u.property⟩).val (productRight n n k)) = _
  rw [rvVolumePoolMap_value,productTuple_right]

def measuredRVRouteSourceIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n)) :
    MeasuredRVIso (U.restrict (C.domain (rvVolumePoolMap e.iso.hom.map)) (C.domain_subset _))
      (measuredRVIsomorphismRouteVertex hc e C (productLeft n n) C.route.start_mem) where
  iso := rvIsoOfVolumePreservingBijection (Map.id (C.domain (rvVolumePoolMap e.iso.hom.map)))
    Function.bijective_id (measuredRVIsomorphismRouteVertex_source_value hc e C)
  balance u := (measuredRVRouteVertex_totalWeight hc U (rvVolumePoolMap e.iso.hom.map) C
    (rvVolumePoolMap_nonzero e.iso.hom.map U.nonzero V.nonzero) _ _ u).symm

def measuredRVRouteTargetIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n)) :
    MeasuredRVIso (measuredRVIsomorphismRouteVertex hc e C (productRight n n) C.route.end_mem)
      (V.restrict (e.iso.hom.map.restrict (C.domain_subset (rvVolumePoolMap e.iso.hom.map))).image
        (rvLabelImage_subset e.iso _ (C.domain_subset _))) where
  iso := rvIsoOfVolumePreservingBijection
    (e.restrict (C.domain (rvVolumePoolMap e.iso.hom.map)) (C.domain_subset _)).iso.hom.map
    (rvIso_map_bijective (e.restrict (C.domain (rvVolumePoolMap e.iso.hom.map)) (C.domain_subset _)).iso)
    (fun u => (measuredRVIsomorphismRouteVertex_target_value hc e C u).symm)
  balance u := (measuredRVRouteVertex_totalWeight hc U (rvVolumePoolMap e.iso.hom.map) C
    (rvVolumePoolMap_nonzero e.iso.hom.map U.nonzero V.nonzero) _ _ u).trans
      (e.balance ⟨u.val,C.domain_subset _ u.property⟩)

theorem measuredRVRouteSourceIso_unary (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n)) (i : Fin n) :
    RVUnaryRelativeAt (measuredRVRouteSourceIso hc e C).iso.hom.map i := by
  intro u k hk
  exact congrFun (measuredRVIsomorphismRouteVertex_source_value hc e C u) k

theorem measuredRVRouteTargetIso_unary (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (C : RVRouteFiniteData (M := M) S n (n+n) U.object.arity (productLeft n n) (productRight n n)) (i : Fin n) :
    RVUnaryRelativeAt (measuredRVRouteTargetIso hc e C).iso.hom.map i := by
  intro u k hk
  exact (congrFun (measuredRVIsomorphismRouteVertex_target_value hc e C u) k).symm

end DiamondIntegral.Section6
