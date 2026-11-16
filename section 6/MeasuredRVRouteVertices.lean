import «section 6».RVRouteVolumeGeometry
import «section 6».MeasuredRVRestrictions

/-! Constructed measured forms at certified route vertices. Every
identity-label transition retains the same original total weight. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n p : ℕ}

def measuredRVRouteVertex (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (pool : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p U.object.arity a b)
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero) (v : Fin n → Fin p) (hv : v ∈ C.route.vertices) :
    MeasuredRVObject (M := M) S n :=
  (U.restrict (C.domain pool) (C.domain_subset pool)).withVolume hc
    (C.vertexObject pool v).volume (C.vertexObject_finiteVolume pool ⟨v,hv⟩)
    (C.vertexObject_nonzero pool hPool v)

theorem measuredRVRouteVertex_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (pool : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p U.object.arity a b)
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero) (v : Fin n → Fin p) (hv : v ∈ C.route.vertices)
    (u : C.domain pool) :
    (measuredRVRouteVertex hc U pool C hPool v hv).totalWeight u =
      U.totalWeight ⟨u.val,C.domain_subset pool u.property⟩ :=
  MeasuredRVObject.withVolume_totalWeight hc (U.restrict (C.domain pool) (C.domain_subset pool))
    (C.vertexObject pool v).volume (C.vertexObject_finiteVolume pool ⟨v,hv⟩)
    (C.vertexObject_nonzero pool hPool v) u

def measuredRVRouteVertexIso (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (pool : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p U.object.arity a b)
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero)
    (v w : Fin n → Fin p) (hv : v ∈ C.route.vertices) (hw : w ∈ C.route.vertices) :
    MeasuredRVIso (measuredRVRouteVertex hc U pool C hPool v hv) (measuredRVRouteVertex hc U pool C hPool w hw) where
  iso := rvIsoOfFiniteVolumeNonzero (Map.id (C.domain pool)) Function.bijective_id
    (C.vertexObject_finiteVolume pool ⟨v,hv⟩) (C.vertexObject_finiteVolume pool ⟨w,hw⟩)
    (C.vertexObject_nonzero pool hPool v) (C.vertexObject_nonzero pool hPool w)
  balance u := (measuredRVRouteVertex_totalWeight hc U pool C hPool v hv u).trans
    (measuredRVRouteVertex_totalWeight hc U pool C hPool w hw u).symm

theorem measuredRVRouteVertexIso_unary (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (pool : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p U.object.arity a b)
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero)
    (v w : Fin n → Fin p) (hv : v ∈ C.route.vertices) (hw : w ∈ C.route.vertices)
    (i : Fin n) (hvw : ∀ k, k ≠ i → w k = v k) :
    RVUnaryRelativeAt (measuredRVRouteVertexIso hc U pool C hPool v w hv hw).iso.hom.map i := by
  intro u k hk
  exact congrArg ((pool ⟨u.val,C.domain_subset pool u.property⟩).val) (hvw k hk)

theorem measuredRVRouteVertex_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (pool : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p U.object.arity a b)
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero) (v : Fin n → Fin p) (hv : v ∈ C.route.vertices)
    (hU : U.doublyBounded) (hB : RVValueDoublyBounded (Set.range (fun u : U.object.domain => (pool u).val))) :
    (measuredRVRouteVertex hc U pool C hPool v hv).doublyBounded :=
  C.vertexObject_doublyBounded pool hU.1 hB v

end DiamondIntegral.Section6
