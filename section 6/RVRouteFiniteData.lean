import «section 6».RVIndexRoutes
import «section 6».FiniteDefSetIntersections

/-! Finite relation certificates for all volumes along a coordinate
route. Their common domain is definable over the original base, and
every visited structural volume has proved finite fibres there. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n p m : ℕ}

def rvSelectedVolumeMap {A : DefSet (rawRVSpace (M := M) m) S}
    (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S)) (v : Fin n → Fin p) :=
  (rvTupleSelectMap S v).comp pool

structure RVRouteFiniteData (S : Set M) (n p m : ℕ) (a b : Fin n → Fin p) where
  route : RVIndexRoute n p a b
  relation : (v : {v // v ∈ route.vertices}) → Fin m → RawClosure.Tuple.GoodRelation (n := n) S

def RVRouteFiniteData.domain {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p m a b)
    {A : DefSet (rawRVSpace (M := M) m) S} (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S)) :
    DefSet (rawRVSpace (M := M) m) S :=
  finiteDefSetIntersection A (fun v : {v // v ∈ C.route.vertices} =>
    rvFiniteVolumeLocus (rvSelectedVolumeMap pool v.val) (C.relation v))

theorem RVRouteFiniteData.domain_subset {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p m a b)
    {A : DefSet (rawRVSpace (M := M) m) S} (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S)) :
    (C.domain pool).carrier ⊆ A.carrier := fun _ h => h.1

theorem RVRouteFiniteData.domain_mem {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p m a b)
    {A : DefSet (rawRVSpace (M := M) m) S} (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S)) (u : A) :
    u.val ∈ (C.domain pool).carrier ↔
      ∀ (v : {v // v ∈ C.route.vertices}) j,
        (rvValues ((pool u).val ∘ v.val),(u.val j).val) ∈ (C.relation v j).val := by
  constructor
  · intro h v
    exact (rvFiniteVolumeLocus_mem (rvSelectedVolumeMap pool v.val) (C.relation v) u).mp (h.2 v)
  · intro h
    exact ⟨u.property,fun v =>
      (rvFiniteVolumeLocus_mem (rvSelectedVolumeMap pool v.val) (C.relation v) u).mpr (h v)⟩

theorem RVRouteFiniteData.volume_finite {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p m a b)
    {A : DefSet (rawRVSpace (M := M) m) S} (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S))
    (v : {v // v ∈ C.route.vertices}) :
    ((rvSelectedVolumeMap pool v.val).restrict (C.domain_subset pool)).FiniteFibres := by
  have hSub : (C.domain pool).carrier ⊆
      (rvFiniteVolumeLocus (rvSelectedVolumeMap pool v.val) (C.relation v)).carrier := fun _ h => h.2 v
  exact (rvFiniteVolumeLocus_finite (rvSelectedVolumeMap pool v.val) (C.relation v)).restrict hSub

theorem exists_rvRouteFiniteData_at
    {A : DefSet (rawRVSpace (M := M) m) S} (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S))
    {a b : Fin n → Fin p} (T : RVIndexRoute n p a b) (u : A)
    (hAlg : ∀ v ∈ T.vertices, ∀ j,
      AlgebraicAt (S ∪ Set.range (rvValues ((pool u).val ∘ v))) .rv (u.val j).val) :
    ∃ C : RVRouteFiniteData (M := M) S n p m a b, C.route = T ∧ u.val ∈ (C.domain pool).carrier := by
  choose R hR using fun (v : {v // v ∈ T.vertices}) j =>
    RawClosure.Tuple.good_relation_of_algebraic S (rvValues ((pool u).val ∘ v.val))
      (u.val j).val (hAlg v.val v.property j).raw_finite_witness
  let C : RVRouteFiniteData (M := M) S n p m a b := ⟨T,R⟩
  exact ⟨C,rfl,(C.domain_mem pool u).mpr hR⟩

end DiamondIntegral.Section6
