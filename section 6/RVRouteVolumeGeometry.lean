import «section 6».RVIsomorphismRouteCovers

/-! Actual nonzero finite-volume objects at every certified route
vertex. All selected coordinates inherit the original endpoint double
bounds on both the label domain and structural volume image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n p m : ℕ}

theorem rvVolumePoolMap_nonzero {U V : RVObject (M := M) S n} (F : Map U.domain V.domain)
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero) (hV : ∀ v k, (V.value v k).val ≠ iRVZero)
    (u : U.domain) (k : Fin (n+n)) : ((rvVolumePoolMap F u).val k).val ≠ iRVZero := by
  rw [rvVolumePoolMap_value]
  obtain ⟨j | j,rfl⟩ := finSumFinEquiv.surjective k
  · change (productTuple (U.value u) (V.value (F u)) (productLeft n n j)).val ≠ iRVZero
    rw [productTuple_left]
    exact hU u j
  · change (productTuple (U.value u) (V.value (F u)) (productRight n n j)).val ≠ iRVZero
    rw [productTuple_right]
    exact hV (F u) j

theorem rvVolumePoolMap_doublyBounded {U V : RVObject (M := M) S n} (F : Map U.domain V.domain)
    (hU : RVObjectDoublyBounded U) (hV : RVObjectDoublyBounded V) :
    RVValueDoublyBounded (Set.range (fun u : U.domain => (rvVolumePoolMap F u).val)) := by
  obtain ⟨γ,hγ⟩ := hU.2
  obtain ⟨δ,hδ⟩ := hV.2
  let ε := max γ δ
  have hγlo : (ε⁻¹).val ≤ (γ⁻¹).val := show ε⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have hδlo : (ε⁻¹).val ≤ (δ⁻¹).val := show ε⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
  refine ⟨ε,?_⟩
  rintro t ⟨u,rfl⟩ k
  change (ε⁻¹).val ≤ Values.vrv ((rvVolumePoolMap F u).val k) ∧
    Values.vrv ((rvVolumePoolMap F u).val k) ≤ ε.val
  rw [rvVolumePoolMap_value]
  obtain ⟨j | j,rfl⟩ := finSumFinEquiv.surjective k
  · change (ε⁻¹).val ≤ Values.vrv (productTuple (U.value u) (V.value (F u)) (productLeft n n j)) ∧
      Values.vrv (productTuple (U.value u) (V.value (F u)) (productLeft n n j)) ≤ ε.val
    rw [productTuple_left]
    have h := hγ (U.value u) ⟨u,rfl⟩ j
    exact ⟨hγlo.trans h.1,h.2.trans (show γ.val ≤ ε.val from le_max_left _ _)⟩
  · change (ε⁻¹).val ≤ Values.vrv (productTuple (U.value u) (V.value (F u)) (productRight n n j)) ∧
      Values.vrv (productTuple (U.value u) (V.value (F u)) (productRight n n j)) ≤ ε.val
    rw [productTuple_right]
    have h := hδ (V.value (F u)) ⟨F u,rfl⟩ j
    exact ⟨hδlo.trans h.1,h.2.trans (show δ.val ≤ ε.val from le_max_right _ _)⟩

def RVRouteFiniteData.vertexObject {a b : Fin n → Fin p} (C : RVRouteFiniteData (M := M) S n p m a b)
    {A : DefSet (rawRVSpace (M := M) m) S} (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S))
    (v : Fin n → Fin p) : RVObject (M := M) S n where
  arity := m
  domain := C.domain pool
  volume := (rvSelectedVolumeMap pool v).restrict (C.domain_subset pool)

theorem RVRouteFiniteData.vertexObject_finiteVolume {a b : Fin n → Fin p}
    (C : RVRouteFiniteData (M := M) S n p m a b) {A : DefSet (rawRVSpace (M := M) m) S}
    (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S)) (v : {v // v ∈ C.route.vertices}) :
    (C.vertexObject pool v.val).volume.FiniteFibres := C.volume_finite pool v

theorem RVRouteFiniteData.vertexObject_nonzero {a b : Fin n → Fin p}
    (C : RVRouteFiniteData (M := M) S n p m a b) {A : DefSet (rawRVSpace (M := M) m) S}
    (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S))
    (hPool : ∀ u k, ((pool u).val k).val ≠ iRVZero) (v : Fin n → Fin p)
    (u : C.domain pool) (k : Fin n) : ((C.vertexObject pool v).value u k).val ≠ iRVZero :=
  hPool ⟨u.val,C.domain_subset pool u.property⟩ (v k)

theorem RVRouteFiniteData.vertexObject_doublyBounded {a b : Fin n → Fin p}
    (C : RVRouteFiniteData (M := M) S n p m a b) {A : DefSet (rawRVSpace (M := M) m) S}
    (pool : Map A (DefSet.univ (rawRVSpace (M := M) p) S))
    (hA : RVValueDoublyBounded A.carrier)
    (hPool : RVValueDoublyBounded (Set.range (fun u : A => (pool u).val))) (v : Fin n → Fin p) :
    RVObjectDoublyBounded (C.vertexObject pool v) := by
  constructor
  · obtain ⟨γ,hγ⟩ := hA
    exact ⟨γ,fun u hu k => hγ u (C.domain_subset pool hu) k⟩
  · obtain ⟨γ,hγ⟩ := hPool
    refine ⟨γ,?_⟩
    rintro t ⟨u,rfl⟩ k
    let w : A := ⟨u.val,C.domain_subset pool u.property⟩
    exact hγ (pool w).val ⟨w,rfl⟩ (v k)

end DiamondIntegral.Section6
