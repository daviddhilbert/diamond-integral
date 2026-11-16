import «section 6».RVIsomorphismVolumeClosure

/-! Original-base definable loci on which specified finite algebraic
relations certify the finite fibres of an actual RV volume map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def rvCodeDefSet (C : Set (Fin n → M)) (hC : S.Definable LRV C) :
    DefSet (rawRVSpace (M := M) n) S where
  carrier := {t | rvValues t ∈ C}
  definable := by
    have h := ((rawRVSpace (M := M) n).definable_domain S).inter hC
    change S.Definable LRV ((rawRVSpace (M := M) n).preimage {t | rvValues t ∈ C})
    convert h using 1 <;> try rfl
    apply Set.ext
    intro (z : Fin n → M)
    constructor
    · rintro ⟨hz,hzC⟩
      change rvValues ((rawRVSpace (M := M) n).decode ⟨z,hz⟩) ∈ C at hzC
      have he : rvValues ((rawRVSpace (M := M) n).decode ⟨z,hz⟩) = z := rvValues_decode _
      exact ⟨hz,he ▸ hzC⟩
    · rintro ⟨hz,hzC⟩
      refine ⟨hz,?_⟩
      change rvValues ((rawRVSpace (M := M) n).decode ⟨z,hz⟩) ∈ C
      rwa [rvValues_decode]

def rvFiniteVolumeRelationLocus (R : Fin m → RawClosure.Tuple.GoodRelation (n := n) S) :
    DefSet (rawRVSpace (M := M) (n+m)) S := by
  let C : Set (Fin (n+m) → M) :=
    {z | ∀ j, (z ∘ productLeft n m,z (productRight n m j)) ∈ (R j).val}
  have hC : S.Definable LRV C := by
    have h (j : Fin m) := (R j).property.1.preimage_comp
      (Sum.elim (productLeft n m) (fun _ : Fin 1 => productRight n m j))
    convert Set.definable_iInter_of_finite h using 1
    ext z
    simp only [C,Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage]
    rfl
  exact rvCodeDefSet C hC

def rvVolumeInputMap {A : DefSet (rawRVSpace (M := M) m) S}
    (θ : Map A (DefSet.univ (rawRVSpace (M := M) n) S)) :
    Map A (DefSet.univ (rawRVSpace (M := M) (n+m)) S) :=
  (rvAppendMap S n m).comp ((θ.pair (Map.id A).toUniv).toUniv)

theorem rvVolumeInputMap_value {A : DefSet (rawRVSpace (M := M) m) S}
    (θ : Map A (DefSet.univ (rawRVSpace (M := M) n) S)) (u : A) :
    (rvVolumeInputMap θ u).val = productTuple (θ u).val u.val := by
  apply productTuple_ext
  · intro i
    rw [productTuple_left]
    exact Fin.append_left _ _ i
  · intro j
    rw [productTuple_right]
    exact Fin.append_right _ _ j

def rvFiniteVolumeLocus {A : DefSet (rawRVSpace (M := M) m) S}
    (θ : Map A (DefSet.univ (rawRVSpace (M := M) n) S))
    (R : Fin m → RawClosure.Tuple.GoodRelation (n := n) S) : DefSet (rawRVSpace (M := M) m) S where
  carrier := {t | ∃ u : A, u.val = t ∧ (rvVolumeInputMap θ u).val ∈ (rvFiniteVolumeRelationLocus R).carrier}
  definable := (rvVolumeInputMap θ).definable_preimage (rvFiniteVolumeRelationLocus R).definable

theorem rvFiniteVolumeLocus_subset {A : DefSet (rawRVSpace (M := M) m) S}
    (θ : Map A (DefSet.univ (rawRVSpace (M := M) n) S))
    (R : Fin m → RawClosure.Tuple.GoodRelation (n := n) S) :
    (rvFiniteVolumeLocus θ R).carrier ⊆ A.carrier := by
  rintro t ⟨u,rfl,_⟩
  exact u.property

theorem rvFiniteVolumeLocus_mem {A : DefSet (rawRVSpace (M := M) m) S}
    (θ : Map A (DefSet.univ (rawRVSpace (M := M) n) S))
    (R : Fin m → RawClosure.Tuple.GoodRelation (n := n) S) (u : A) :
    u.val ∈ (rvFiniteVolumeLocus θ R).carrier ↔
      ∀ j, (rvValues (θ u).val,(u.val j).val) ∈ (R j).val := by
  have he (u : A) : (rvVolumeInputMap θ u).val ∈ (rvFiniteVolumeRelationLocus R).carrier ↔
      ∀ j, (rvValues (θ u).val,(u.val j).val) ∈ (R j).val := by
    change (∀ j, (rvValues (rvVolumeInputMap θ u).val ∘ productLeft n m,
      rvValues (rvVolumeInputMap θ u).val (productRight n m j)) ∈ (R j).val) ↔ _
    rw [rvVolumeInputMap_value]
    have hLeft : rvValues (productTuple (θ u).val u.val) ∘ productLeft n m = rvValues (θ u).val := by
      funext i
      exact congrArg Subtype.val (productTuple_left _ _ i)
    rw [hLeft]
    exact forall_congr' (fun j => by rw [show rvValues (productTuple (θ u).val u.val) (productRight n m j) =
      (u.val j).val from congrArg Subtype.val (productTuple_right _ _ j)])
  constructor
  · rintro ⟨v,hv,hR⟩
    have hUV : v = u := Subtype.ext hv
    subst v
    exact (he u).mp hR
  · intro h
    exact ⟨u,rfl,(he u).mpr h⟩

theorem rvFiniteVolumeLocus_finite {A : DefSet (rawRVSpace (M := M) m) S}
    (θ : Map A (DefSet.univ (rawRVSpace (M := M) n) S))
    (R : Fin m → RawClosure.Tuple.GoodRelation (n := n) S) :
    (θ.restrict (rvFiniteVolumeLocus_subset θ R)).FiniteFibres := by
  intro t
  let D := rvFiniteVolumeLocus θ R
  let H : Set (Fin m → M) := {z | ∀ j, (rvValues t.val,z j) ∈ (R j).val}
  have hH : H.Finite := Set.Finite.pi' (fun j => (R j).property.2 (rvValues t.val))
  have hinj : Function.Injective (fun u : D => rvValues u.val) :=
    fun _ _ h => Subtype.ext (rvValues_injective h)
  apply (hH.preimage hinj.injOn).subset
  intro u hu
  let v : A := ⟨u.val,rvFiniteVolumeLocus_subset θ R u.property⟩
  have h := (rvFiniteVolumeLocus_mem θ R v).mp u.property
  have hv : θ v = t := hu
  rw [hv] at h
  exact h

end DiamondIntegral.Section6
