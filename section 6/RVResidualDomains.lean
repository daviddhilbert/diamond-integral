import «section 6».FiniteDefSetUnions

/-! The original-base residual label domain after all good coordinate
pivots. On it every target volume coordinate lies in its finite inverse
obstacle family over the old source prefix. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvResidualDomain {U V : RVObject (M := M) S (n+1)} (F : RVHom U V)
    (E : Fin (n+1) → RawClosure.Tuple.GoodRelation (n := n) S) :
    DefSet (rawRVSpace (M := M) U.arity) S :=
  U.domain.sdiff (finiteDefSetUnion (fun j => rvGoodReplacementDomain F j (E j)))

theorem rvResidualDomain_subset {U V : RVObject (M := M) S (n+1)} (F : RVHom U V)
    (E : Fin (n+1) → RawClosure.Tuple.GoodRelation (n := n) S) :
    (rvResidualDomain F E).carrier ⊆ U.domain.carrier := Set.sdiff_subset

theorem rvResidualDomain_mem {U V : RVObject (M := M) S (n+1)} (F : RVHom U V)
    (E : Fin (n+1) → RawClosure.Tuple.GoodRelation (n := n) S) (u : U.domain) :
    u.val ∈ (rvResidualDomain F E).carrier ↔
      ∀ j, (Fin.init (rvValues (U.value u)),(V.value (F.map u) j).val) ∈ (E j).val := by
  constructor
  · rintro ⟨_,hNot⟩ j
    by_contra hj
    exact hNot (Set.mem_iUnion.mpr ⟨j,(rvGoodReplacementDomain_mem F j (E j) u).mpr hj⟩)
  · intro h
    refine ⟨u.property,?_⟩
    change u.val ∉ ⋃ j : Fin (n+1), (rvGoodReplacementDomain F j (E j)).carrier
    intro hu
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hu
    exact ((rvGoodReplacementDomain_mem F j (E j) u).mp hj) (h j)

def rvResidualPrefixMap {U V : RVObject (M := M) S (n+1)} (F : RVHom U V)
    (E : Fin (n+1) → RawClosure.Tuple.GoodRelation (n := n) S) :
    Map (rvResidualDomain F E) (DefSet.univ (rawRVSpace (M := M) n) S) :=
  (rvTupleSelectMap S Fin.castSucc).comp (U.volume.restrict (rvResidualDomain_subset F E))

theorem rvResidualPrefixMap_value {U V : RVObject (M := M) S (n+1)} (F : RVHom U V)
    (E : Fin (n+1) → RawClosure.Tuple.GoodRelation (n := n) S) (u : rvResidualDomain F E) :
    (rvResidualPrefixMap F E u).val = Fin.init (U.value ⟨u.val,rvResidualDomain_subset F E u.property⟩) := rfl

end DiamondIntegral.Section6
