import «section 6».RVGoodReplacementFiniteness

/-! An actual relatively unary RV isomorphism on every good coordinate
pivot domain. The new volume is constructed and its finite fibres and
nonzero coordinates are proved from the original hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvGoodReplacementObject {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S) : RVObject (M := M) S (n+1) where
  arity := U.arity
  domain := rvGoodReplacementDomain F j E
  volume := (rvLastReplacementMap F j).restrict (rvGoodReplacementDomain_subset F j E)

theorem rvGoodReplacementObject_nonzero {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero) (hV : ∀ v i, (V.value v i).val ≠ iRVZero)
    (u : (rvGoodReplacementObject F j E).domain) (i : Fin (n+1)) :
    ((rvGoodReplacementObject F j E).value u i).val ≠ iRVZero := by
  let a : U.domain := ⟨u.val,rvGoodReplacementDomain_subset F j E u.property⟩
  change ((rvLastReplacementMap F j a).val i).val ≠ iRVZero
  rw [rvLastReplacementMap_value]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simpa only [Fin.snoc_last] using hV (F.map a) j
  · simpa only [Fin.snoc_castSucc,Fin.init] using hU a k.castSucc

def rvGoodPivotIso {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S) (hUF : U.volume.FiniteFibres)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero) (hV : ∀ v i, (V.value v i).val ≠ iRVZero)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite) :
    U.restrict (rvGoodReplacementDomain F j E) (rvGoodReplacementDomain_subset F j E) ≅
      rvGoodReplacementObject F j E :=
  rvIsoOfFiniteVolumeNonzero (Map.id (rvGoodReplacementDomain F j E)) Function.bijective_id
    (hUF.restrict (rvGoodReplacementDomain_subset F j E)) (rvGoodReplacementMap_finite F j E hUF hObs)
    (fun u => hU ⟨u.val,rvGoodReplacementDomain_subset F j E u.property⟩)
    (rvGoodReplacementObject_nonzero F j E hU hV)

theorem rvGoodPivotIso_unary {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S) (hUF : U.volume.FiniteFibres)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero) (hV : ∀ v i, (V.value v i).val ≠ iRVZero)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite) :
    RVUnaryRelativeAt (rvGoodPivotIso F j E hUF hU hV hObs).hom.map (Fin.last n) := by
  intro u i hi
  let a : U.domain := ⟨u.val,rvGoodReplacementDomain_subset F j E u.property⟩
  change (rvLastReplacementMap F j a).val i = U.value a i
  rw [rvLastReplacementMap_value]
  revert hi
  refine Fin.lastCases ?_ (fun k hk => ?_) i
  · intro h
    exact (h rfl).elim
  · simp only [Fin.snoc_castSucc,Fin.init]

end DiamondIntegral.Section6
