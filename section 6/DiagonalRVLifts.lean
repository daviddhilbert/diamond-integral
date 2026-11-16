import «section 6».FiniteRVObjectCenters

/-! Actual diagonal affine lifts in every degree, using original-label
VF center maps and retaining all old source and target labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def diagonalRVLiftVFMap {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S)) :
    Map (rvLift U) (DefSet.univ (rawVFSpace (M := M) n) S) := by
  let A := a.comp (liftLabelMap U)
  let B := b.comp (e.hom.map.comp (liftLabelMap U))
  let X := Map.fst (rawVFSpace (M := M) n) (rawRVSpace U.arity) S (rvLift U)
  let F (i : Fin n) := by
    let c := vfTupleSelectMap S (fun _ : Fin 1 => i)
    let T := ((c.comp B).pair (c.comp A)).pair (c.comp X)
    exact (scalarRatioMulMap S).comp ((Map.inclusion (fun _ _ => Set.mem_univ _)).comp T)
  exact vfTupleAssembleMap (rvLift U) n F

theorem diagonalRVLiftVFMap_value {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S)) (p : rvLift U) :
    (diagonalRVLiftVFMap e a b p).val = fun i =>
      (b (e.hom.map (liftLabelMap U p))).val i / (a (liftLabelMap U p)).val i * p.val.1 i := by
  unfold diagonalRVLiftVFMap
  rw [vfTupleAssembleMap_value]
  rfl

def diagonalRVLift {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hnz : ∀ u i, (a u).val i ≠ 0) : Map (rvLift U) (rvLift V) := by
  let f := (diagonalRVLiftVFMap e a b).pair (e.hom.map.comp (liftLabelMap U))
  refine f.corestrict (fun p => ?_)
  refine ⟨e.hom.map (liftLabelMap U p),rfl,?_⟩
  funext i
  change V.value (e.hom.map (liftLabelMap U p)) i = rv M ((diagonalRVLiftVFMap e a b p).val i)
  rw [diagonalRVLiftVFMap_value]
  exact (congrFun (hb _) i).symm.trans (rv_ratio_mul_of_eq (hnz _ i)
    ((congrFun (liftLabelMap_volume U p) i).symm.trans (congrFun (ha _) i).symm)).symm

theorem diagonalRVLift_value {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hnz : ∀ u i, (a u).val i ≠ 0) (p : rvLift U) :
    (diagonalRVLift e a b ha hb hnz p).val =
      (fun i => (b (e.hom.map (liftLabelMap U p))).val i / (a (liftLabelMap U p)).val i * p.val.1 i,
        (e.hom.map (liftLabelMap U p)).val) :=
  Prod.ext (diagonalRVLiftVFMap_value e a b p) rfl

theorem diagonalRVLift_label {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hnz : ∀ u i, (a u).val i ≠ 0) (p : rvLift U) :
    liftLabelMap V (diagonalRVLift e a b ha hb hnz p) = e.hom.map (liftLabelMap U p) := by
  apply Subtype.ext
  rfl

end DiamondIntegral.Section6
