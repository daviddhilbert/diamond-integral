import «section 6».FiniteMeasuredRVLiftFieldBase
import «section 6».RVUnaryFactorizations

/-! A relatively unary RV map admits compatible target center families:
all unchanged volume coordinates use the identical source VF center.
The resulting diagonal lift fixes those VF coordinates exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def relativeTargetCenters {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S)) (i : Fin n) :
    Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S) :=
  vfTupleAssembleMap V.domain n (fun j => (vfTupleSelectMap S (fun _ : Fin 1 => j)).comp
    (if j = i then b else a.comp e.inv.map))

theorem relativeTargetCenters_value {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S)) (i : Fin n) (v : V.domain) (j : Fin n) :
    (relativeTargetCenters e a b i v).val j = if j = i then (b v).val j else (a (e.inv.map v)).val j := by
  change (vfTupleAssembleMap V.domain n _ v).val j = _
  rw [vfTupleAssembleMap_value]
  by_cases hj : j = i
  · simp only [if_pos hj]
    rfl
  · simp only [if_neg hj]
    rfl

theorem relativeTargetCenters_rv {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S)) (i : Fin n)
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hUnary : RVUnaryRelativeAt e.hom.map i) (v : V.domain) :
    SpecialTransformations.Section4.tupleRV (relativeTargetCenters e a b i v).val = V.value v := by
  funext j
  change rv M ((relativeTargetCenters e a b i v).val j) = V.value v j
  rw [relativeTargetCenters_value]
  by_cases hj : j = i
  · rw [if_pos hj]
    exact congrFun (hb v) j
  · rw [if_neg hj]
    have h := hUnary (e.inv.map v) j hj
    rw [rvIso_apply_inv] at h
    exact (congrFun (ha (e.inv.map v)) j).trans h.symm

theorem relative_diagonalRVLift_unary {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S)) (i : Fin n)
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hUnary : RVUnaryRelativeAt e.hom.map i) (hnz : ∀ u j, (a u).val j ≠ 0) :
    VFUnaryRelativeAt (diagonalRVLift e a (relativeTargetCenters e a b i) ha
      (relativeTargetCenters_rv e a b i ha hb hUnary) hnz) i := by
  intro p j hj
  rw [diagonalRVLift_value]
  dsimp only
  rw [relativeTargetCenters_value,if_neg hj,rvIso_inv_apply,div_self (hnz _ j),one_mul]

end DiamondIntegral.Section6
