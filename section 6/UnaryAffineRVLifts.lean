import «section 6».ScalarRationalMaps
import «section 6».UnaryCenterRepair
import Section9.AffineMixedDerivative

/-! Actual labelwise scalar affine lifts. Definable centers are supplied
as maps on the original label domains, so no individual label or center
is named in the base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem rv_ratio_mul_of_eq {a b x : VF M} (ha : a ≠ 0) (hx : rv M x = rv M a) :
    rv M (b / a * x) = rv M b := by
  change RVOperations.rvHom (b / a * x) = RVOperations.rvHom b
  change RVOperations.rvHom x = RVOperations.rvHom a at hx
  rw [map_mul,map_div₀,hx]
  have hn : RVOperations.rvHom a ≠ 0 := (RVOperations.rv_ne_zero a).mpr ha
  exact div_mul_cancel₀ _ hn

def unaryAffineVFMap {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    Map (rvLift U) (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let A := a.comp (liftLabelMap U)
  let B := b.comp (e.hom.map.comp (liftLabelMap U))
  let X := Map.fst (rawVFSpace (M := M) 1) (rawRVSpace U.arity) S (rvLift U)
  let T := (B.pair A).pair X
  exact (scalarRatioMulMap S).comp ((Map.inclusion (fun _ _ => Set.mem_univ _)).comp T)

theorem unaryAffineVFMap_value {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : rvLift U) :
    (unaryAffineVFMap e a b p).val 0 =
      (b (e.hom.map (liftLabelMap U p))).val 0 / (a (liftLabelMap U p)).val 0 * p.val.1 0 := rfl

def unaryAffineRVLift {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.value u 0)
    (hb : ∀ v, rv M ((b v).val 0) = V.value v 0)
    (hnz : ∀ u, (a u).val 0 ≠ 0) : Map (rvLift U) (rvLift V) := by
  let f := (unaryAffineVFMap e a b).pair (e.hom.map.comp (liftLabelMap U))
  refine f.corestrict (fun p => ?_)
  refine ⟨e.hom.map (liftLabelMap U p),rfl,?_⟩
  funext i
  fin_cases i
  change V.value (e.hom.map (liftLabelMap U p)) 0 = rv M ((unaryAffineVFMap e a b p).val 0)
  rw [unaryAffineVFMap_value]
  exact (hb _).symm.trans (rv_ratio_mul_of_eq (hnz _) ((congrFun (liftLabelMap_volume U p) 0).symm.trans (ha _).symm)).symm

theorem unaryAffineRVLift_value {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.value u 0)
    (hb : ∀ v, rv M ((b v).val 0) = V.value v 0)
    (hnz : ∀ u, (a u).val 0 ≠ 0) (p : rvLift U) :
    (unaryAffineRVLift e a b ha hb hnz p).val =
      (fun _ => (b (e.hom.map (liftLabelMap U p))).val 0 / (a (liftLabelMap U p)).val 0 * p.val.1 0,
        (e.hom.map (liftLabelMap U p)).val) := by
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

end DiamondIntegral.Section6
