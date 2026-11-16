import «section 6».UnaryAffineRVLiftInverse

/-! Full fixed-label total derivatives of the affine replacement at
every point, including VF-algebraic points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem unaryAffineRVLift_derivative {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.value u 0)
    (hb : ∀ v, rv M ((b v).val 0) = V.value v 0)
    (hnz : ∀ u, (a u).val 0 ≠ 0) (p : rvLift U) :
    HasMixedVFDerivativeAt (unaryAffineRVLift e a b ha hb hnz) p
      (vfDiagonalLinear (fun _ => (b (e.hom.map (liftLabelMap U p))).val 0 /
        (a (liftLabelMap U p)).val 0)) := by
  let u := liftLabelMap U p
  let c := (b (e.hom.map u)).val 0 / (a u).val 0
  have hlinear (x : Fin 1 → VF M) : vfDiagonalLinear (fun _ : Fin 1 => c) x = fun _ => c*x 0 := by
    funext i
    fin_cases i
    change (Matrix.diagonal (fun _ : Fin 1 => c)).mulVec x 0 = _
    rw [Matrix.mulVec_diagonal]
  have hp0 : p.val.1 0 ≠ 0 := by
    intro h
    have hrv := (congrFun (liftLabelMap_volume U p) 0).symm.trans (ha u).symm
    change rv M (p.val.1 0) = rv M ((a u).val 0) at hrv
    rw [h] at hrv
    have hzero : (a u).val 0 = 0 := (rv_eq_zero_iff _).mp (hrv.symm.trans rv_zero)
    exact hnz u hzero
  obtain ⟨δ,hδ⟩ := unary_rv_ball p.val.1 hp0
  refine ⟨fun x => vfDiagonalLinear (fun _ : Fin 1 => c) x + 0,⟨δ,fun x hx => ?_⟩,
    hasVFDerivativeAt_affine (vfDiagonalLinear (fun _ : Fin 1 => c)) 0 p.val.1⟩
  have hxU : (x,p.val.2) ∈ (rvLift U).carrier := by
    refine ⟨u,rfl,?_⟩
    funext i
    fin_cases i
    exact (congrFun (liftLabelMap_volume U p) 0).trans (hδ x hx).symm
  refine ⟨hxU,?_⟩
  rw [unaryAffineRVLift_value]
  have hu : liftLabelMap U ⟨(x,p.val.2),hxU⟩ = u := Subtype.ext rfl
  rw [hu]
  change (fun _ => c*x 0,(e.hom.map u).val) =
    (vfDiagonalLinear (fun _ : Fin 1 => c) x + 0,(unaryAffineRVLift e a b ha hb hnz p).val.2)
  rw [hlinear,add_zero]
  rfl

theorem unaryAffineRVLift_determinant {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : rvLift U) :
    (LinearMap.toMatrix' (vfDiagonalLinear (fun _ : Fin 1 =>
      (b (e.hom.map (liftLabelMap U p))).val 0 / (a (liftLabelMap U p)).val 0))).det =
      (b (e.hom.map (liftLabelMap U p))).val 0 / (a (liftLabelMap U p)).val 0 := by
  rw [det_vfDiagonalLinear]
  simp

end DiamondIntegral.Section6
