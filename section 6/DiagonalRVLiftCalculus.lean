import «section 6».DiagonalRVLifts

/-! Inverse and everywhere total derivative of actual diagonal lifts.
All coefficients are fixed on an original RV label fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem diagonalRVLift_leftInverse {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hnza : ∀ u i, (a u).val i ≠ 0) (hnzb : ∀ v i, (b v).val i ≠ 0) :
    Function.LeftInverse (diagonalRVLift e.symm b a hb ha hnzb) (diagonalRVLift e a b ha hb hnza) := by
  intro p
  apply Subtype.ext
  rw [diagonalRVLift_value,diagonalRVLift_label]
  change (fun i => (a (e.inv.map (e.hom.map (liftLabelMap U p)))).val i /
      (b (e.hom.map (liftLabelMap U p))).val i * (diagonalRVLift e a b ha hb hnza p).val.1 i,
      (e.inv.map (e.hom.map (liftLabelMap U p))).val) = p.val
  rw [rvIso_inv_apply,diagonalRVLift_value]
  apply Prod.ext
  · funext i
    dsimp only
    field_simp [hnza _ i,hnzb _ i]
  · rfl

theorem diagonalRVLift_bijective {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hnza : ∀ u i, (a u).val i ≠ 0) (hnzb : ∀ v i, (b v).val i ≠ 0) :
    Function.Bijective (diagonalRVLift e a b ha hb hnza) :=
  ⟨(diagonalRVLift_leftInverse e a b ha hb hnza hnzb).injective,
    (diagonalRVLift_leftInverse e.symm b a hb ha hnzb hnza).surjective⟩

theorem nonzero_tuple_rv_ball (a : Fin n → VF M) (ha : ∀ i, a i ≠ 0) :
    ∃ δ : Gamma M, ∀ x ∈ vfBall a δ,
      SpecialTransformations.Section4.tupleRV x = SpecialTransformations.Section4.tupleRV a := by
  obtain ⟨δ,hδ⟩ := (Set.finite_range (fun i => finiteValue (a i) (ha i))).bddAbove
  refine ⟨δ,fun x hx => funext (fun i => ?_)⟩
  have hle : (finiteValue (a i) (ha i)).val ≤ δ.val := hδ (Set.mem_range_self i)
  exact rv_eq_of_close_at_radius (finiteValue (a i) (ha i)) le_rfl (hle.trans_lt (hx i))

theorem diagonalRVLift_derivative {U V : RVObject (M := M) S n} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.value v)
    (hnz : ∀ u i, (a u).val i ≠ 0) (p : rvLift U) :
    HasMixedVFDerivativeAt (diagonalRVLift e a b ha hb hnz) p
      (vfDiagonalLinear (fun i => (b (e.hom.map (liftLabelMap U p))).val i /
        (a (liftLabelMap U p)).val i)) := by
  let u := liftLabelMap U p
  let c (i : Fin n) := (b (e.hom.map u)).val i / (a u).val i
  have hlinear (x : Fin n → VF M) : vfDiagonalLinear c x = fun i => c i*x i := by
    funext i
    change (Matrix.diagonal c).mulVec x i = _
    rw [Matrix.mulVec_diagonal]
  have hp0 (i : Fin n) : p.val.1 i ≠ 0 := by
    intro h
    have hrv := (congrFun (liftLabelMap_volume U p) i).symm.trans (congrFun (ha u) i).symm
    change rv M (p.val.1 i) = rv M ((a u).val i) at hrv
    rw [h] at hrv
    exact hnz u i ((rv_eq_zero_iff _).mp (hrv.symm.trans rv_zero))
  obtain ⟨δ,hδ⟩ := nonzero_tuple_rv_ball p.val.1 hp0
  refine ⟨fun x => vfDiagonalLinear c x+0,⟨δ,fun x hx => ?_⟩,
    hasVFDerivativeAt_affine (vfDiagonalLinear c) 0 p.val.1⟩
  have hxU : (x,p.val.2) ∈ (rvLift U).carrier :=
    ⟨u,rfl,(liftLabelMap_volume U p).trans (hδ x hx).symm⟩
  refine ⟨hxU,?_⟩
  rw [diagonalRVLift_value]
  have hu : liftLabelMap U ⟨(x,p.val.2),hxU⟩ = u := Subtype.ext rfl
  rw [hu]
  change (fun i => c i*x i,(e.hom.map u).val) =
    (vfDiagonalLinear c x+0,(diagonalRVLift e a b ha hb hnz p).val.2)
  rw [hlinear,add_zero]
  rfl

end DiamondIntegral.Section6
