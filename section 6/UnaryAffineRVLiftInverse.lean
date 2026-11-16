import «section 6».UnaryAffineRVLifts

/-! Labelwise affine lifts are actual bijections, with their inverse
obtained by exchanging the two definable center families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem unaryAffineRVLift_label {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.value u 0)
    (hb : ∀ v, rv M ((b v).val 0) = V.value v 0)
    (hnz : ∀ u, (a u).val 0 ≠ 0) (p : rvLift U) :
    liftLabelMap V (unaryAffineRVLift e a b ha hb hnz p) = e.hom.map (liftLabelMap U p) := by
  apply Subtype.ext
  rfl

theorem unaryAffineRVLift_leftInverse {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.value u 0)
    (hb : ∀ v, rv M ((b v).val 0) = V.value v 0)
    (hnza : ∀ u, (a u).val 0 ≠ 0) (hnzb : ∀ v, (b v).val 0 ≠ 0) :
    Function.LeftInverse (unaryAffineRVLift e.symm b a hb ha hnzb)
      (unaryAffineRVLift e a b ha hb hnza) := by
  intro p
  apply Subtype.ext
  rw [unaryAffineRVLift_value,unaryAffineRVLift_label]
  change (fun _ => (a (e.inv.map (e.hom.map (liftLabelMap U p)))).val 0 /
      (b (e.hom.map (liftLabelMap U p))).val 0 * (unaryAffineRVLift e a b ha hb hnza p).val.1 0,
      (e.inv.map (e.hom.map (liftLabelMap U p))).val) = p.val
  rw [SpecialTransformations.Section7.rvIso_inv_apply,unaryAffineRVLift_value]
  apply Prod.ext
  · funext i
    fin_cases i
    dsimp only
    field_simp [hnza _,hnzb _]
    exact congrArg p.val.1 (Subsingleton.elim _ _)
  · rfl

theorem unaryAffineRVLift_bijective {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.value u 0)
    (hb : ∀ v, rv M ((b v).val 0) = V.value v 0)
    (hnza : ∀ u, (a u).val 0 ≠ 0) (hnzb : ∀ v, (b v).val 0 ≠ 0) :
    Function.Bijective (unaryAffineRVLift e a b ha hb hnza) := by
  exact ⟨(unaryAffineRVLift_leftInverse e a b ha hb hnza hnzb).injective,
    (unaryAffineRVLift_leftInverse e.symm b a hb ha hnzb hnza).surjective⟩

end DiamondIntegral.Section6
