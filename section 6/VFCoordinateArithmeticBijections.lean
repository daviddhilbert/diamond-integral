import «section 6».VFCoordinateArithmeticMaps

/-! The actual VF arithmetic maps biject whole old-label polydiscs,
including both division operations. The inverse is explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem tupleRV_coordinateArithmetic_field (op : RVCoordinateOperation) (i j : Fin n) (x : Fin n → VF M) :
    tupleRV (coordinateArithmetic op i j x)=coordinateArithmetic op i j (tupleRV x) := by
  rw [tupleRV_coordinateArithmetic]
  cases op <;> rfl

theorem coordinateArithmeticRVLift_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :
    Function.Bijective (coordinateArithmeticRVLift hc U op i j hij) := by
  let A := measuredCoordinateArithmeticObject hc U op i j hij
  constructor
  · intro p q h
    have hx := congrArg (fun z : rvLift A.object => z.val.1) h
    have ht := congrArg (fun z : rvLift A.object => z.val.2) h
    change coordinateArithmetic op i j p.val.1=coordinateArithmetic op i j q.val.1 at hx
    have he := congrArg (coordinateArithmetic op.inverse i j) hx
    rw [coordinateArithmetic_inverse op i j hij _ (rvLift_vf_coordinate_ne_zero U p i)
      (rvLift_vf_coordinate_ne_zero U p j),
      coordinateArithmetic_inverse op i j hij _ (rvLift_vf_coordinate_ne_zero U q i)
        (rvLift_vf_coordinate_ne_zero U q j)] at he
    exact Subtype.ext (Prod.ext he ht)
  · intro q
    let u : U.object.domain := liftLabelMap A.object q
    let x := coordinateArithmetic op.inverse i j q.val.1
    have hRV : tupleRV q.val.1=coordinateArithmetic op i j (U.object.value u) := by
      rw [← liftLabelMap_volume A.object q]
      change (measuredCoordinateArithmeticObject hc U op i j hij).object.value u=_
      rw [measuredCoordinateArithmeticObject_value]
      cases op <;> rfl
    have hx : tupleRV x=U.object.value u := by
      rw [tupleRV_coordinateArithmetic_field,hRV]
      exact coordinateArithmetic_inverse op i j hij _ ((rv_nonzero_code_iff _).mp (U.nonzero u i))
        ((rv_nonzero_code_iff _).mp (U.nonzero u j))
    let p : rvLift U.object := ⟨(x,u.val),u,rfl,hx.symm⟩
    refine ⟨p,Subtype.ext (Prod.ext ?_ rfl)⟩
    change coordinateArithmetic op i j (coordinateArithmetic op.inverse i j q.val.1)=q.val.1
    have h := coordinateArithmetic_inverse op.inverse i j hij q.val.1
      (rvLift_vf_coordinate_ne_zero A q i) (rvLift_vf_coordinate_ne_zero A q j)
    rwa [op.inverse_inverse] at h

end DiamondIntegral.Section6
