import «section 6».VFCoordinateArithmeticBijections
import «section 6».VFCoordinateArithmeticJacobians
import «section 6».MeasuredLiftDensityValues

/-! Actual everywhere measured relatively unary VF lifts of the
elementary RV coordinate operations. Full total derivatives are checked
at every point, with the exact prescribed Gamma density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

set_option backward.isDefEq.respectTransparency true in
theorem coordinateArithmetic_product_ratio {K : Type*} [CommGroupWithZero K]
    (op : RVCoordinateOperation) (i j : Fin n) (x : Fin n → K) (hx : ∀ k,x k ≠ 0) :
    (∏ k,coordinateArithmetic op i j x k) / (∏ k,x k) = op.fieldValue (x i) (x j) / x i := by
  classical
  have hP := (Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)).symm
  have hne : (∏ k ∈ Finset.univ.erase i,x k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => hx k)
  rw [coordinateArithmetic,Finset.prod_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase,hP]
  exact mul_div_mul_right _ _ hne

theorem coordinateArithmetic_slope_value (op : RVCoordinateOperation) (x y : VF M)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    vfValue (op.vfSlope x y)=vfValue (op.fieldValue x y / x) := by
  cases op
  · change vfValue y=vfValue (x*y/x)
    rw [mul_div_cancel_left₀ y hx]
  · change vfValue y⁻¹=vfValue (x/y/x)
    congr 1
    simp [div_eq_mul_inv,hx,mul_assoc,mul_comm,mul_left_comm]
  · change vfValue (-(y*x⁻¹ ^ 2))=vfValue (y/x/x)
    rw [show vfValue (-(y*x⁻¹ ^ 2))=vfValue (y*x⁻¹ ^ 2) from vfValue_neg _]
    congr 1
    simp [div_eq_mul_inv,pow_two,mul_assoc]

def coordinateArithmeticMeasuredRVLift (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :
    EverywhereMeasuredRVLift (measuredCoordinateArithmeticIso hc U op i j hij) where
  map := coordinateArithmeticRVLift hc U op i j hij
  bijective := coordinateArithmeticRVLift_bijective hc U op i j hij
  labels p := ⟨liftLabelMap U.object p,rfl,rfl⟩
  measure p := by
    obtain ⟨L,hL,hDet⟩ := coordinateArithmeticRVLift_derivative_and_det hc U op i j hij p
    refine ⟨L,hL,?_⟩
    rw [hDet,measuredLift_density_value (measuredCoordinateArithmeticIso hc U op i j hij)
      (coordinateArithmeticRVLift hc U op i j hij) (fun q => ⟨liftLabelMap U.object q,rfl,rfl⟩) p]
    change vfValue (op.vfSlope (p.val.1 i) (p.val.1 j))=
      vfValue ((∏ k,coordinateArithmetic op i j p.val.1 k) / ∏ k,p.val.1 k)
    rw [coordinateArithmetic_product_ratio op i j p.val.1 (rvLift_vf_coordinate_ne_zero U p)]
    exact coordinateArithmetic_slope_value op _ _ (rvLift_vf_coordinate_ne_zero U p i)
      (rvLift_vf_coordinate_ne_zero U p j)

theorem coordinateArithmeticMeasuredRVLift_unary (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :
    VFUnaryRelativeAt (coordinateArithmeticMeasuredRVLift hc U op i j hij).map i :=
  coordinateArithmeticRVLift_unary hc U op i j hij

end DiamondIntegral.Section6
