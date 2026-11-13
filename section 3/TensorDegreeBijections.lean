import «section 3».TensorObjectNormalForm
import «section 3».GammaGroundRVGradedComparison
import «section 3».GammaGroundRVIsomorphismClasses
import «section 3».GammaGroundRVCoproducts
import Mathlib.Algebra.DirectSum.Module
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def gammaGroundUnmeasuredTensorDegreeImage (k : ℕ) :
    GammaGroundUnmeasuredPositiveTensor hc B →+ GammaGroundRVKPlus hc B k :=
  (DirectSum.component ℕ ℕ (GammaGroundRVKPlus hc B) k).toAddMonoidHom.comp
    (gammaGroundRVPresentationToDirectSum.toAddMonoidHom.comp gammaGroundUnmeasuredTensorMap.toAddMonoidHom)

/-- Retain an object's actual grade, returning the empty object in every
other grade. Equality transport does not change its positive class. -/
def gammaGroundRVObjectAtDegree {j : ℕ} (U : GammaGroundRVObject hc B j) (k : ℕ) :
    GammaGroundRVObject hc B k := if h : j = k then h ▸ U else GammaGroundRVObject.empty hc B k

theorem gammaGroundRVObjectAtDegree_class {j : ℕ} (U : GammaGroundRVObject hc B j) (k : ℕ) :
    gammaGroundRVClass (gammaGroundRVObjectAtDegree U k) =
      DirectSum.component ℕ ℕ (GammaGroundRVKPlus hc B) k
        (gammaGroundRVPresentationToDirectSum (gammaGroundRVSemiringClass U)) := by
  rw [gammaGroundRVPresentationToDirectSum_class]
  by_cases h : j = k
  · subst k
    rw [gammaGroundRVObjectAtDegree,dite_eq_left rfl]
    change gammaGroundRVClass U = DirectSum.component ℕ ℕ (GammaGroundRVKPlus hc B) j
      (DirectSum.lof ℕ ℕ (GammaGroundRVKPlus hc B) j (gammaGroundRVClass U))
    exact (DirectSum.component.lof_self ℕ j (gammaGroundRVClass U)).symm
  · rw [gammaGroundRVObjectAtDegree,dite_eq_right h,gammaGroundRVClass_empty]
    change 0 = DirectSum.component ℕ ℕ (GammaGroundRVKPlus hc B) k
      (DirectSum.lof ℕ ℕ (GammaGroundRVKPlus hc B) j (gammaGroundRVClass U))
    rw [DirectSum.component.of,dite_eq_right h]

def GammaGroundUnmeasuredTensorTerm.rvObjectAt (t : GammaGroundUnmeasuredTensorTerm hc B) (k : ℕ) :
    GammaGroundRVObject hc B k := gammaGroundRVObjectAtDegree t.rvObject k

theorem GammaGroundUnmeasuredTensorTerm.rvObjectAt_class (t : GammaGroundUnmeasuredTensorTerm hc B) (k : ℕ) :
    gammaGroundRVClass (t.rvObjectAt k) = gammaGroundUnmeasuredTensorDegreeImage k t.value := by
  change gammaGroundRVClass (gammaGroundRVObjectAtDegree t.rvObject k) =
    DirectSum.component ℕ ℕ (GammaGroundRVKPlus hc B) k
      (gammaGroundRVPresentationToDirectSum (gammaGroundUnmeasuredTensorMap t.value))
  rw [t.value_image]
  exact gammaGroundRVObjectAtDegree_class t.rvObject k

def gammaGroundTensorListRVObject (k : ℕ) (l : List (GammaGroundUnmeasuredTensorTerm hc B)) :
    GammaGroundRVObject hc B k :=
  (l.map (fun t => t.rvObjectAt k)).foldr GammaGroundRVObject.coprod (GammaGroundRVObject.empty hc B k)

theorem gammaGroundTensorListRVObject_class (k : ℕ) (l : List (GammaGroundUnmeasuredTensorTerm hc B)) :
    gammaGroundRVClass (gammaGroundTensorListRVObject k l) =
      gammaGroundUnmeasuredTensorDegreeImage k ((l.map GammaGroundUnmeasuredTensorTerm.value).sum) := by
  induction l with
  | nil => exact gammaGroundRVClass_empty.trans (map_zero _).symm
  | cons t l ih =>
    change gammaGroundRVClass ((t.rvObjectAt k).coprod (gammaGroundTensorListRVObject k l)) =
      gammaGroundUnmeasuredTensorDegreeImage k (t.value+(l.map GammaGroundUnmeasuredTensorTerm.value).sum)
    rw [gammaGroundRVClass_coprod,t.rvObjectAt_class,ih,map_add]

/-- Equal positive tensor images give actual original-ground RV
bijections between the product unions in each total degree. No matched
summands have been cancelled to obtain these bijections. -/
theorem gammaGroundTensorListRVObject_iso_of_equal_images
    (l q : List (GammaGroundUnmeasuredTensorTerm hc B))
    (h : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundUnmeasuredTensorTerm.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundUnmeasuredTensorTerm.value).sum)) (k : ℕ) :
    Nonempty (gammaGroundTensorListRVObject k l ≅ gammaGroundTensorListRVObject k q) := by
  apply gammaGroundRVClass_eq_iff_iso.mp
  rw [gammaGroundTensorListRVObject_class,gammaGroundTensorListRVObject_class]
  exact congrArg (fun a => DirectSum.component ℕ ℕ (GammaGroundRVKPlus hc B) k
    (gammaGroundRVPresentationToDirectSum a)) h
end DiamondIntegral.Section3
