import «section 3».TensorDegreeBijections
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3

/-- Regroup a finite positive sum by any finite family of degrees
containing its support. Only commutative addition is required. -/
theorem positive_list_sum_by_degree {ι A : Type} [AddCommMonoid A]
    (degree : ι → ℕ) (value : ι → A) (l : List ι) (F : Finset ℕ)
    (hF : ∀ t ∈ l, degree t ∈ F) :
    ∑ k ∈ F, ((l.filter (fun t => decide (degree t = k))).map value).sum = (l.map value).sum := by
  induction l with
  | nil => simp only [List.filter_nil,List.map_nil,List.sum_nil,Finset.sum_const_zero]
  | cons t l ih =>
    have hhead (k : ℕ) :
        (((t::l).filter (fun t => decide (degree t = k))).map value).sum =
        (if degree t = k then value t else 0) + ((l.filter (fun t => decide (degree t = k))).map value).sum := by
      by_cases h : degree t = k <;> simp [h]
    simp_rw [hhead]
    rw [Finset.sum_add_distrib,ih (fun a ha => hF a (List.mem_cons_of_mem t ha))]
    have hsum : ∑ k ∈ F, (if degree t = k then value t else 0) = value t := by
      rw [Finset.sum_eq_single (degree t)]
      · exact ite_eq_left rfl
      · intro k _ hk
        exact ite_eq_right (Ne.symm hk)
      · intro ht
        exact False.elim (ht (hF t (List.mem_cons_self ..)))
    rw [hsum]
    rfl

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

def gammaGroundTensorTermsInDegree (k : ℕ) (l : List (GammaGroundUnmeasuredTensorTerm hc B)) :=
  l.filter (fun t => decide (t.residueDegree+t.gammaDegree = k))

theorem gammaGroundRVSemiringClass_coprod {k : ℕ} (U V : GammaGroundRVObject hc B k) :
    gammaGroundRVSemiringClass (U.coprod V) = gammaGroundRVSemiringClass U + gammaGroundRVSemiringClass V := by
  have h := congrArg (gammaGroundRVKPlusToSemiring (hc := hc) (ground := B)) (gammaGroundRVClass_coprod U V)
  simpa only [map_add,gammaGroundRVKPlusToSemiring_class] using h

theorem gammaGroundRVObjectAtDegree_semiringClass {j : ℕ} (U : GammaGroundRVObject hc B j) (k : ℕ) :
    gammaGroundRVSemiringClass (gammaGroundRVObjectAtDegree U k) =
      if j = k then gammaGroundRVSemiringClass U else 0 := by
  by_cases h : j = k
  · subst k
    simp [gammaGroundRVObjectAtDegree]
  · simp only [gammaGroundRVObjectAtDegree,dite_eq_right h,ite_eq_right h,gammaGroundRVSemiringClass_empty]

theorem GammaGroundUnmeasuredTensorTerm.rvObjectAt_semiringClass
    (t : GammaGroundUnmeasuredTensorTerm hc B) (k : ℕ) :
    gammaGroundRVSemiringClass (t.rvObjectAt k) =
      if t.residueDegree+t.gammaDegree = k then gammaGroundUnmeasuredTensorMap t.value else 0 := by
  rw [GammaGroundUnmeasuredTensorTerm.rvObjectAt,gammaGroundRVObjectAtDegree_semiringClass,t.value_image]

theorem gammaGroundTensorListRVObject_semiringClass (k : ℕ)
    (l : List (GammaGroundUnmeasuredTensorTerm hc B)) :
    gammaGroundRVSemiringClass (gammaGroundTensorListRVObject k l) =
      gammaGroundUnmeasuredTensorMap
        (((gammaGroundTensorTermsInDegree k l).map GammaGroundUnmeasuredTensorTerm.value).sum) := by
  induction l with
  | nil => exact gammaGroundRVSemiringClass_empty.trans (map_zero _).symm
  | cons t l ih =>
    change gammaGroundRVSemiringClass ((t.rvObjectAt k).coprod (gammaGroundTensorListRVObject k l)) = _
    rw [gammaGroundRVSemiringClass_coprod,t.rvObjectAt_semiringClass,ih]
    by_cases h : t.residueDegree+t.gammaDegree = k <;>
      simp [gammaGroundTensorTermsInDegree,h,map_add]

/-- Equality of complete positive images restricts to equality of each
homogeneous block by actual RV bijections, without cancellation. -/
theorem gammaGroundTensorTermsInDegree_images_equal
    (l q : List (GammaGroundUnmeasuredTensorTerm hc B))
    (h : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundUnmeasuredTensorTerm.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundUnmeasuredTensorTerm.value).sum)) (k : ℕ) :
    gammaGroundUnmeasuredTensorMap
      (((gammaGroundTensorTermsInDegree k l).map GammaGroundUnmeasuredTensorTerm.value).sum) =
    gammaGroundUnmeasuredTensorMap
      (((gammaGroundTensorTermsInDegree k q).map GammaGroundUnmeasuredTensorTerm.value).sum) := by
  obtain ⟨E⟩ := gammaGroundTensorListRVObject_iso_of_equal_images l q h k
  have he := gammaGroundRVSemiringClass_iso E
  rw [gammaGroundTensorListRVObject_semiringClass,gammaGroundTensorListRVObject_semiringClass] at he
  exact he
end DiamondIntegral.Section3
