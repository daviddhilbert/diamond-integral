import «section 6».VFFieldDifferentiability

/-! Exact full determinants of the elementary VF arithmetic maps.
Inactive rows are literal identity rows, and the active partial is
computed from the proved one-variable derivative, including reciprocal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

set_option backward.isDefEq.respectTransparency true in
theorem determinant_eq_active_of_fixed_rows {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (h : ∀ j ≠ i,∀ k,A j k=(1 : Matrix (Fin n) (Fin n) K) j k) : A.det=A i i := by
  let I : Matrix (Fin n) (Fin n) K := 1
  have he : A=I.updateRow i (A i) := by
    ext j k
    by_cases hj : j=i
    · subst j
      rw [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hj]
      exact h j hj k
  have hr : (∑ k,A i k • I k)=A i := by
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,I,Matrix.one_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  calc
    A.det=(I.updateRow i (A i)).det := congrArg Matrix.det he
    _ = A i i := (congrArg (fun r => (I.updateRow i r).det) hr.symm).trans
      (by rw [Matrix.det_updateRow_sum,show I=1 from rfl,Matrix.det_one,smul_eq_mul,mul_one])

def RVCoordinateOperation.vfSlope (op : RVCoordinateOperation) (x y : VF M) : VF M :=
  match op with | .multiply => y | .divide => y⁻¹ | .divideFrom => -(y * x⁻¹ ^ 2)

theorem HasVFDerivativeAt.const_smul {m : ℕ}
    {f : (Fin n → VF M) → Fin m → VF M} {a : Fin n → VF M}
    {L : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)}
    (hf : HasVFDerivativeAt f a L) (c : VF M) :
    HasVFDerivativeAt (fun x => c • f x) a (c • L) := by
  have h := (hasVFDerivativeAt_affine (c • (LinearMap.id :
    (Fin m → VF M) →ₗ[VF M] (Fin m → VF M))) 0 (f a)).comp hf
  simpa only [LinearMap.smul_apply,LinearMap.id_apply,add_zero,Function.comp_def,
    LinearMap.smul_comp,LinearMap.id_comp] using h

theorem hasVFDerivativeAt_scalarArithmetic (op : RVCoordinateOperation) (x y : VF M) (hx : x ≠ 0) :
    HasVFDerivativeAt (fun z : Fin 1 → VF M => fun _ : Fin 1 => op.fieldValue (z 0) y)
      (fun _ => x) (op.vfSlope x y • (LinearMap.id : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M))) := by
  cases op <;> dsimp only [RVCoordinateOperation.vfSlope]
  · have h := hasVFDerivativeAt_affine (y • (LinearMap.id :
        (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M))) 0 (fun _ => x)
    convert h using 1
    funext z k
    fin_cases k
    simp [RVCoordinateOperation.fieldValue,mul_comm]
  · have h := hasVFDerivativeAt_affine (y⁻¹ • (LinearMap.id :
        (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M))) 0 (fun _ => x)
    convert h using 1
    funext z k
    fin_cases k
    simp [RVCoordinateOperation.fieldValue,div_eq_mul_inv,mul_comm]
  · have h := HasVFDerivativeAt.const_smul (hasVFDerivativeAt_reciprocal (fun _ => x) hx) y
    have hc : y • (- (x⁻¹ ^ 2) • (LinearMap.id :
        (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M))) =
        -(y*x⁻¹ ^ 2) • LinearMap.id := by rw [smul_smul,mul_neg]
    rw [hc] at h
    convert h using 1
    funext z k
    fin_cases k
    simp [RVCoordinateOperation.fieldValue,div_eq_mul_inv]

theorem coordinateArithmetic_active_partial (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j)
    (a : Fin n → VF M) (ha : a i ≠ 0) :
    HasVFPartialAt (coordinateArithmetic op i j) a i i (op.vfSlope (a i) (a j)) := by
  have h := hasVFDerivativeAt_scalarArithmetic op (a i) (a j) ha
  intro ε
  obtain ⟨δ,hδ⟩ := h.component 0 ε
  refine ⟨δ,fun t ht hclose => ?_⟩
  have hn : (fun _ : Fin 1 => t) ≠ 0 := by
    intro he
    exact ht (congrFun he 0)
  have hval : vfTupleValue (fun _ : Fin 1 => t)=Values.vfValueHom t := by
    obtain ⟨k,hk⟩ := vfTupleValue_eq_component (fun _ : Fin 1 => t) (by decide)
    exact hk
  have hclose' : δ.val < vfTupleValue (fun _ : Fin 1 => t) := hval.symm ▸ hclose
  have hs := hδ (fun _ : Fin 1 => t) hn hclose'
  rw [hval] at hs
  simpa only [coordinateArithmetic,Function.update_self,Pi.add_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne hij.symm,add_zero,LinearMap.smul_apply,LinearMap.id_apply,Pi.smul_apply,smul_eq_mul] using hs

theorem coordinateArithmetic_derivative_det (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j)
    (a : Fin n → VF M) (ha : a i ≠ 0)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hL : HasVFDerivativeAt (coordinateArithmetic op i j) a L) :
    (LinearMap.toMatrix' L).det=op.vfSlope (a i) (a j) := by
  have hRows : ∀ k ≠ i,∀ l,LinearMap.toMatrix' L k l=(1 : Matrix (Fin n) (Fin n) (VF M)) k l := by
    intro k hk l
    apply (hL.hasPartialAt l k).unique
    intro ε
    refine ⟨1,fun t ht _ => ?_⟩
    have he : coordinateArithmetic op i j (a+Pi.single l t) k-
        coordinateArithmetic op i j a k-(1 : Matrix (Fin n) (Fin n) (VF M)) k l*t=0 := by
      simp only [coordinateArithmetic,Function.update_of_ne hk,Pi.add_apply]
      by_cases hkl : k=l
      · subst l
        simp
      · simp [hkl]
    rw [he,map_zero]
    exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε)
      (fun he => ht ((vfValue_eq_zero_iff t).mp he)))
  rw [determinant_eq_active_of_fixed_rows _ i hRows]
  exact (hL.hasPartialAt i i).unique (coordinateArithmetic_active_partial op i j hij a ha)

theorem coordinateArithmeticRVLift_derivative_and_det (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation)
    (i j : Fin n) (hij : i ≠ j) (p : rvLift U.object) :
    ∃ L,HasMixedVFDerivativeAt (coordinateArithmeticRVLift hc U op i j hij) p L ∧
      (LinearMap.toMatrix' L).det=op.vfSlope (p.val.1 i) (p.val.1 j) := by
  obtain ⟨L,hL⟩ := vfdifferentiableAt_coordinateArithmetic op i j p.val.1
    (rvLift_vf_coordinate_ne_zero U p i) (rvLift_vf_coordinate_ne_zero U p j)
  obtain ⟨ρ,hρ⟩ := exists_fixed_label_ball_in_rvLift U p
  exact ⟨L,⟨coordinateArithmetic op i j,⟨ρ,fun x hx => ⟨hρ x hx,rfl⟩⟩,hL⟩,
    coordinateArithmetic_derivative_det op i j hij _ (rvLift_vf_coordinate_ne_zero U p i) hL⟩

end DiamondIntegral.Section6
