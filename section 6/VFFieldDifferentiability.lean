import «section 6».VFReciprocalDifferentiability
import «section 6».VFCoordinateArithmeticMaps

/-! Full differentiation of scalar products, quotients and elementary
VF coordinate arithmetic, including dependence on both coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem VFDifferentiableAt.multiply
    {f g : (Fin n → VF M) → Fin 1 → VF M} {a : Fin n → VF M}
    (hf : VFDifferentiableAt f a) (hg : VFDifferentiableAt g a) :
    VFDifferentiableAt (fun x (_ : Fin 1) => f x 0 * g x 0) a := by
  let u (x : Fin n → VF M) : Fin 2 → VF M := ![f x 0,g x 0]
  have hu : VFDifferentiableAt u a := by
    apply vfdifferentiableAt_components
    intro i
    fin_cases i
    · convert hf using 1
      funext x k
      fin_cases k
      rfl
    · convert hg using 1
      funext x k
      fin_cases k
      rfl
  let P : Fin 1 → MvPolynomial (Fin 2) (VF M) := fun _ => X 0 * X 1
  have h := VFDifferentiableAt.polynomial hu P
  simpa only [P,map_mul,aeval_X,u,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using h

theorem VFDifferentiableAt.divide
    {f g : (Fin n → VF M) → Fin 1 → VF M} {a : Fin n → VF M}
    (hf : VFDifferentiableAt f a) (hg : VFDifferentiableAt g a) (hg0 : g a 0 ≠ 0) :
    VFDifferentiableAt (fun x (_ : Fin 1) => f x 0 / g x 0) a := by
  simpa only [div_eq_mul_inv] using VFDifferentiableAt.multiply hf (VFDifferentiableAt.reciprocal hg hg0)

theorem vfdifferentiableAt_coordinateArithmetic (op : RVCoordinateOperation) (i j : Fin n)
    (a : Fin n → VF M) (ha : a i ≠ 0) (hb : a j ≠ 0) :
    VFDifferentiableAt (coordinateArithmetic op i j) a := by
  have hi : VFDifferentiableAt (fun x (_ : Fin 1) => x i) a :=
    vfdifferentiableAt_select (fun _ : Fin 1 => i) a
  have hj : VFDifferentiableAt (fun x (_ : Fin 1) => x j) a :=
    vfdifferentiableAt_select (fun _ : Fin 1 => j) a
  apply vfdifferentiableAt_components
  intro k
  by_cases hk : k=i
  · subst k
    simp only [coordinateArithmetic,Function.update_self]
    cases op
    · change VFDifferentiableAt (fun x (_ : Fin 1) => x i * x j) a
      exact VFDifferentiableAt.multiply (M := M) (f := fun x (_ : Fin 1) => x i)
        (g := fun x (_ : Fin 1) => x j) hi hj
    · change VFDifferentiableAt (fun x (_ : Fin 1) => x i / x j) a
      exact VFDifferentiableAt.divide (M := M) (f := fun x (_ : Fin 1) => x i)
        (g := fun x (_ : Fin 1) => x j) hi hj hb
    · change VFDifferentiableAt (fun x (_ : Fin 1) => x j / x i) a
      exact VFDifferentiableAt.divide (M := M) (f := fun x (_ : Fin 1) => x j)
        (g := fun x (_ : Fin 1) => x i) hj hi ha
  · simp only [coordinateArithmetic,Function.update_of_ne hk]
    exact vfdifferentiableAt_select (fun _ : Fin 1 => k) a

theorem coordinateArithmeticRVLift_differentiable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation)
    (i j : Fin n) (hij : i ≠ j) (p : rvLift U.object) :
    ∃ L,HasMixedVFDerivativeAt (coordinateArithmeticRVLift hc U op i j hij) p L := by
  obtain ⟨L,hL⟩ := vfdifferentiableAt_coordinateArithmetic op i j p.val.1
    (rvLift_vf_coordinate_ne_zero U p i) (rvLift_vf_coordinate_ne_zero U p j)
  obtain ⟨ρ,hρ⟩ := exists_fixed_label_ball_in_rvLift U p
  exact ⟨L,coordinateArithmetic op i j,⟨ρ,fun x hx => ⟨hρ x hx,rfl⟩⟩,hL⟩

end DiamondIntegral.Section6
