import «section 6».JacobianLocus
import Section9.DerivativeCoordinates

/-! Both lifted centripetal clauses are shears in one coordinate. Their
determinant is one at points of total differentiability, for arbitrary
focus functions. The statement does not infer total differentiability
from the existence of partial derivatives. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def coordinateShear (j : Fin n) (focus : (Fin n → VF M) → VF M)
    (a : Fin n → VF M) : Fin n → VF M :=
  Function.update a j (a j + focus (Function.update a j 0))

theorem coordinateShear_other (j i : Fin n) (hi : i ≠ j)
    (focus : (Fin n → VF M) → VF M) (a : Fin n → VF M) :
    coordinateShear j focus a i = a i := by
  simp only [coordinateShear,Function.update_of_ne hi]

theorem coordinateShear_axis (j : Fin n) (focus : (Fin n → VF M) → VF M)
    (a : Fin n → VF M) (t : VF M) :
    coordinateShear j focus (a + Pi.single j t) j = coordinateShear j focus a j + t := by
  have herase : Function.update (a + Pi.single j t) j 0 = Function.update a j 0 := by
    funext i
    by_cases hi : i = j
    · subst i
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hi,Pi.add_apply,Pi.single_eq_of_ne hi,add_zero]
  simp only [coordinateShear,Function.update_self,herase,Pi.add_apply,Pi.single_eq_same]
  abel

theorem determinant_one_of_fixed_rows {K : Type*} [Field K]
    (D : Matrix (Fin n) (Fin n) K) (j : Fin n)
    (hrow : ∀ i ≠ j, ∀ k, D i k = (1 : Matrix (Fin n) (Fin n) K) i k)
    (hjj : D j j = 1) : D.det = 1 := by
  classical
  let I : Matrix (Fin n) (Fin n) K := 1
  have he : D = I.updateRow j (D j) := by
    ext i k
    by_cases hij : i = j
    · subst i
      rw [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hij]
      exact hrow i hij k
  have hr : (∑ k, D j k • I k) = D j := by
    funext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,I,Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [hki]
    · simp
  rw [he]
  exact (congrArg (fun row => (I.updateRow j row).det) hr.symm).trans
    (by rw [Matrix.det_updateRow_sum,hjj,one_smul,show I = 1 from rfl,Matrix.det_one])

private theorem partial_of_exact_axis
    {f : (Fin n → VF M) → Fin n → VF M} {a : Fin n → VF M}
    (i j : Fin n) (d : VF M)
    (haxis : ∀ t : VF M, f (a + Pi.single j t) i = f a i + d*t) :
    HasVFPartialAt f a j i d := by
  intro ε
  refine ⟨1,fun t ht _ => ?_⟩
  rw [haxis t,add_sub_cancel_left,sub_self,map_zero]
  exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε)
    (fun he => ht ((vfValue_eq_zero_iff t).mp he)))

theorem coordinateShear_derivative_det_one
    (j : Fin n) (focus : (Fin n → VF M) → VF M) (a : Fin n → VF M)
    (L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M))
    (hL : HasVFDerivativeAt (coordinateShear j focus) a L) :
    (LinearMap.toMatrix' L).det = 1 := by
  classical
  apply determinant_one_of_fixed_rows _ j
  · intro i hi k
    apply (hL.hasPartialAt k i).unique
    apply partial_of_exact_axis
    intro t
    rw [coordinateShear_other j i hi,coordinateShear_other j i hi]
    by_cases hik : i = k
    · subst k
      simp
    · simp only [Pi.add_apply,Pi.single_eq_of_ne hik,Matrix.one_apply_ne hik,zero_mul]
  · apply (hL.hasPartialAt j j).unique
    apply partial_of_exact_axis
    intro t
    simpa only [one_mul] using coordinateShear_axis j focus a t

theorem coordinateShear_unitJacobian
    (j : Fin n) (focus : (Fin n → VF M) → VF M) (a : Fin n → VF M)
    (hd : ∃ L, HasDerivativeAt (coordinateShear j focus) a L) :
    HasUnitJacobianAt (coordinateShear j focus) a := by
  obtain ⟨L,hL⟩ := hd
  exact ⟨L,hL,coordinateShear_derivative_det_one j focus a L
    ((hasDerivativeAt_iff_companion _ _ _).mp hL)⟩

theorem locally_coordinateShear_unitJacobian
    {f : (Fin n → VF M) → Fin n → VF M} {a : Fin n → VF M}
    (j : Fin n) (focus : (Fin n → VF M) → VF M)
    (ρ : Gamma M) (he : Set.EqOn f (coordinateShear j focus) (vfBall a ρ))
    (hd : ∃ L, HasDerivativeAt f a L) : HasUnitJacobianAt f a := by
  obtain ⟨L,hL⟩ := hd
  have hs := ((hasDerivativeAt_iff_companion _ _ _).mp hL).congr_on_vfBall he
  exact ⟨L,hL,coordinateShear_derivative_det_one j focus a L hs⟩

end DiamondIntegral.Section6
