import «section 6».RVCoordinateTranspositions

/-! Explicit double bounds for elementary RV coordinate arithmetic.
The estimates are made in the finite Gamma group, so no ordered-field
law is imposed on the paper's infinity element. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def RVCoordinateOperation.gammaValue (op : RVCoordinateOperation) (x y : Gamma M) : Gamma M :=
  match op with
  | .multiply => x*y
  | .divide => x/y
  | .divideFrom => y/x

theorem RVCoordinateOperation.value_gamma (op : RVCoordinateOperation)
    (x y : RVInfinity M) (hx : x.val ≠ iRVZero) (hy : y.val ≠ iRVZero) :
    Values.vrv (op.value x y) = (op.gammaValue (Values.gammaOf x hx) (Values.gammaOf y hy)).val := by
  cases op
  · exact RVOperations.vrv_mul x y
  · change Values.vrv (x/y) = ((Values.gammaOf x hx / Values.gammaOf y hy) : Gamma M).val
    simp only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv]
    exact map_mul RVOperations.vrvHom x y⁻¹ |>.trans
      (congrArg (fun z => Values.vrv x * z) (map_inv₀ RVOperations.vrvHom y))
  · change Values.vrv (y/x) = ((Values.gammaOf y hy / Values.gammaOf x hx) : Gamma M).val
    simp only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv]
    exact map_mul RVOperations.vrvHom y x⁻¹ |>.trans
      (congrArg (fun z => Values.vrv y * z) (map_inv₀ RVOperations.vrvHom x))

theorem gamma_square_interval_mul {δ a b : Gamma M}
    (ha : δ⁻¹ ≤ a ∧ a ≤ δ) (hb : δ⁻¹ ≤ b ∧ b ≤ δ) :
    (δ*δ)⁻¹ ≤ a*b ∧ a*b ≤ δ*δ := by
  constructor
  · rw [mul_inv]
    exact mul_le_mul' ha.1 hb.1
  · exact mul_le_mul' ha.2 hb.2

theorem gamma_interval_inv {δ a : Gamma M} (ha : δ⁻¹ ≤ a ∧ a ≤ δ) :
    δ⁻¹ ≤ a⁻¹ ∧ a⁻¹ ≤ δ := by
  exact ⟨inv_le_inv' ha.2,by simpa only [inv_inv] using inv_le_inv' ha.1⟩

theorem RVCoordinateOperation.gammaValue_bounds (op : RVCoordinateOperation) {δ a b : Gamma M}
    (ha : δ⁻¹ ≤ a ∧ a ≤ δ) (hb : δ⁻¹ ≤ b ∧ b ≤ δ) :
    (δ*δ)⁻¹ ≤ op.gammaValue a b ∧ op.gammaValue a b ≤ δ*δ := by
  cases op
  · exact gamma_square_interval_mul ha hb
  · simpa only [gammaValue,div_eq_mul_inv] using gamma_square_interval_mul ha (gamma_interval_inv hb)
  · simpa only [gammaValue,div_eq_mul_inv] using gamma_square_interval_mul hb (gamma_interval_inv ha)

theorem rvCoordinateArithmeticObject_doublyBounded (U : RVObject (M := M) S n)
    (op : RVCoordinateOperation) (i j : Fin n) (hU : ∀ u k, (U.value u k).val ≠ iRVZero)
    (hB : RVObjectDoublyBounded U) : RVObjectDoublyBounded (rvCoordinateArithmeticObject U op i j) := by
  refine ⟨hB.1,?_⟩
  obtain ⟨γ,hγ⟩ := hB.2
  let δ := max γ (1 : Gamma M)
  have hδ : δ ≤ δ*δ := by
    simpa only [mul_one] using mul_le_mul' (le_refl δ) (le_max_right γ (1 : Gamma M))
  have hγδ : γ ≤ δ := le_max_left _ _
  have hOld (u : U.domain) (k : Fin n) :
      δ⁻¹ ≤ Values.gammaOf (U.value u k) (hU u k) ∧ Values.gammaOf (U.value u k) (hU u k) ≤ δ := by
    have h := hγ (U.value u) ⟨u,rfl⟩ k
    exact ⟨(inv_le_inv' hγδ).trans h.1,h.2.trans hγδ⟩
  refine ⟨δ*δ,?_⟩
  rintro t ⟨u,rfl⟩ k
  rw [rvCoordinateArithmeticObject_value]
  by_cases hk : k = i
  · subst k
    rw [Function.update_self,op.value_gamma _ _ (hU u i) (hU u j)]
    exact op.gammaValue_bounds (hOld u i) (hOld u j)
  · rw [Function.update_of_ne hk]
    exact ⟨(inv_le_inv' hδ).trans (hOld u k).1,(hOld u k).2.trans hδ⟩

theorem rvReindexVolume_doublyBounded (U : RVObject (M := M) S n) (e : Equiv.Perm (Fin n))
    (hB : RVObjectDoublyBounded U) : RVObjectDoublyBounded (U.reindexVolume e) := by
  refine ⟨hB.1,?_⟩
  obtain ⟨γ,hγ⟩ := hB.2
  refine ⟨γ,?_⟩
  rintro t ⟨u,rfl⟩ k
  exact hγ (U.value u) ⟨u,rfl⟩ (e k)

end DiamondIntegral.Section6
