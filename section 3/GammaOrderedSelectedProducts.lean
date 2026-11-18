import IntegrationSection6.OrderedSelectedWeights

/-! The recursive selected coordinate order preserves the full product,
not only the RV rank. This is the multiplicative version of the saved
ordered-selected-weight proof and applies to genuine Gamma weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {W : Type*} [CommMonoid W]

theorem gammaOrderedSelectedIndex_product {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (P : OrderedContractionProgram S A D) {k : ℕ} (ρ : Fin k → Fin a) (w : Fin b → W) :
    (∏ j, w (orderedSelectedIndex P ρ j)) =
      (∏ i, w (P.volumeIndex i)) * ∏ j, w (suffixIndex P.rvArity_le (ρ j)) := by
  induction P generalizing k with
  | zero A =>
    have hidx (j : Fin k) : suffixIndex (OrderedContractionProgram.zero A).rvArity_le (ρ j) = ρ j := by
      apply Fin.ext
      simp [suffixIndex]
    simp only [orderedSelectedIndex,Fin.prod_univ_zero,one_mul,hidx]
    rfl
  | @step n a b A D T tail ih =>
    change (∏ j, w (orderedSelectedIndex tail (headVolumeIndex T ρ) j)) = _
    rw [ih]
    have hOld : (fun j => w (suffixIndex tail.rvArity_le (headVolumeIndex T ρ j))) =
        Fin.append (fun _ : Fin 1 => w ((OrderedContractionProgram.step T tail).volumeIndex 0))
          (fun j => w (suffixIndex (OrderedContractionProgram.step T tail).rvArity_le (ρ j))) := by
      funext j
      cases j using Fin.addCases with
      | left j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      | right j =>
        simp only [headVolumeIndex,Fin.append_right,headSelectedLabelIndex]
        rw [suffixIndex_step_tail T tail (ρ j)]
    rw [hOld,Fin.prod_univ_add]
    simp only [Fin.append_left,Fin.append_right,Fin.prod_univ_one]
    rw [Fin.prod_univ_succ (fun i => w ((OrderedContractionProgram.step T tail).volumeIndex i))]
    change _ * (_ * _) = (_ * (∏ i, w (tail.volumeIndex i))) * _
    ac_rfl

theorem gammaOrderedSelectedIndex_empty_product {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (P : OrderedContractionProgram S A D) (w : Fin b → W) :
    (∏ j, w (orderedSelectedIndex P (Fin.elim0 : Fin 0 → Fin a) j)) = ∏ i, w (P.volumeIndex i) := by
  simpa only [Fin.prod_univ_zero,mul_one] using gammaOrderedSelectedIndex_product P (Fin.elim0 : Fin 0 → Fin a) w

end DiamondIntegral.Section3
