import «section 2».Conventions
import Section9.GammaJacobian

/-! Notation 2.8 for RV/Gamma coordinates of possibly different arities.
The paper's difference of total values is a quotient in the released
multiplicative Gamma group. Nonzero RV labels give actual finite values. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped BigOperators

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev GammaLabels (n m : ℕ) := (Fin n → RV M) × (Fin m → Gamma M)

noncomputable def rvFiniteValue (t : RV M) : Gamma M :=
  Values.gammaOf t.val (fun he => t.property (Subtype.ext he))

noncomputable def gammaLabelWeight {n m : ℕ} (p : GammaLabels (M := M) n m) : Gamma M :=
  (∏ i, rvFiniteValue (p.1 i)) * ∏ j, p.2 j

noncomputable def gammaJacobian {n m k l : ℕ}
    (p : GammaLabels (M := M) n m) (q : GammaLabels (M := M) k l) : Gamma M :=
  gammaLabelWeight q / gammaLabelWeight p

theorem rvFiniteValue_val (t : RV M) : (rvFiniteValue t).val = Values.vrv t.val := rfl

theorem gammaJacobian_self {n m : ℕ} (p : GammaLabels (M := M) n m) : gammaJacobian p p = 1 := by
  simp [gammaJacobian]

theorem gammaJacobian_comp {n m k l r s : ℕ}
    (p : GammaLabels (M := M) n m) (q : GammaLabels (M := M) k l) (u : GammaLabels (M := M) r s) :
    gammaJacobian p u = gammaJacobian q u * gammaJacobian p q := by
  simp [gammaJacobian,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem gammaJacobian_symm {n m k l : ℕ}
    (p : GammaLabels (M := M) n m) (q : GammaLabels (M := M) k l) :
    gammaJacobian q p = (gammaJacobian p q)⁻¹ := by
  simp [gammaJacobian]

theorem gammaJacobian_eq_companion {n : ℕ} (p q : Fin n → RV M) :
    gammaJacobian (p,Fin.elim0) (q,Fin.elim0) =
      SpecialTransformations.Section9.rvGammaJacobian (fun i => (p i).val) (fun i => (q i).val)
        (fun i he => (p i).property (Subtype.ext he)) (fun i he => (q i).property (Subtype.ext he)) := by
  simp only [gammaJacobian,gammaLabelWeight,Fin.prod_univ_zero,mul_one,
    SpecialTransformations.Section9.rvGammaJacobian,SpecialTransformations.Section9.rvVolumeGamma,rvFiniteValue]

end DiamondIntegral.Section2
