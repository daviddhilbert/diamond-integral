import «section 7».Lemma720Protect

/-! Lemma 7.20, step 10: the protected neighbourhood of the obstacles is definable.

Radii are coded by nonzero RV elements and balls by the upstream raw `ball` relation.
The set `Protect.U` is described by a first-order condition on raw codes (`UR`), and
`U_definable` shows it is definable over the base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4
open IntegrationInACVF.Section3ACVF.UniformGammaBallSyntax IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}

theorem ball_iff_value (r : M) (hr : NonzeroRV r) (x c : VF M) :
    ball r x.val c.val ↔ (codeValue r).val < vfValue (x - c) :=
  (ball_iff r hr x c).trans (mem_gammaBall_iff c x (codeValue r))

theorem codeValue_rv_val (t : RVInfinity M) (ht : t ≠ rvZero M) :
    (codeValue t.val).val = Values.vrv t := by
  have hr : NonzeroRV t.val := ⟨t.property, fun h => ht (Subtype.ext h)⟩
  simp only [codeValue, dite_eq_left hr]
  rfl

end DiamondIntegral.Section7.Lemma720
