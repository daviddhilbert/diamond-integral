import «section 2».GeneralDiscPoints
import IntegrationSection6.SmallGammaDefinableClosure

/-! Lemma 2.20 (`algebraic:balls:definable:centers`) with smallness of the
base itself. The Section 2 statements assume that the definable closure of
the base is small. For an uncountable saturation cardinal this follows from
smallness of `S` and `G`, by the formula count in
`IntegrationInACVF.Section6.closureBase_real_small`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Algebraic case of Lemma 2.20 over a small base. -/
theorem lemma_2_20_algebraic_small {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : LRV.Substructure M} (F : VFGeneratedFieldBase S) (G : Set (Gamma M))
    (hS : Cardinal.mk (S : Set M) < κ) (hG : Cardinal.mk G < κ)
    (D : DC (M := M)) (hD : DiscAlgebraic ⟨(S : Set M), G⟩ D) :
    ∃ x : VF M, GammaParameters.AlgebraicAtBase ⟨(S : Set M), G⟩ .vf x.val ∧
      x.val ∈ BallImaginaries.underlying D :=
  lemma_2_20_algebraic hκ.le hs h00 F G
    (IntegrationInACVF.Section6.closureBase_real_small hκ ⟨(S : Set M), G⟩ hS hG) D hD

/-- Definable case of Lemma 2.20 over a small base. -/
theorem lemma_2_20_definable_small {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : LRV.Substructure M} (F : VFGeneratedFieldBase S) (G : Set (Gamma M))
    (hS : Cardinal.mk (S : Set M) < κ) (hG : Cardinal.mk G < κ)
    (D : DC (M := M)) (hD : DiscDefinable ⟨(S : Set M), G⟩ D) :
    ∃ x : VF M, GammaParameters.DefinableClosureAtBase ⟨(S : Set M), G⟩ .vf x.val ∧
      x.val ∈ BallImaginaries.underlying D :=
  lemma_2_20_definable hκ.le hs h00 F G
    (IntegrationInACVF.Section6.closureBase_real_small hκ ⟨(S : Set M), G⟩ hS hG) D hD

end DiamondIntegral.Section3