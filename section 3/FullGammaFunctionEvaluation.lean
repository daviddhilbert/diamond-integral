import «section 3».FullGammaFunctions
import «section 3».RVGammaValueFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {α : Type} [Finite α]

theorem FullGammaFunction.eval_definable {f : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (c : α → Values.Gamma (M := M)) (hc : ∀ i, GammaDefinableClosureAtBase B (c i)) :
    GammaDefinableClosureAtBase B (f c) := by
  let F : α ⊕ Fin 1 → (Fin 1 → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
    Sum.elim (fun i _ => c i) (fun i z => z i)
  have hF : ∀ i, FullGammaFunction (integrationGammaBase B) (F i) := by
    intro i
    cases i with
    | inl i => exact FullGammaFunction.constant (c i) (integrationGammaDefinable (hc i))
    | inr i => exact FullGammaFunction.proj _ i
  have hh := FullGammaFunction.substitute hf F hF
  have hs : FullGammaSyntax.Scalar (integrationGammaBase B) {f c} := by
    apply (FullGammaSyntax.scalar_definable_iff _).mp
    exact hh.congr (fun z => eq_comm)
  exact (gammaScalar_definable_iff_native B {f c}).mpr hs
end DiamondIntegral.Section3
