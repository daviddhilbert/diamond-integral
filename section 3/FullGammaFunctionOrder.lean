import «section 3».FullGammaFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {α : Type} [Finite α] {B : FullBaseAtomicity.Base (M := M)}

/-- Strict comparisons of full Gamma functions retain the same complete
original-ground graphs. -/
theorem FullGammaFunction.lt {f g : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) (hg : FullGammaFunction B g) :
    FullGammaSyntax.Definable B (fun z => f z < g z) := by
  let F : Fin 2 → (α → Values.Gamma (M := M)) → Values.Gamma (M := M) := ![f,g]
  have hF : ∀ i, FullGammaFunction B (F i) := by intro i; fin_cases i; exact hf; exact hg
  exact FullGammaFunction.substitute (FullGammaSyntax.lt_definable B (0 : Fin 2) 1) F hF
end DiamondIntegral.Section3
