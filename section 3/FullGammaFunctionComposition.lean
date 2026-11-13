import «section 3».FullGammaFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3.FullGammaFunction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : FullBaseAtomicity.Base (M := M)} {α β : Type} [Finite α] [Finite β]

theorem comp {f : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) (g : α → (β → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hg : ∀ i, FullGammaFunction B (g i)) :
    FullGammaFunction B (fun z => f (fun i => g i z)) := by
  let F : α ⊕ Fin 1 → ((β ⊕ Fin 1) → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
    Sum.elim (fun i z => g i (z ∘ Sum.inl)) (fun i z => z (.inr i))
  have hF : ∀ i, FullGammaFunction B (F i) := by
    intro i
    cases i with
    | inl i => exact (hg i).reindex Sum.inl
    | inr i => exact FullGammaFunction.proj B (Sum.inr i : β ⊕ Fin 1)
  exact FullGammaFunction.substitute hf F hF
end DiamondIntegral.Section3.FullGammaFunction
