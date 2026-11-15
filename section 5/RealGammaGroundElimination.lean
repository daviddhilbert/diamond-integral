import «section 5».EmptyGammaSortedDefinability
import Section3.GammaClosureLaws

/-! Gamma names already definable over the real coefficient field can
be eliminated without adjoining an RV representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))

theorem realGammaGround_definable_iff
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) :
    DefinableOverBase B sn A ↔ DefinableOverBase (EmptyGammaGround.base B.real) sn A := by
  constructor
  · intro h
    exact h.eliminate_definable_params
      (fun a ha => (subset_closureBase (EmptyGammaGround.base B.real)).1 ha) hγ
  · intro h
    exact h.mono Set.Subset.rfl (Set.empty_subset _)

end DiamondIntegral.Section5
