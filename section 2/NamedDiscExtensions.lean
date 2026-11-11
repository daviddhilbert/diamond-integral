import «section 2».DiscTupleNames
import «section 2».PrefixedDiscCoordinates

/-! Adding a finite tuple of DC names keeps every old presentation free. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem DefinableOverFiniteDiscNames.append_names_left
    {B : ParameterBase M} {k l n : ℕ} {ground : Fin k → Bool}
    {d : Fin k → VF M} {τ : Fin k → Gamma M} {sn : Fin n → SortTag} {U : Set (Fin n → M)}
    (hU : DefinableOverFiniteDiscNames B ground d τ sn U)
    (closed : Fin l → Bool) (a : Fin l → VF M) (δ : Fin l → Gamma M) :
    DefinableOverFiniteDiscNames B (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) sn U := by
  apply DefinableOverFiniteDiscNames.pullback_names _ (Fin.castAdd l) _ _
  simpa only [Function.comp_def,Fin.append_left] using hU

theorem DefinableOverFiniteDiscNames.append_names_right
    {B : ParameterBase M} {k l n : ℕ} {closed : Fin l → Bool}
    {a : Fin l → VF M} {δ : Fin l → Gamma M} {sn : Fin n → SortTag} {U : Set (Fin n → M)}
    (hU : DefinableOverFiniteDiscNames B closed a δ sn U)
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M) :
    DefinableOverFiniteDiscNames B (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) sn U := by
  apply DefinableOverFiniteDiscNames.pullback_names _ (Fin.natAdd k) _ _
  simpa only [Function.comp_def,Fin.append_right] using hU

end DiamondIntegral.Section2
