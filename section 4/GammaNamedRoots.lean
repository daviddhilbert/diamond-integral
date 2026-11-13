import «section 4».GammaDefinableMaps
import «section 4».GammaNamesSubgroup

/-! Unique Gamma roots are definable over the original base. Consequently
the actual group of base-definable Gamma constants is divisible, without
assuming a definable RV lift for a root. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaNamedRoots
open GammaOrderLogic GammaDefinableMaps GammaGroupNames GammaNamesSubgroup

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem root_definable_base (B : Base (M := M)) (c : Values.Gamma (M := M))
    (hc : GammaDefinableClosureAtBase B c) (q : ℕ) (hq : q ≠ 0) :
    GammaDefinableClosureAtBase B (RootableBy.root c q) := by
  apply (unary_definable_iff B {RootableBy.root c q}).mp
  exact root_definable B (fun _ : Fin 0 → Values.Gamma (M := M) => c)
    (constant_definable B c hc) q hq

instance namesRootable (B : Base (M := M)) : RootableBy (namesSubgroup B) ℕ where
  root a n := ⟨RootableBy.root a.val n, by
    by_cases hn : n = 0
    · rw [hn, RootableBy.root_zero]
      exact one_definable_base B
    · exact root_definable_base B a.val a.property n hn⟩
  root_zero a := Subtype.ext (RootableBy.root_zero a.val)
  root_cancel a hn := Subtype.ext (RootableBy.root_cancel a.val hn)

end DiamondIntegral.Section4.GammaNamedRoots
