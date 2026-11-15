import «section 5».Completed18CellBaseTransfer
import IntegrationSection6.ContractionProgramExtensions

/-! The complete graph certificates of an actual contraction program
descend along definable parameter inclusions, without changing its steps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem BaseDefinableIn.program {G H : Base (M := M)} (h : BaseDefinableIn G H)
    {S : Set M} {n a l : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) (hT : GammaProgramDefinable G T) :
    GammaProgramDefinable H T := by
  induction T with
  | zero U => exact h.transfer hT
  | step T tail ih => exact ⟨h.transfer hT.1,h.transfer hT.2.1,ih hT.2.2⟩

end DiamondIntegral.Section5
