import «section 6».MeasuredOrderedProgramData

/-! The zero-VF measured program is the actual identity and retains the
entire original Gamma form without an open-level hypothesis. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def zeroArityMeasuredOrderedProgram
    (A : DefSet (rawMixedSpace (M := M) 0 r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) : MeasuredOrderedProgram (G := G) A ω where
  arity := r
  rvTarget := A
  program := .zero A
  rvForm := ω
  factor := fun _ => rfl

end DiamondIntegral.Section6
