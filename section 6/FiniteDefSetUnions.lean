import «section 6».RVGoodPivotBounds

/-! Finite unions of actual definable presented sets, with all code
representatives included in the original-base defining graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] {S : Set M}

def finiteDefSetUnion {P : SpecialTransformations.DefinableGeometry.Space LRV M} {I : Type} [Finite I]
    (A : I → DefSet P S) : DefSet P S where
  carrier := ⋃ i, (A i).carrier
  definable := by
    have h := Set.definable_iUnion_of_finite (fun i => (A i).definable)
    change S.Definable LRV (P.preimage (⋃ i, (A i).carrier))
    convert h using 1
    ext z
    simp only [Space.preimage,Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨hz,i,hi⟩
      exact ⟨i,hz,hi⟩
    · rintro ⟨i,hz,hi⟩
      exact ⟨hz,i,hi⟩

end DiamondIntegral.Section6
