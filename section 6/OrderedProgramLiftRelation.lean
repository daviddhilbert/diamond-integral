import «section 6».OrderedStandardContractionPrograms
import «section 6».ContractionMapTransports

/-! The full map of an ordered program is its actual stage composition:
at each successor, lift the tail while carrying the contracted coordinate,
then compose with the current stage. This records the stage provenance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive IsOrderedProgramLift (S : Set M) :
    {n r q : ℕ} → {A : DefSet (rawMixedSpace (M := M) n r) S} →
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} →
    OrderedStandardContractionProgram (G := G) S A U →
    {B : DefSet (rawMixedSpace (M := M) n q) S} → Map A B → Prop where
  | zero {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 0 r) S) :
      IsOrderedProgramLift S (.zero A) (Map.id A)
  | step {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
      {U : DefSet (rawMixedSpace (M := M) 0 q) S}
      (T : StandardContractionStage (G := G) A)
      (tail : OrderedStandardContractionProgram (G := G) S T.contracted U)
      {B : DefSet (rawMixedSpace (M := M) n q) S} {f : Map T.contracted B}
      (hTail : IsOrderedProgramLift S tail f)
      (hLabels : ∀ p : T.contracted,(f p).val.2 (tail.oldLabels T.leading)=p.val.2 T.leading)
      (hTarget : T.target=rvCoordinateBundle T.contracted T.leading) :
      IsOrderedProgramLift S (.step T tail)
        ((carryLastMap f T.leading (tail.oldLabels T.leading) hLabels).comp (changeMapTarget T.lift hTarget))

end DiamondIntegral.Section6
