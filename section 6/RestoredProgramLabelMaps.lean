import «section 6».RestoredStageLabelData
import «section 6».OrderedStandardContractionPrograms
import «section 6».PureRVDiscQuotients
import «section 6».TupleCoordinateMaps

/-! The contracted target of an actual restored stage still selects
every label of its original preparation. All later stages retain these
labels, giving an actual original-base map on the final RV target. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {B : DefSet (rawMixedSpace (M := M) (n+1) s) S} {f : Map A B}
namespace RestoredStageLabelData

def oldIndex (D : RestoredStageLabelData (G := G) f) : Fin s → Fin D.stage.arity := Fin.cast D.arity_eq.symm

def finalOldTags (D : RestoredStageLabelData (G := G) f)
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (tail : OrderedStandardContractionProgram (G := G) S D.stage.contracted U) :
    Map U (pureRVTagDomain B) := by
  let σ := tail.oldLabels ∘ D.oldIndex
  let R := (rvTupleSelectMap S σ).comp (rvTailMap U)
  refine R.corestrict ?_
  intro u
  obtain ⟨b,hb⟩ := tail.surjective u
  obtain ⟨p,hp⟩ := D.stage.contraction_surjective b
  refine ⟨f p,funext (fun i => ?_)⟩
  change (f p).val.2 i=u.val.2 (tail.oldLabels (D.oldIndex i))
  calc
    _ = (D.stage.contraction p).val.2 (D.oldIndex i) := (D.labels p i).symm
    _ = b.val.2 (D.oldIndex i) := congrArg (fun z : D.stage.contracted => z.val.2 (D.oldIndex i)) hp
    _ = (tail.toMap b).val.2 (tail.oldLabels (D.oldIndex i)) := (tail.retained b (D.oldIndex i)).symm
    _ = _ := congrArg (fun z : U => z.val.2 (tail.oldLabels (D.oldIndex i))) hb

theorem finalOldTags_value (D : RestoredStageLabelData (G := G) f)
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (tail : OrderedStandardContractionProgram (G := G) S D.stage.contracted U) (u : U) :
    (D.finalOldTags tail u).val=u.val.2 ∘ (tail.oldLabels ∘ D.oldIndex) := rfl

theorem finalOldTags_commutes (D : RestoredStageLabelData (G := G) f)
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (tail : OrderedStandardContractionProgram (G := G) S D.stage.contracted U) (p : A) :
    (D.finalOldTags tail ((OrderedStandardContractionProgram.step D.stage tail).toMap p)).val=(f p).val.2 := by
  funext i
  change (tail.toMap (D.stage.contraction p)).val.2 (tail.oldLabels (D.oldIndex i))=(f p).val.2 i
  exact (tail.retained (D.stage.contraction p) (D.oldIndex i)).trans (D.labels p i)

end RestoredStageLabelData
end DiamondIntegral.Section6
