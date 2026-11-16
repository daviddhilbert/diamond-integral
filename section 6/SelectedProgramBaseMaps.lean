import «section 6».SelectedProgramContexts
import «section 6».TaggedPullbackRefinements
import «section 6».SelectedIndexedFocusRepair

/-! Actual base maps and covered joint frames of a finite fusion
stage. All maps are definable over the original base and select only
retained labels of the actual source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k t : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

namespace SelectedProgramContext

def baseMap (X : SelectedProgramContext η A P C π σ) : Map C B :=
  ((unaryFamilyBaseMap S n r s).comp (selectRVLabelsMap C (Fin.addCases π σ))).corestrict
    (by
      intro p
      change unaryFamilyBasePoint (selectedJointPoint π σ p.val) ∈ B.carrier
      rw [selectedJointPoint_base]
      exact X.base p.val p.property)

theorem baseMap_value (X : SelectedProgramContext η A P C π σ) (p : C) :
    (X.baseMap p).val=selectedUnaryBasePoint π p.val := selectedJointPoint_base π σ p.val

theorem baseMap_labels (X : SelectedProgramContext η A P C π σ) (p z : C) (h : p.val.2=z.val.2) :
    (X.baseMap p).val.2=(X.baseMap z).val.2 := by
  rw [X.baseMap_value,X.baseMap_value]
  exact congrArg (fun u => u ∘ π) h

def jointFrame (X : SelectedProgramContext η A P C π σ)
    (hTag : ∀ p ∈ (unaryIndexedMixedFamily η A).carrier,∀ z ∈ (unaryIndexedMixedFamily η A).carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1) : RVRefinementFrame (unaryIndexedMixedFamily η A) :=
  RVRefinementFrame.of_tagged_pullback (unaryIndexedMixedFamily η A) C (Fin.addCases π σ)
    X.proper X.doublyBounded X.pullback hTag (by
      intro p hp
      exact X.source p hp)

theorem jointFrame_piece (X : SelectedProgramContext η A P C π σ)
    (hTag : ∀ p ∈ (unaryIndexedMixedFamily η A).carrier,∀ z ∈ (unaryIndexedMixedFamily η A).carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1) (i : Fin k) :
    (X.jointFrame hTag).selectedPiece (unaryIndexedMixedFamily η (P i))=
      rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)) := rfl

end SelectedProgramContext

theorem UniformProgramFamily.initial_rows
    {T : CentripetalProgramTemplate (M := M) S 1 n s t}
    (U : UniformProgramFamily η T A P) (b c : B) (hTags : b.val.2=c.val.2) :
    ((leadingRVImageTemplate A).fibre (unaryFamilyParameter η b)).carrier=
      ((leadingRVImageTemplate A).fibre (unaryFamilyParameter η c)).carrier :=
  U.rows _ (T.initial_ambient_data_mem A P) b c hTags

theorem UniformProgramFamily.component_joint_tagged
    {T : CentripetalProgramTemplate (M := M) S 1 n s t}
    (U : UniformProgramFamily η T A P)
    (F : FocusComponentParameterTemplate (M := M) S 1 n s)
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ F.good A P)
    (hB : ∀ b ∈ B.carrier,∀ c ∈ B.carrier,b.2=c.2 → tupleRV M b.1=tupleRV M c.1) :
    ∀ p ∈ (unaryIndexedMixedFamily η A).carrier,∀ z ∈ (unaryIndexedMixedFamily η A).carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1 :=
  unaryIndexedMixedFamily_tagged hB η A U.pullback U.initial_rows (fun b => F.source_tagged _ (hGood b))

end DiamondIntegral.Section6
