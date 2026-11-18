import «section 6».RowArbitraryCoordinateBranches
import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleRVRefinement
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleTagBranchAssembly
import «section 6».RowFormCompatibleTagComponents
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
import «section 6».RowRVRefinementGammaForms
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowMeasuredRVRefinementPreparation
import «section 6».RowFormCompatibleTagChainExtensions
import «section 6».ComplementaryBranchPreparation

/-! (Row-form version for Remark 6.20, translated from `MeasuredBranchFormConstancy`.)
 Exact forms on a measured branch agree on every whole ambient
output-label fibre meeting that branch. These comparisons use the
actual local and ambient maps, including their retained old labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {hQC : ∀ i,(Q i).carrier ⊆ C.carrier}
variable {η : RowFormOn C qR}
variable (T : MeasuredCoordinatePreparationRow (G := G) C Q hQC η)
variable {X : SynchronizedTagBranchFrame C Q}
namespace SynchronizedTagBranchExtension

theorem source_form_constant_on_selected_row
    (F : SynchronizedTagBranchExtension (G := G) X T.map hQC)
    (ω : RowFormOn X.ambient qR)
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,X.subset p.property⟩).val)
    (p q : X.ambient) (he : (F.map p).val.2=(F.map q).val.2) (hpU : p.val.2 ∈ X.tags.carrier) :
    (ω p).val=(ω q).val := by
  have hRet := F.oldLabels_at
  have hOld : p.val.2=q.val.2 := (hRet p).symm.trans ((congrArg (fun u => u ∘ F.oldLabels) he).trans (hRet q))
  have hpC : p.val ∈ C.carrier := (Set.ext_iff.mp X.source_eq p.val).mpr ⟨p.property,hpU⟩
  have hqC : q.val ∈ C.carrier := (Set.ext_iff.mp X.source_eq q.val).mpr ⟨q.property,hOld ▸ hpU⟩
  let a : C := ⟨p.val,hpC⟩
  let b : C := ⟨q.val,hqC⟩
  have hImages : (T.map a).val.2=(T.map b).val.2 := by
    rw [← congrArg Prod.snd (F.branch a),← congrArg Prod.snd (F.branch b)]
    exact he
  have h := T.constant (T.map a).val (T.map a).property (T.map b).val (T.map b).property hImages
  rw [rowFormExtension_at _ (T.map a),rowFormExtension_at _ (T.map b)] at h
  exact (hForm a).symm.trans ((T.transportRow a).symm.trans (h.trans ((T.transportRow b).trans (hForm b))))

theorem source_form_constant_row
    (F : SynchronizedTagBranchExtension (G := G) X T.map hQC)
    (ω : RowFormOn X.ambient qR)
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,X.subset p.property⟩).val)
    (hOutside : ∀ p q : X.ambient,p.val.2=q.val.2 → p.val.2 ∉ X.tags.carrier → (ω p).val=(ω q).val) :
    ∀ p q : X.ambient,(F.map p).val.2=(F.map q).val.2 → (ω p).val=(ω q).val := by
  intro p q he
  by_cases hpU : p.val.2 ∈ X.tags.carrier
  · exact F.source_form_constant_on_selected_row T ω hForm p q he hpU
  · apply hOutside p q _ hpU
    exact (F.oldLabels_at p).symm.trans
      ((congrArg (fun u => u ∘ F.oldLabels) he).trans (F.oldLabels_at q))

theorem image_branch_form_constant_row
    (h00 : M ⊨ Axioms.ACVF00) (F : SynchronizedTagBranchExtension (G := G) X T.map hQC)
    (ω : RowFormOn X.ambient qR)
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,X.subset p.property⟩).val)
    (Ω : RowFormOn F.output.ambient qR)
    (hTransport : ∀ p : X.ambient,(Ω (F.map p)).val=(ω p).val) :
    ∀ p q : F.output.ambient,p.val.2=q.val.2 → p.val.2 ∈ F.output.tags.carrier → (Ω p).val=(Ω q).val := by
  intro p q he hpU
  have hf := F.chain.toChain.toSpecial.bijective h00
  let a := F.map.inverse hf p
  let b := F.map.inverse hf q
  have hOut : (F.map a).val.2=(F.map b).val.2 := by
    rw [Map.apply_inverse,Map.apply_inverse]
    exact he
  have hIn : a.val.2 ∈ X.tags.carrier := (F.selected a).mp (by
    change (F.map (F.map.inverse hf p)).val.2 ∈ F.output.tags.carrier
    rw [Map.apply_inverse]
    exact hpU)
  have h := F.source_form_constant_on_selected_row T ω hForm a b hOut hIn
  have ha := hTransport a
  have hb := hTransport b
  rw [Map.apply_inverse] at ha hb
  exact ha.trans (h.trans hb.symm)

end SynchronizedTagBranchExtension
end DiamondIntegral.Section6
