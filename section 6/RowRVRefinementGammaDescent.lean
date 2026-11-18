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
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowRVRefinementGammaForms
import «section 6».DefinableSurjectiveDescent

/-! (Row-form version for Remark 6.20, translated from `RVRefinementGammaDescent`.)
 The actual form descends to the covered old-label source whenever
it agrees on the fibres of that actual map. Its complete original-base
graph and open levels are constructed, without naming a Gamma value or
choosing any representative as a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RVRefinementFrame
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def descendedGammaFormRow (X : RVRefinementFrame A)
    (ω : RowFormOn X.base qR)
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val) :
    RowFormOn X.coveredBase qR :=
  RowFormOn.descent X.oldMap.toImage (map_toImage_surjective _) ω
    (fun p q he => Subtype.ext (hSame p q (congrArg (fun z : X.coveredBase => z.val) he)))

theorem descendedGammaForm_at_row (X : RVRefinementFrame A)
    (ω : RowFormOn X.base qR)
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val) (p : X.base) :
    X.descendedGammaFormRow ω hSame (X.oldMap.toImage p)=ω p :=
  RowFormOn.descent_apply _ _ _ _ p

theorem descendedGammaForm_levels_open_row (X : RVRefinementFrame A)
    (ω : RowFormOn X.base qR)
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ X.base.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ X.coveredBase.carrier ∧
      rowFormExtension (X.descendedGammaFormRow ω hSame) (x,u)=γ} := by
  intro u γ
  by_cases hFibre : (vfFibre X.coveredBase.carrier u).Nonempty
  · obtain ⟨x,hx⟩ := hFibre
    obtain ⟨p,hp⟩ := (map_toImage_surjective X.oldMap) ⟨(x,u),hx⟩
    have hTags : p.val.2 ∘ X.labels=u := congrArg (fun q : X.coveredBase => q.val.2) hp
    have hFibres : vfFibre X.base.carrier p.val.2=vfFibre X.coveredBase.carrier u := by
      have h := (X.fibre_eq_of_mem p).trans (X.coveredBase_fibre_of_mem p).symm
      rwa [hTags] at h
    have hValue (z : Fin n → VF M) (hz : (z,p.val.2) ∈ X.base.carrier) :
        rowFormExtension (X.descendedGammaFormRow ω hSame) (z,u)=rowFormExtension ω (z,p.val.2) := by
      let a : X.base := ⟨(z,p.val.2),hz⟩
      have hMap : (X.oldMap.toImage a).val=(z,u) := Prod.ext rfl hTags
      have hAt := congrArg Subtype.val (X.descendedGammaForm_at_row ω hSame a)
      exact (congrArg (rowFormExtension (X.descendedGammaFormRow ω hSame)) hMap).symm.trans
        ((rowFormExtension_at _ (X.oldMap.toImage a)).trans (hAt.trans (rowFormExtension_at ω a).symm))
    have hSet : {z : Fin n → VF M | (z,u) ∈ X.coveredBase.carrier ∧
        rowFormExtension (X.descendedGammaFormRow ω hSame) (z,u)=γ}=
        {z : Fin n → VF M | (z,p.val.2) ∈ X.base.carrier ∧ rowFormExtension ω (z,p.val.2)=γ} := by
      ext z
      have hMem : (z,u) ∈ X.coveredBase.carrier ↔ (z,p.val.2) ∈ X.base.carrier :=
        (Set.ext_iff.mp hFibres z).symm
      constructor
      · rintro ⟨hz,hγ⟩
        exact ⟨hMem.mp hz,(hValue z (hMem.mp hz)).symm.trans hγ⟩
      · rintro ⟨hz,hγ⟩
        exact ⟨hMem.mpr hz,(hValue z hz).trans hγ⟩
    rw [hSet]
    exact hLevels p.val.2 γ
  · have hEmpty : {z : Fin n → VF M | (z,u) ∈ X.coveredBase.carrier ∧
        rowFormExtension (X.descendedGammaFormRow ω hSame) (z,u)=γ}=∅ := by
      ext z
      exact ⟨fun hz => (hFibre ⟨z,hz.1⟩).elim,False.elim⟩
    rw [hEmpty]
    exact isOpen_empty

end DiamondIntegral.Section6.RVRefinementFrame
