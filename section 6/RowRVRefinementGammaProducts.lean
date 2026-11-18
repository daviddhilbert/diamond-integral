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
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
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
import «section 6».RowRVRefinementGammaDescent
import «section 6».RowGammaFormFreezing

/-! (Row-form version for Remark 6.20, translated from `RVRefinementGammaProducts`.)
 Product conditions on all descended Gamma levels lift to every
full retained-label fibre of the actual source. Consequently freezing
the joint source preserves the complete actual source Gamma form. -/

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
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem gamma_level_fibre_eq_row (X : RVRefinementFrame A)
    (ω : RowFormOn X.base qR)
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (p : X.base) (γ : Set (rawRVSpace (M := M) qR).Carrier) :
    vfFibre {q | q ∈ X.base.carrier ∧ rowFormExtension ω q=γ} p.val.2=
      vfFibre {q | q ∈ X.coveredBase.carrier ∧ rowFormExtension (X.descendedGammaFormRow ω hSame) q=γ}
        (p.val.2 ∘ X.labels) := by
  have hFibres := (X.fibre_eq_of_mem p).trans (X.coveredBase_fibre_of_mem p).symm
  have hValue (z : Fin n → VF M) (hz : (z,p.val.2) ∈ X.base.carrier) :
      rowFormExtension (X.descendedGammaFormRow ω hSame) (z,p.val.2 ∘ X.labels)=rowFormExtension ω (z,p.val.2) := by
    let a : X.base := ⟨(z,p.val.2),hz⟩
    have hAt := congrArg Subtype.val (X.descendedGammaForm_at_row ω hSame a)
    exact (rowFormExtension_at _ (X.oldMap.toImage a)).trans (hAt.trans (rowFormExtension_at ω a).symm)
  ext z
  have hMem : (z,p.val.2) ∈ X.base.carrier ↔ (z,p.val.2 ∘ X.labels) ∈ X.coveredBase.carrier :=
    Set.ext_iff.mp hFibres z
  constructor
  · rintro ⟨hz,hγ⟩
    exact ⟨hMem.mp hz,(hValue z hz).trans hγ⟩
  · rintro ⟨hz,hγ⟩
    exact ⟨hMem.mpr hz,(hValue z (hMem.mpr hz)).symm.trans hγ⟩

theorem gamma_level_product_row (X : RVRefinementFrame A)
    (ω : RowFormOn X.base qR)
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (γ : Set (rawRVSpace (M := M) qR).Carrier) (D : Set (VF M)) (c : VF M) (j : Fin n)
    (hProduct : FMT.CoordinateProductDomain
      {q | q ∈ X.coveredBase.carrier ∧ rowFormExtension (X.descendedGammaFormRow ω hSame) q=γ} D c j) :
    FMT.CoordinateProductDomain {q | q ∈ X.base.carrier ∧ rowFormExtension ω q=γ} D c j := by
  intro p hpD
  by_cases hFibre : (vfFibre X.base.carrier p.2).Nonempty
  · obtain ⟨a,ha⟩ := hFibre
    let q : X.base := ⟨(a,p.2),ha⟩
    have hF := X.gamma_level_fibre_eq_row ω hSame q γ
    have h₁ := Set.ext_iff.mp hF p.1
    have h₂ := Set.ext_iff.mp hF (Function.update p.1 j c)
    exact h₁.trans ((hProduct (p.1,p.2 ∘ X.labels) hpD).trans h₂.symm)
  · constructor
    · intro hp
      exact (hFibre ⟨p.1,hp.1⟩).elim
    · intro hp
      exact (hFibre ⟨Function.update p.1 j c,hp.1⟩).elim

theorem gamma_value_freeze_row (X : RVRefinementFrame A)
    (ω : RowFormOn X.base qR)
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hSep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val → x ∈ OpenBallCodes.underlying E.val → D=E)
    (hProducts : ∀ γ,∀ D : balls,FMT.CoordinateProductDomain
      {q | q ∈ X.coveredBase.carrier ∧ rowFormExtension (X.descendedGammaFormRow ω hSame) q=γ}
      (FMT.vfOpenBall D.val) (centers D) j) (p : X.base) :
    rowFormExtension ω (FMT.mixedFamilyFreeze balls centers j p.val)=(ω p).val :=
  FMT.gammaFormExtension_freeze_row balls centers j hSep ω
    (fun γ D => X.gamma_level_product_row ω hSame γ _ _ j (hProducts γ D)) p

end DiamondIntegral.Section6.RVRefinementFrame
