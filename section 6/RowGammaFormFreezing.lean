import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowExactGammaTransport
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
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
import «section 6».RowFrozenFormRootControl
import «section 6».RowMeasuredProgramSubstitution

/-! (Row-form version for Remark 6.20, translated from `GammaFormFreezing`.)
 Simultaneous product conditions on all Gamma levels preserve the
actual form exactly under freezing. The complete original-base Gamma
map is unchanged, even when none of its individual values is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FMT
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem gammaFormExtension_freeze_row
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (ω : RowFormOn A qR)
    (hLevels : ∀ γ,∀ D : balls,CoordinateProductDomain
      {p | p ∈ A.carrier ∧ rowFormExtension ω p=γ} (vfOpenBall D.val) (centers D) j)
    (p : A) : rowFormExtension ω (mixedFamilyFreeze balls centers j p.val)=(ω p).val := by
  have h := mixedFamilyFreeze_mapsTo balls centers j
    {x | x ∈ A.carrier ∧ rowFormExtension ω x=(ω p).val} hsep (hLevels (ω p).val)
      (show p.val ∈ {x | x ∈ A.carrier ∧ rowFormExtension ω x=(ω p).val} from
        ⟨p.property,rowFormExtension_at ω p⟩)
  exact h.2

def frozenGammaFormRow
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ∀ D : balls,CoordinateProductDomain A.carrier (vfOpenBall D.val) (centers D) j)
    (ω : RowFormOn A qR) :
    RowFormOn A qR :=
  ω.comp ((mixedFamilyFreezeMap balls centers j hsep hballs hcenters A).corestrict
    (fun p => mixedFamilyFreeze_mapsTo balls centers j A.carrier hsep hA p.property))

theorem frozenGammaForm_eq_row
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ∀ D : balls,CoordinateProductDomain A.carrier (vfOpenBall D.val) (centers D) j)
    (ω : RowFormOn A qR)
    (hLevels : ∀ γ,∀ D : balls,CoordinateProductDomain
      {p | p ∈ A.carrier ∧ rowFormExtension ω p=γ} (vfOpenBall D.val) (centers D) j) :
    frozenGammaFormRow balls centers j hsep hballs hcenters hA ω=ω := by
  apply RowFormOn.ext
  intro p
  apply Subtype.ext
  have h := gammaFormExtension_freeze_row balls centers j hsep ω hLevels p
  rw [rowFormExtension_at ω
    ⟨mixedFamilyFreeze balls centers j p.val,mixedFamilyFreeze_mapsTo balls centers j A.carrier hsep hA p.property⟩] at h
  exact h

end DiamondIntegral.Section6.FMT
