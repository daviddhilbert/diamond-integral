import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowMeasuredProjectedFreezing

/-! (Row-form version for Remark 6.20, translated from `FrozenFormRootControl`.)
 Freezing preserves the complete Gamma form's root-control invariant
when its balls are product domains for all levels simultaneously. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem frozen_form_control_row (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprodA : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (ω : Mixed M (n+1) r → Set (rawRVSpace (M := M) qR).Carrier)
    (hprodLevels : ∀ γ, ∀ D : balls, FMT.CoordinateProductDomain {p | p ∈ A.carrier ∧ ω p = γ}
      (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (hControl : CoordinateFormRootControlRow (G := G) R ω) :
    CoordinateFormRootControlRow (G := G) (R.frozen balls centers j hsep hballs hcenters hprodA) ω :=
  coordinateFormRootControl_of_levels_row _ ω (fun γ => R.frozen_control balls centers j hsep hballs hcenters
    hprodA {p | p ∈ A.carrier ∧ ω p = γ} (hprodLevels γ) (hControl.levels γ))

end DiamondIntegral.Section6.CoordinateRootFamily
