import «section 6».MeasuredProjectedFreezing

/-! Freezing preserves the complete Gamma form's root-control invariant
when its balls are product domains for all levels simultaneously. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem frozen_form_control (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprodA : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (ω : Mixed M (n+1) r → Gamma M)
    (hprodLevels : ∀ γ, ∀ D : balls, FMT.CoordinateProductDomain {p | p ∈ A.carrier ∧ ω p = γ}
      (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (hControl : CoordinateFormRootControl (G := G) R ω) :
    CoordinateFormRootControl (G := G) (R.frozen balls centers j hsep hballs hcenters hprodA) ω :=
  coordinateFormRootControl_of_levels _ ω (fun γ => R.frozen_control balls centers j hsep hballs hcenters
    hprodA {p | p ∈ A.carrier ∧ ω p = γ} (hprodLevels γ) (hControl.levels γ))

end DiamondIntegral.Section6.CoordinateRootFamily
