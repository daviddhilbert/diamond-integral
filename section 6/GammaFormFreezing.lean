import «section 6».FrozenFormRootControl
import «section 6».MeasuredProgramSubstitution

/-! Simultaneous product conditions on all Gamma levels preserve the
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem gammaFormExtension_freeze
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ γ,∀ D : balls,CoordinateProductDomain
      {p | p ∈ A.carrier ∧ gammaFormExtension ω p=γ} (vfOpenBall D.val) (centers D) j)
    (p : A) : gammaFormExtension ω (mixedFamilyFreeze balls centers j p.val)=(ω p).val := by
  have h := mixedFamilyFreeze_mapsTo balls centers j
    {x | x ∈ A.carrier ∧ gammaFormExtension ω x=(ω p).val} hsep (hLevels (ω p).val)
      (show p.val ∈ {x | x ∈ A.carrier ∧ gammaFormExtension ω x=(ω p).val} from
        ⟨p.property,gammaFormExtension_at ω p⟩)
  exact h.2

def frozenGammaForm
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ∀ D : balls,CoordinateProductDomain A.carrier (vfOpenBall D.val) (centers D) j)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    Map A (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  ω.comp ((mixedFamilyFreezeMap balls centers j hsep hballs hcenters A).corestrict
    (fun p => mixedFamilyFreeze_mapsTo balls centers j A.carrier hsep hA p.property))

theorem frozenGammaForm_eq
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ∀ D : balls,CoordinateProductDomain A.carrier (vfOpenBall D.val) (centers D) j)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ γ,∀ D : balls,CoordinateProductDomain
      {p | p ∈ A.carrier ∧ gammaFormExtension ω p=γ} (vfOpenBall D.val) (centers D) j) :
    frozenGammaForm balls centers j hsep hballs hcenters hA ω=ω := by
  apply Map.ext
  intro p
  apply Subtype.ext
  have h := gammaFormExtension_freeze balls centers j hsep ω hLevels p
  rw [gammaFormExtension_at ω
    ⟨mixedFamilyFreeze balls centers j p.val,mixedFamilyFreeze_mapsTo balls centers j A.carrier hsep hA p.property⟩] at h
  exact h

end DiamondIntegral.Section6.FMT
