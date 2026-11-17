import «section 3».MeasuredRealGroundRVCompatibility
import «section 3».MeasuredRVGradedComparison
import «section 3».GammaGroundMeasuredRVGradingConsequences

/-! Ordinary RV scissors and their redundant-Gamma presentation have
inverse maps in each degree and on the full positive semiring. All maps
are induced by the actual literal measured object adapters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)

theorem realRV_degree_inclusion_injective (k : ℕ) :
    Function.Injective (measuredRVKPlusToSemiring (M := M) (S := (C.base : Set M)) (k := k) hc) := by
  intro a b h
  obtain ⟨U,rfl⟩ := measuredRVClass_surjective hc a
  obtain ⟨V,rfl⟩ := measuredRVClass_surjective hc b
  rw [measuredRVKPlusToSemiring_class,measuredRVKPlusToSemiring_class] at h
  have he := congrArg (fun x : MeasuredRVPositiveSemiring hc (C.base : Set M) =>
    (measuredRVPresentationToDirectSum x) k) h
  rw [measuredRVPresentationToDirectSum_class,measuredRVPresentationToDirectSum_class] at he
  simpa only [measuredRVDirectSumClass,DirectSum.of_eq_same] using he

def rvSemiringFromRealInvariant : PositiveGrothendieck.Invariant (measuredRVSemiringPresentation hc (C.base : Set M))
    (R := GammaGroundMeasuredRVPositiveSemiring hc (measuredRealGroundContext C B).base) where
  toFun A := gammaGroundMeasuredRVSemiringClass (rvFromReal C hc B A.2)
  iso := by
    rintro A E ⟨k,U,V,⟨e⟩,rfl,rfl⟩
    exact gammaGroundMeasuredRVSemiringClass_iso (asIso (rvHomFromReal C hc B e.hom))
  empty := rvFromReal_empty_class C hc B 0
  unit := by
    let e : GammaGroundMeasuredRVHom (rvFromReal C hc B (MeasuredRVObject.unit hc (C.base : Set M)))
        (GammaGroundMeasuredRVObject.unit hc (measuredRealGroundContext C B).base) :=
      ⟨GammaGroundBijection.id _,fun _ => rfl⟩
    exact (gammaGroundMeasuredRVSemiringClass_iso (asIso e)).trans gammaGroundMeasuredRVSemiringClass_unit
  product A E := (gammaGroundMeasuredRVSemiringClass_iso (asIso (rvFromRealProductHom C hc B A.2 E.2))).trans
    (gammaGroundMeasuredRVSemiringClass_product _ _)
  scissor := by
    rintro A E F H (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · exact rvFromReal_scissor_class C hc B h
    · simp only [rvFromReal_empty_class,add_zero]

def rvSemiringFromReal : MeasuredRVPositiveSemiring hc (C.base : Set M) →+*
    GammaGroundMeasuredRVPositiveSemiring hc (measuredRealGroundContext C B).base :=
  PositiveGrothendieck.lift _ (rvSemiringFromRealInvariant C hc B)

theorem rvSemiringFromReal_class {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    rvSemiringFromReal C hc B (measuredRVSemiringClass hc U) = gammaGroundMeasuredRVSemiringClass (rvFromReal C hc B U) :=
  PositiveGrothendieck.lift_of (measuredRVSemiringPresentation hc (C.base : Set M)) (rvSemiringFromRealInvariant C hc B) ⟨k,U⟩

def rvSemiringToRealInvariant : PositiveGrothendieck.Invariant
    (gammaGroundMeasuredRVSemiringPresentation hc (measuredRealGroundContext C B).base)
    (R := MeasuredRVPositiveSemiring hc (C.base : Set M)) where
  toFun A := measuredRVSemiringClass hc (rvToReal C hc B A.2)
  iso := by
    rintro A E ⟨k,U,V,⟨e⟩,rfl,rfl⟩
    exact measuredRVSemiringClass_iso hc (asIso (rvHomToReal C hc B e.hom))
  empty := rvToReal_empty_class C hc B 0
  unit := by
    let e : MeasuredRVHom (rvToReal C hc B (GammaGroundMeasuredRVObject.unit hc (measuredRealGroundContext C B).base))
        (MeasuredRVObject.unit hc (C.base : Set M)) := ⟨DefinableBijection.id _,fun _ => rfl⟩
    exact (measuredRVSemiringClass_iso hc (asIso e)).trans (measuredRVSemiringClass_unit hc)
  product A E := (measuredRVSemiringClass_iso hc (asIso (rvToRealProductHom C hc B A.2 E.2))).trans
    (measuredRVSemiringClass_product hc _ _)
  scissor := by
    rintro A E F H (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · exact rvToReal_scissor_class C hc B h
    · simp only [rvToReal_empty_class,add_zero]

def rvSemiringToReal : GammaGroundMeasuredRVPositiveSemiring hc (measuredRealGroundContext C B).base →+*
    MeasuredRVPositiveSemiring hc (C.base : Set M) :=
  PositiveGrothendieck.lift _ (rvSemiringToRealInvariant C hc B)

theorem rvSemiringToReal_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k) :
    rvSemiringToReal C hc B (gammaGroundMeasuredRVSemiringClass U) = measuredRVSemiringClass hc (rvToReal C hc B U) :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredRVSemiringPresentation hc (measuredRealGroundContext C B).base)
    (rvSemiringToRealInvariant C hc B) ⟨k,U⟩

theorem rvSemiringToReal_fromReal (a : MeasuredRVPositiveSemiring hc (C.base : Set M)) :
    rvSemiringToReal C hc B (rvSemiringFromReal C hc B a) = a := by
  have he : (rvSemiringToReal C hc B).comp (rvSemiringFromReal C hc B) = RingHom.id _ := by
    apply positivePresentationHom_ext (measuredRVSemiringPresentation hc (C.base : Set M))
    rintro ⟨k,U⟩
    change rvSemiringToReal C hc B (rvSemiringFromReal C hc B (measuredRVSemiringClass hc U)) = measuredRVSemiringClass hc U
    rw [rvSemiringFromReal_class,rvSemiringToReal_class]
    exact measuredRVSemiringClass_iso hc (asIso (rvRealRoundTrip C hc B U))
  exact RingHom.congr_fun he a

theorem rvSemiringFromReal_toReal (a : GammaGroundMeasuredRVPositiveSemiring hc (measuredRealGroundContext C B).base) :
    rvSemiringFromReal C hc B (rvSemiringToReal C hc B a) = a := by
  have he : (rvSemiringFromReal C hc B).comp (rvSemiringToReal C hc B) = RingHom.id _ := by
    apply positivePresentationHom_ext (gammaGroundMeasuredRVSemiringPresentation hc (measuredRealGroundContext C B).base)
    rintro ⟨k,U⟩
    change rvSemiringFromReal C hc B (rvSemiringToReal C hc B (gammaGroundMeasuredRVSemiringClass U)) = gammaGroundMeasuredRVSemiringClass U
    rw [rvSemiringToReal_class,rvSemiringFromReal_class]
    exact gammaGroundMeasuredRVSemiringClass_iso (asIso (rvGroundRoundTrip C hc B U))
  exact RingHom.congr_fun he a

end DiamondIntegral.Section3.MeasuredRealGround
