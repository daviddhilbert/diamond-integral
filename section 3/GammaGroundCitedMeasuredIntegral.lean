import «section 3».GammaGroundMeasuredVFSemiring
import «section 3».GammaGroundMeasuredRVGenerators
import «section 3».CompletionEquivalences
import «section 3».QuotientIntegral
import «section 3».PresentationHomExt

/-! Replaceable Gamma-volume inputs from accepted [18], Theorems
2.35–2.36, the opening extension of Section 7, Propositions 7.8–7.10
and Theorem 7.13. Genuine VF generation and nontriviality of the full
Gamma ground are retained by GammaGroundContext. The consequences below
do not supply the separate grading/universal-presentation comparisons. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

structure YinGammaGroundMeasuredLiftInput where
  lift : GammaGroundMeasuredRVPositiveSemiring hc C.base →+* GammaGroundMeasuredVFPositiveSemiring C hc hv
  lift_class : ∀ {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k),
    lift (gammaGroundMeasuredRVSemiringClass U) = gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift U)
  surjective : Function.Surjective lift
  kernel : gammaGroundMeasuredRVSpecialCongruence hc C.base = RingCon.ker lift

def gammaGroundMeasuredRVFixedSpecialHom (k : ℕ) : GammaGroundMeasuredRVKPlus hc C.base k →+
    (gammaGroundMeasuredRVSpecialCongruence hc C.base).Quotient :=
  (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk'.toAddMonoidHom.comp gammaGroundMeasuredRVKPlusToSemiring

def gammaGroundMeasuredRVFixedSpecialCongruence (k : ℕ) : AddCon (GammaGroundMeasuredRVKPlus hc C.base k) :=
  AddCon.ker (gammaGroundMeasuredRVFixedSpecialHom C hc k)

structure YinGammaGroundDegreeMeasuredLiftInput where
  lift : ∀ k, GammaGroundMeasuredRVKPlus hc C.base k →+
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k
  lift_class : ∀ {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k),
    lift k (gammaGroundMeasuredRVClass U) =
      gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv (gammaGroundMeasuredObjectLift U)
  surjective : ∀ k, Function.Surjective (lift k)
  kernel : ∀ k, gammaGroundMeasuredRVFixedSpecialCongruence C hc k = AddCon.ker (lift k)

variable {C hc hv}

def gammaGroundMeasuredPositiveIntegral (H : YinGammaGroundMeasuredLiftInput C hc hv) :
    GammaGroundMeasuredVFPositiveSemiring C hc hv ≃+* (gammaGroundMeasuredRVSpecialCongruence hc C.base).Quotient :=
  semiringIntegralFromKernel H.lift H.surjective _ H.kernel

theorem gammaGroundMeasuredPositiveIntegral_characterization
    (H : YinGammaGroundMeasuredLiftInput C hc hv) {k : ℕ}
    (A : GammaGroundMeasuredVFData hc C.base k) (U : GammaGroundMeasuredRVObject hc C.base k) :
    gammaGroundMeasuredPositiveIntegral H (gammaGroundMeasuredVFSemiringClass C hc hv A) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVSemiringClass U) ↔
      gammaGroundMeasuredVFSemiringClass C hc hv A =
        gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift U) := by
  rw [gammaGroundMeasuredPositiveIntegral, semiringIntegralFromKernel_characterization, H.lift_class]

@[simp] theorem gammaGroundMeasuredPositiveIntegral_lift_class
    (H : YinGammaGroundMeasuredLiftInput C hc hv) {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k) :
    gammaGroundMeasuredPositiveIntegral H (gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift U)) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVSemiringClass U) :=
  (gammaGroundMeasuredPositiveIntegral_characterization H (gammaGroundMeasuredObjectLift U) U).mpr rfl

theorem gammaGroundMeasuredPositiveIntegral_unique (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (e : GammaGroundMeasuredVFPositiveSemiring C hc hv →+* (gammaGroundMeasuredRVSpecialCongruence hc C.base).Quotient)
    (he : ∀ {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k),
      e (gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift U)) =
        (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVSemiringClass U)) :
    e = (gammaGroundMeasuredPositiveIntegral H).toRingHom := by
  have hcomp : e.comp H.lift = (gammaGroundMeasuredPositiveIntegral H).toRingHom.comp H.lift := by
    apply positivePresentationHom_ext (gammaGroundMeasuredRVSemiringPresentation hc C.base)
    rintro ⟨k, U⟩
    change e (H.lift (gammaGroundMeasuredRVSemiringClass U)) =
      gammaGroundMeasuredPositiveIntegral H (H.lift (gammaGroundMeasuredRVSemiringClass U))
    rw [H.lift_class]
    exact (he U).trans (gammaGroundMeasuredPositiveIntegral_lift_class H U).symm
  apply RingHom.ext
  intro a
  obtain ⟨u, rfl⟩ := H.surjective a
  exact RingHom.congr_fun hcomp u

def gammaGroundMeasuredRingIntegral (H : YinGammaGroundMeasuredLiftInput C hc hv) :
    GammaGroundMeasuredVFGrothendieckRing C hc hv ≃+*
      GammaGroundMeasuredRVGrothendieckRing hc C.base ⧸ Ideal.span
        ({gammaGroundMeasuredRVPrincipalElement hc C.base} : Set (GammaGroundMeasuredRVGrothendieckRing hc C.base)) :=
  (ringCompletionCongr (gammaGroundMeasuredPositiveIntegral H)).trans (gammaGroundMeasuredRVSpecialCompletionEquiv hc C.base)

def gammaGroundDegreeMeasuredIntegral (H : YinGammaGroundDegreeMeasuredLiftInput C hc hv) (k : ℕ) :
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k ≃+
      (gammaGroundMeasuredRVFixedSpecialCongruence C hc k).Quotient :=
  integralFromKernel (H.lift k) (H.surjective k) _ (H.kernel k)

theorem gammaGroundDegreeMeasuredIntegral_characterization
    (H : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ}
    (A : GammaGroundMeasuredVFData hc C.base k) (U : GammaGroundMeasuredRVObject hc C.base k) :
    gammaGroundDegreeMeasuredIntegral H k (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv A) =
      (gammaGroundMeasuredRVFixedSpecialCongruence C hc k).mk' (gammaGroundMeasuredRVClass U) ↔
      gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv A =
        gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv (gammaGroundMeasuredObjectLift U) := by
  rw [gammaGroundDegreeMeasuredIntegral, integralFromKernel_characterization, H.lift_class]

@[simp] theorem gammaGroundDegreeMeasuredIntegral_lift_class
    (H : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k) :
    gammaGroundDegreeMeasuredIntegral H k
        (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv (gammaGroundMeasuredObjectLift U)) =
      (gammaGroundMeasuredRVFixedSpecialCongruence C hc k).mk' (gammaGroundMeasuredRVClass U) :=
  (gammaGroundDegreeMeasuredIntegral_characterization H (gammaGroundMeasuredObjectLift U) U).mpr rfl

theorem gammaGroundDegreeMeasuredIntegral_unique (H : YinGammaGroundDegreeMeasuredLiftInput C hc hv) (k : ℕ)
    (e : GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k →+
      (gammaGroundMeasuredRVFixedSpecialCongruence C hc k).Quotient)
    (he : ∀ U : GammaGroundMeasuredRVObject hc C.base k,
      e (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv (gammaGroundMeasuredObjectLift U)) =
        (gammaGroundMeasuredRVFixedSpecialCongruence C hc k).mk' (gammaGroundMeasuredRVClass U)) :
    e = (gammaGroundDegreeMeasuredIntegral H k).toAddMonoidHom := by
  have hcomp : e.comp (H.lift k) = (gammaGroundDegreeMeasuredIntegral H k).toAddMonoidHom.comp (H.lift k) := by
    apply positiveAdditivePresentationHom_ext (gammaGroundMeasuredRVPresentation hc C.base k)
      (F := e.comp (H.lift k))
      (G := (gammaGroundDegreeMeasuredIntegral H k).toAddMonoidHom.comp (H.lift k))
    intro U
    change e (H.lift k (gammaGroundMeasuredRVClass U)) =
      gammaGroundDegreeMeasuredIntegral H k (H.lift k (gammaGroundMeasuredRVClass U))
    rw [H.lift_class]
    exact (he U).trans (gammaGroundDegreeMeasuredIntegral_lift_class H U).symm
  apply AddMonoidHom.ext
  intro a
  obtain ⟨u, rfl⟩ := H.surjective k a
  exact DFunLike.congr_fun hcomp u

end DiamondIntegral.Section3
