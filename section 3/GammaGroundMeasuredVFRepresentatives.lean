import «section 3».GammaGroundMeasuredVFRelativeComparison
import «section 3».GammaGroundMeasuredRVRepresentatives

/-! The accepted degreewise lift supplies actual measured VF object
representatives of every positive class over the complete Gamma ground. -/
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
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}

theorem gammaGroundMeasuredVFClass_surjective (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) (k : ℕ) :
    Function.Surjective (gammaGroundMeasuredVFClass (hc := hc) (ground := C.base)
      C.uncountable.le C.saturated C.small_real hv (n := k)) := by
  intro a
  obtain ⟨x, rfl⟩ := D.surjective k a
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective x
  exact ⟨gammaGroundMeasuredObjectLift U, (D.lift_class U).symm⟩

end DiamondIntegral.Section3
