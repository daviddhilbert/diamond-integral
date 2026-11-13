import «section 3».GammaGroundCitedMeasuredIntegral
import «section 3».PresentationHomExt

/-! Positive fixed-degree VF comparison consequences of the explicit
accepted global and degreewise Gamma-volume lift inputs. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}


theorem gammaGroundMeasuredLift_degree_compat (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) (k : ℕ) :
    H.lift.toAddMonoidHom.comp (gammaGroundMeasuredRVKPlusToSemiring (k := k)) =
      (gammaGroundMeasuredVFKPlusToSemiring C hc hv).comp (D.lift k) := by
  apply positiveAdditivePresentationHom_ext (gammaGroundMeasuredRVPresentation hc C.base k)
  intro U
  change H.lift (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U)) =
    gammaGroundMeasuredVFKPlusToSemiring C hc hv (D.lift k (gammaGroundMeasuredRVClass U))
  rw [gammaGroundMeasuredRVKPlusToSemiring_class, H.lift_class, D.lift_class, gammaGroundMeasuredVFKPlusToSemiring_class]

theorem gammaGroundMeasuredVFKPlusToSemiring_injective (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) (k : ℕ) :
    Function.Injective (gammaGroundMeasuredVFKPlusToSemiring C hc hv (k := k)) := by
  intro a b h
  obtain ⟨x, rfl⟩ := D.surjective k a
  obtain ⟨y, rfl⟩ := D.surjective k b
  have he := gammaGroundMeasuredLift_degree_compat H D k
  have ht : H.lift (gammaGroundMeasuredRVKPlusToSemiring x) = H.lift (gammaGroundMeasuredRVKPlusToSemiring y) :=
    (congrArg (fun f : GammaGroundMeasuredRVKPlus hc C.base k →+ GammaGroundMeasuredVFPositiveSemiring C hc hv => f x) he).trans
      (h.trans (congrArg (fun f : GammaGroundMeasuredRVKPlus hc C.base k →+ GammaGroundMeasuredVFPositiveSemiring C hc hv => f y) he).symm)
  have hk : gammaGroundMeasuredRVFixedSpecialCongruence C hc k x y := by
    change (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring x) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring y)
    apply (RingCon.eq _).mpr
    rw [H.kernel]
    exact ht
  rw [D.kernel k] at hk
  exact hk

end DiamondIntegral.Section3
