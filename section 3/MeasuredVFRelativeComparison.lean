import «section 3».CitedMeasuredIntegral
import «section 3».MeasuredRVRepresentatives

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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (VFType (M := M))]
variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : Section2.VFGeneratedFieldBase C.base}

theorem measuredLift_degree_compat (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) (k : ℕ) :
    H.lift.toAddMonoidHom.comp (measuredRVKPlusToSemiring hc (k := k)) =
      (measuredVFKPlusToSemiring C hc).comp (D.lift k) := by
  apply PositiveAdditiveGrothendieck.hom_ext (measuredRVPresentation hc (C.base : Set M) k)
  intro U
  change H.lift (measuredRVKPlusToSemiring hc (measuredRVClass hc U)) =
    measuredVFKPlusToSemiring C hc (D.lift k (measuredRVClass hc U))
  rw [measuredRVKPlusToSemiring_class, H.lift_class, D.lift_class, measuredVFKPlusToSemiring_class]

theorem measuredVFKPlusToSemiring_injective (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) (k : ℕ) :
    Function.Injective (measuredVFKPlusToSemiring C hc (k := k)) := by
  intro a b h
  obtain ⟨x, rfl⟩ := D.surjective k a
  obtain ⟨y, rfl⟩ := D.surjective k b
  have he := measuredLift_degree_compat H D k
  have ht : H.lift (measuredRVKPlusToSemiring hc x) = H.lift (measuredRVKPlusToSemiring hc y) :=
    (congrArg (fun f : MeasuredRVKPlus hc (C.base : Set M) k →+ MeasuredVFPositiveSemiring C hc => f x) he).trans
      (h.trans (congrArg (fun f : MeasuredRVKPlus hc (C.base : Set M) k →+ MeasuredVFPositiveSemiring C hc => f y) he).symm)
  have hk : measuredRVFixedSpecialCongruence C hc k x y := by
    change (measuredRVSpecialCongruence hc (C.base : Set M)).mk' (measuredRVKPlusToSemiring hc x) =
      (measuredRVSpecialCongruence hc (C.base : Set M)).mk' (measuredRVKPlusToSemiring hc y)
    apply (RingCon.eq _).mpr
    rw [H.kernel]
    exact ht
  rw [D.kernel k] at hk
  exact hk

theorem measuredVFClass_surjective (D : YinDegreeMeasuredLiftInput C hc B) (k : ℕ) :
    Function.Surjective (positiveClass (measuredVFPresentation C hc k)) := by
  intro a
  obtain ⟨x, rfl⟩ := D.surjective k a
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc x
  exact ⟨measuredObjectLift hc C k U, (D.lift_class U).symm⟩

def measuredVFDataClass {k : ℕ} (U : MeasuredVFData C hc k) : MeasuredVFKPlus C hc k :=
  positiveClass (measuredVFPresentation C hc k) U.toObject

@[simp] theorem measuredVFDataClass_inclusion {k : ℕ} (U : MeasuredVFData C hc k) :
    measuredVFKPlusToSemiring C hc (measuredVFDataClass U) = measuredVFDataSemiringClass C hc U := by
  rw [measuredVFDataClass, measuredVFKPlusToSemiring_class]
  unfold measuredVFObjectSemiringClass
  rw [MeasuredVFData.of_toObject]

theorem measuredVFDataClass_surjective (D : YinDegreeMeasuredLiftInput C hc B) (k : ℕ) :
    Function.Surjective (measuredVFDataClass (C := C) (hc := hc) (k := k)) := by
  intro a
  obtain ⟨U, rfl⟩ := measuredVFClass_surjective D k a
  refine ⟨MeasuredVFData.ofObject U, ?_⟩
  unfold measuredVFDataClass
  rw [MeasuredVFData.to_ofObject]

end DiamondIntegral.Section3
