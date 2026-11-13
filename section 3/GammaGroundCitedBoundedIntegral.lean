import «section 3».GammaGroundContext
import «section 3».GammaGroundRVFiltration
import «section 3».GammaGroundVFFiltration
import «section 3».GammaGroundLifting
import «section 3».QuotientIntegral

/-! The bounded-degree accepted [18] input, Proposition 6.18 and the
discussion before Theorem 6.19, with the complete Gamma ground retained.
The source is a genuine finite direct sum and the target uses the actual
manuscript VF dimension and literal finite RV fibres. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))

structure YinGammaGroundBoundedUnmeasuredLiftInput
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) where
  lift : ∀ k, GammaGroundRVBoundedPositive hc C.base k →+ GammaGroundVFKPlus hc C.base k
  lift_class : ∀ k (i : Fin (k + 1)) (U : GammaGroundRVObject hc C.base i.val),
    lift k (gammaGroundRVBoundedClass i U) =
      gammaGroundVFClass ((gammaGroundObjectLiftVF U).raise (Nat.le_of_lt_succ i.isLt))
  surjective : ∀ k, Function.Surjective (lift k)
  kernel : ∀ k, gammaGroundRVBoundedSpecialCongruence (ground := C.base) (k := k) hc = AddCon.ker (lift k)

variable {C hc} {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}

def gammaGroundBoundedUnmeasuredIntegral (H : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) (k : ℕ) :
    GammaGroundVFKPlus hc C.base k ≃+
      (gammaGroundRVBoundedSpecialCongruence (ground := C.base) (k := k) hc).Quotient :=
  integralFromKernel (H.lift k) (H.surjective k) _ (H.kernel k)

theorem gammaGroundBoundedUnmeasuredIntegral_characterization
    (H : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) (k : ℕ)
    (A : GammaGroundVFObject hc C.base k) (i : Fin (k + 1)) (U : GammaGroundRVObject hc C.base i.val) :
    gammaGroundBoundedUnmeasuredIntegral H k (gammaGroundVFClass A) =
      (gammaGroundRVBoundedSpecialCongruence (ground := C.base) (k := k) hc).mk' (gammaGroundRVBoundedClass i U) ↔
      gammaGroundVFClass A = gammaGroundVFClass ((gammaGroundObjectLiftVF U).raise (Nat.le_of_lt_succ i.isLt)) := by
  rw [gammaGroundBoundedUnmeasuredIntegral, integralFromKernel_characterization, H.lift_class]

theorem gammaGroundBoundedLift_transition (H : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv)
    {k l : ℕ} (hkl : k ≤ l) (a : GammaGroundRVBoundedPositive hc C.base k) :
    H.lift l (gammaGroundRVBoundedTransition hkl a) = gammaGroundVFRaiseKPlus hkl (H.lift k a) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a =>
    have hHom : ((H.lift l).comp (gammaGroundRVBoundedTransition hkl)).comp
        (DirectSum.of (fun j : Fin (k + 1) => GammaGroundRVKPlus hc C.base j.val) i) =
        ((gammaGroundVFRaiseKPlus hkl).comp (H.lift k)).comp
          (DirectSum.of (fun j : Fin (k + 1) => GammaGroundRVKPlus hc C.base j.val) i) := by
      apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundRVPresentation hc C.base i.val)
      intro U
      change H.lift l (gammaGroundRVBoundedTransition hkl (gammaGroundRVBoundedClass i U)) =
        gammaGroundVFRaiseKPlus hkl (H.lift k (gammaGroundRVBoundedClass i U))
      rw [show gammaGroundRVBoundedTransition hkl (gammaGroundRVBoundedClass i U) =
        gammaGroundRVBoundedClass ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hkl 1)⟩ U from
          gammaGroundRVBoundedTransition_of hkl i (gammaGroundRVClass U)]
      rw [H.lift_class, H.lift_class, gammaGroundVFRaiseKPlus_class]
      rfl
    exact DFunLike.congr_fun hHom a
  | add a b ha hb => simp only [map_add, ha, hb]

@[simp] theorem gammaGroundBoundedUnmeasuredIntegral_lift
    (H : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) (k : ℕ) (a : GammaGroundRVBoundedPositive hc C.base k) :
    gammaGroundBoundedUnmeasuredIntegral H k (H.lift k a) =
      (gammaGroundRVBoundedSpecialCongruence (ground := C.base) hc).mk' a :=
  (integralFromKernel_characterization (H.lift k) (H.surjective k) _ (H.kernel k) (H.lift k a) a).mpr rfl

theorem gammaGroundBoundedUnmeasuredIntegral_transition
    (H : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv)
    {k l : ℕ} (hkl : k ≤ l) (a : GammaGroundVFKPlus hc C.base k) :
    gammaGroundRVBoundedQuotientTransition hc hkl (gammaGroundBoundedUnmeasuredIntegral H k a) =
      gammaGroundBoundedUnmeasuredIntegral H l (gammaGroundVFRaiseKPlus hkl a) := by
  obtain ⟨b, rfl⟩ := H.surjective k a
  rw [gammaGroundBoundedUnmeasuredIntegral_lift, gammaGroundRVBoundedQuotientTransition_mk,
    ← gammaGroundBoundedLift_transition H hkl b, gammaGroundBoundedUnmeasuredIntegral_lift]

end DiamondIntegral.Section3
