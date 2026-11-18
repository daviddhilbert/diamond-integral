import «section 3».GammaGroundMeasuredRVGenerators
import «section 3».GammaGroundMeasuredRVGradingConsequences
import «section 3».GammaMeasuredClosureClassLift

/-! The homogeneous measured special relation introduces no degree-zero
identifications. Together with literal zero-degree descent this proves
the zero component of the Gamma-valued kernel without a cited input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

def gammaMeasuredRVDegreeZeroInvariant :
    PositiveGrothendieck.Invariant (gammaGroundMeasuredRVSemiringPresentation hc B)
      (R := GammaGroundMeasuredRVPositiveSemiring hc B) where
  toFun A := if A.1 = 0 then gammaGroundMeasuredRVSemiringClass A.2 else 0
  iso := by
    rintro A D ⟨k,U,V,⟨e⟩,rfl,rfl⟩
    by_cases hk : k=0
    · simpa only [hk,ite_true] using gammaGroundMeasuredRVSemiringClass_iso e
    · simp only [hk,ite_false]
  empty := by
    change (if (0:ℕ)=0 then gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredRVObject.empty hc B 0) else 0)=0
    rw [if_pos rfl,gammaGroundMeasuredRVSemiringClass_empty]
  unit := by
    change (if (0:ℕ)=0 then gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredRVObject.unit hc B) else 0)=1
    rw [if_pos rfl,gammaGroundMeasuredRVSemiringClass_unit]
  product := by
    rintro ⟨n,U⟩ ⟨m,V⟩
    change (if n+m=0 then gammaGroundMeasuredRVSemiringClass (U.product V) else 0) =
      (if n=0 then gammaGroundMeasuredRVSemiringClass U else 0) *
        (if m=0 then gammaGroundMeasuredRVSemiringClass V else 0)
    by_cases hn : n=0 <;> by_cases hm : m=0
    · simpa only [hn,hm,Nat.zero_add,ite_true] using gammaGroundMeasuredRVSemiringClass_product U V
    · simp only [hn,hm,Nat.zero_add,ite_true,ite_false,mul_zero]
    · simp only [hn,hm,Nat.add_zero,ite_true,ite_false,zero_mul]
    · have hnm : n+m ≠ 0 := fun h => hn (Nat.add_eq_zero.mp h).1
      simp only [hn,hm,hnm,ite_false,zero_mul]
  scissor := by
    rintro A D E F (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · by_cases hk : k=0
      · simpa only [hk,ite_true] using gammaGroundMeasuredRVSemiringClass_scissor h
      · simp only [hk,ite_false,add_zero]
    · simp only [gammaGroundMeasuredRVSemiringClass_empty,ite_self,add_zero]

def gammaMeasuredRVDegreeZeroProjection :
    GammaGroundMeasuredRVPositiveSemiring hc B →+* GammaGroundMeasuredRVPositiveSemiring hc B :=
  PositiveGrothendieck.lift _ gammaMeasuredRVDegreeZeroInvariant

@[simp] theorem gammaMeasuredRVDegreeZeroProjection_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) :
    gammaMeasuredRVDegreeZeroProjection (gammaGroundMeasuredRVSemiringClass U) =
      if k=0 then gammaGroundMeasuredRVSemiringClass U else 0 :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredRVSemiringPresentation hc B)
    (gammaMeasuredRVDegreeZeroInvariant (hc := hc) (B := B)) ⟨k,U⟩

theorem gammaMeasuredRVDegreeZeroProjection_fixed (a : GammaGroundMeasuredRVKPlus hc B 0) :
    gammaMeasuredRVDegreeZeroProjection (gammaGroundMeasuredRVKPlusToSemiring a) =
      gammaGroundMeasuredRVKPlusToSemiring a := by
  have he : gammaMeasuredRVDegreeZeroProjection.toAddMonoidHom.comp
      (gammaGroundMeasuredRVKPlusToSemiring (hc := hc) (ground := B) (k := 0)) = gammaGroundMeasuredRVKPlusToSemiring := by
    apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundMeasuredRVPresentation hc B 0)
    intro U
    change gammaMeasuredRVDegreeZeroProjection (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U)) = _
    rw [gammaGroundMeasuredRVKPlusToSemiring_class,gammaMeasuredRVDegreeZeroProjection_class,if_pos rfl]
    exact (gammaGroundMeasuredRVKPlusToSemiring_class U).symm
  exact DFunLike.congr_fun he a

theorem gammaMeasuredRVDegreeZeroProjection_respects :
    gammaGroundMeasuredRVSpecialCongruence hc B ≤ RingCon.ker (gammaMeasuredRVDegreeZeroProjection (hc := hc) (B := B)) := by
  apply RingCon.ringConGen_le.mpr
  rintro x y ⟨rfl,rfl⟩
  change gammaMeasuredRVDegreeZeroProjection _ = gammaMeasuredRVDegreeZeroProjection _
  rw [gammaMeasuredRVDegreeZeroProjection_class,gammaMeasuredRVDegreeZeroProjection_class]
  rfl

theorem gammaMeasuredRVSpecialQuotient_zero_injective : Function.Injective
    ((gammaGroundMeasuredRVSpecialCongruence hc B).mk'.toAddMonoidHom.comp
      (gammaGroundMeasuredRVKPlusToSemiring (k := 0))) := by
  intro a b hab
  let F := (gammaGroundMeasuredRVSpecialCongruence hc B).lift gammaMeasuredRVDegreeZeroProjection
    gammaMeasuredRVDegreeZeroProjection_respects
  have he := congrArg F hab
  change gammaMeasuredRVDegreeZeroProjection (gammaGroundMeasuredRVKPlusToSemiring a) =
    gammaMeasuredRVDegreeZeroProjection (gammaGroundMeasuredRVKPlusToSemiring b) at he
  rw [gammaMeasuredRVDegreeZeroProjection_fixed,gammaMeasuredRVDegreeZeroProjection_fixed] at he
  exact gammaGroundMeasuredRVKPlusToSemiring_injective he

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaContextMeasuredDegreeLift_zero_injective (C : GammaGroundContext M)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    Function.Injective (gammaContextMeasuredDegreeLift C hc hv 0) := by
  have he : gammaContextMeasuredDegreeLift C hc hv 0 =
      gammaZeroMeasuredRVClassLift C.uncountable.le C.saturated C.small_real hv := by
    apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundMeasuredRVPresentation hc C.base 0)
    intro U
    exact (gammaMeasuredClosureRVClassLift_class C.uncountable C.saturated C.model00 C.small_real C.small_gamma
      (C.fieldBase.gamma_closure_generated C.base.gamma) hv U).trans
        (gammaZeroMeasuredRVClassLift_class C.uncountable.le C.saturated C.small_real hv U).symm
  rw [he]
  exact (gammaZeroMeasuredClassEquiv C.uncountable.le C.saturated C.small_real hv).injective

theorem gammaContextMeasuredDegreeLift_zero_kernel (C : GammaGroundContext M)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    AddCon.ker ((gammaGroundMeasuredRVSpecialCongruence hc C.base).mk'.toAddMonoidHom.comp
      (gammaGroundMeasuredRVKPlusToSemiring (k := 0))) =
        AddCon.ker (gammaContextMeasuredDegreeLift C hc hv 0) := by
  ext a b
  change (_ = _) ↔ (_ = _)
  constructor
  · intro h
    exact congrArg (gammaContextMeasuredDegreeLift C hc hv 0) (gammaMeasuredRVSpecialQuotient_zero_injective h)
  · intro h
    exact congrArg ((gammaGroundMeasuredRVSpecialCongruence hc C.base).mk'.toAddMonoidHom.comp
      (gammaGroundMeasuredRVKPlusToSemiring (k := 0))) (gammaContextMeasuredDegreeLift_zero_injective C hc hv h)

end DiamondIntegral.Section3
