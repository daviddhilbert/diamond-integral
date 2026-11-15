import «section 5».NativeRVGroundTransfer
import «section 5».NativeVFGroundTransfer
import «section 5».OriginalBaseVFIntegral

/-! The exact Section 3 lifting/kernel input transports across equivalent
actual sorted parameter presentations. Both native positive semirings
and the special congruence are transported before taking any Euler value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)

theorem sortedTransferVFPositive_lift {k : ℕ} (U : GammaGroundRVObject hc B k) :
    sortedTransferVFPositive H (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)) =
      gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite (sortedTransferRVObject H U)) := by
  rw [sortedTransferVFPositive_class]
  apply nativePositiveVFClass_bijection
  apply GammaGroundBijection.ofCarrierEq
  ext q
  change (∃ u : U.domain,u.val = q.2 ∧ (U.volume u).val = Section2.tupleRV M q.1) ↔
    ∃ u : (sortedTransferRVObject H U).domain,u.val = q.2 ∧
      ((sortedTransferRVObject H U).volume u).val = Section2.tupleRV M q.1
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,(sortedTransferRVVolume_value H U ⟨u.val,u.property⟩).trans hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,(sortedTransferRVVolume_value H U u).symm.trans hv⟩

theorem sortedTransferRVPositive_oneObject :
    sortedTransferRVPositive (hc := hc) H
      (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (rvOneObject B.real))) =
        gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (rvOneObject C.real)) := by
  rw [sortedTransferRVPositive_class]
  exact nativePositiveRVClass_bijection (GammaGroundBijection.ofCarrierEq rfl)

theorem sortedTransferRVPositive_positiveObject :
    sortedTransferRVPositive (hc := hc) H
      (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (rvPositiveObject hc B.real))) =
        gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (rvPositiveObject hc C.real)) := by
  rw [sortedTransferRVPositive_class]
  exact nativePositiveRVClass_bijection (GammaGroundBijection.ofCarrierEq rfl)

theorem sortedTransferRVPositive_special {x y : GammaGroundRVPositiveSemiring hc B}
    (h : gammaGroundRVSpecialCongruence hc B x y) :
    gammaGroundRVSpecialCongruence hc C (sortedTransferRVPositive H x) (sortedTransferRVPositive H y) := by
  let φ : GammaGroundRVPositiveSemiring hc B →+* (gammaGroundRVSpecialCongruence hc C).Quotient :=
    (gammaGroundRVSpecialCongruence hc C).mk'.comp (sortedTransferRVPositive H)
  have hle : gammaGroundRVSpecialCongruence hc B ≤ RingCon.ker φ := by
    apply RingCon.ringConGen_le.mpr
    rintro a b ⟨rfl,rfl⟩
    change (gammaGroundRVSpecialCongruence hc C).mk' (sortedTransferRVPositive H _) =
      (gammaGroundRVSpecialCongruence hc C).mk' (sortedTransferRVPositive H _)
    apply (gammaGroundRVSpecialCongruence hc C).eq.mpr
    rw [sortedTransferRVPositive_oneObject,
      (sortedTransferRVPositive (hc := hc) H).map_add,
      sortedTransferRVPositive_positiveObject,
      (sortedTransferRVPositive (hc := hc) H).map_one]
    exact RingConGen.Rel.of _ _ ⟨rfl,rfl⟩
  exact (gammaGroundRVSpecialCongruence hc C).eq.mp (hle h)

variable (K : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase C sn D → DefinableOverBase B sn D)

include H in
theorem sortedTransferRVPositive_special_iff (x y : GammaGroundRVPositiveSemiring hc C) :
    gammaGroundRVSpecialCongruence hc B (sortedTransferRVPositive K x) (sortedTransferRVPositive K y) ↔
      gammaGroundRVSpecialCongruence hc C x y := by
  constructor
  · intro h
    have he := sortedTransferRVPositive_special H h
    rw [sortedTransferRVPositive_left_inv K H,sortedTransferRVPositive_left_inv K H] at he
    exact he
  · exact sortedTransferRVPositive_special K

def sortedTransferOriginalLiftInput (I : OriginalBaseUnmeasuredLiftInput hc B) :
    OriginalBaseUnmeasuredLiftInput hc C where
  lift := (sortedTransferVFPositive (hc := hc) H).comp (I.lift.comp (sortedTransferRVPositive K))
  lift_class U := by
    change sortedTransferVFPositive H (I.lift (sortedTransferRVPositive K (gammaGroundRVSemiringClass U))) = _
    rw [sortedTransferRVPositive_class,I.lift_class]
    rw [← sortedTransferVFPositive_lift K U]
    exact sortedTransferVFPositive_left_inv K H _
  surjective := (sortedTransferVFPositiveEquiv H K).surjective.comp
    (I.surjective.comp (sortedTransferRVPositiveEquiv K H).surjective)
  kernel := by
    ext x y
    change gammaGroundRVSpecialCongruence hc C x y ↔
      sortedTransferVFPositive H (I.lift (sortedTransferRVPositive K x)) =
        sortedTransferVFPositive H (I.lift (sortedTransferRVPositive K y))
    have hinj : Function.Injective (sortedTransferVFPositive (hc := hc) H) := (sortedTransferVFPositiveEquiv H K).injective
    rw [hinj.eq_iff]
    rw [← show gammaGroundRVSpecialCongruence hc B (sortedTransferRVPositive K x) (sortedTransferRVPositive K y) ↔
      I.lift (sortedTransferRVPositive K x) = I.lift (sortedTransferRVPositive K y) by rw [I.kernel]; rfl]
    exact (sortedTransferRVPositive_special_iff H K x y).symm

end DiamondIntegral.Section5
