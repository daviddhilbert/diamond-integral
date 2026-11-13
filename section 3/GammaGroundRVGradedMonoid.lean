import «section 3».GammaGroundRVHomogeneousProducts
import «section 3».GammaGroundRVProductLaws
import Mathlib.Algebra.GradedMonoid

/-! The homogeneous RV products satisfy the actual graded monoid laws
at the complete Gamma ground. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundRVKPlusCast {k l : ℕ} (h : k = l) (a : GammaGroundRVKPlus hc ground k) : GammaGroundRVKPlus hc ground l := h ▸ a

theorem gammaGroundRVKPlusCast_add {k l : ℕ} (h : k = l) (a b : GammaGroundRVKPlus hc ground k) :
    gammaGroundRVKPlusCast h (a + b) = gammaGroundRVKPlusCast h a + gammaGroundRVKPlusCast h b := by
  cases h
  rfl

theorem gammaGroundRVClass_cast_reindex {k l : ℕ} (h : k = l)
    (U : GammaGroundRVObject hc ground k) (e : Fin l ≃ Fin k) :
    gammaGroundRVKPlusCast h (gammaGroundRVClass U) = gammaGroundRVClass (U.reindexVolume e) := by
  cases h
  exact gammaGroundRVClass_iso (asIso (show U ⟶ U.reindexVolume e from GammaGroundBijection.id U.domain))

theorem gammaGroundRVClassMul_comm_cast {k l : ℕ} (a : GammaGroundRVKPlus hc ground k) (b : GammaGroundRVKPlus hc ground l) :
    gammaGroundRVKPlusCast (Nat.add_comm l k) (gammaGroundRVClassMul b a) = gammaGroundRVClassMul a b := by
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundRVClass_surjective b
  rw [gammaGroundRVClassMul_class, gammaGroundRVClassMul_class]
  exact (gammaGroundRVClass_cast_reindex (Nat.add_comm l k) (V.product U) finAddFlip).trans
    (gammaGroundRVClass_iso (asIso (show _ ⟶ _ from gammaGroundRVProductCommBijection U V))).symm

theorem gammaGroundRVClass_heq_of_reindexedIso {k l : ℕ} (h : k = l)
    (U : GammaGroundRVObject hc ground k) (V : GammaGroundRVObject hc ground l)
    (e : Fin k ≃ Fin l) (hi : U ≅ V.reindexVolume e) : HEq (gammaGroundRVClass U) (gammaGroundRVClass V) := by
  have hcast : (h.symm ▸ gammaGroundRVClass V) = gammaGroundRVClass U :=
    (gammaGroundRVClass_cast_reindex h.symm V e).trans (gammaGroundRVClass_iso hi).symm
  have hh : HEq (h.symm ▸ gammaGroundRVClass V) (gammaGroundRVClass V) := by cases h; rfl
  exact (heq_of_eq hcast.symm).trans hh

instance gammaGroundRVKPlusGMul : GradedMonoid.GMul (GammaGroundRVKPlus hc ground) := ⟨gammaGroundRVClassMul⟩

instance gammaGroundRVKPlusGOne : GradedMonoid.GOne (GammaGroundRVKPlus hc ground) := ⟨gammaGroundRVClass (GammaGroundRVObject.unit hc ground)⟩

theorem gammaGroundRVHomogeneous_mul_comm (a b : GradedMonoid (GammaGroundRVKPlus hc ground)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundRVClass_surjective b
  change (⟨k + l, gammaGroundRVClassMul (gammaGroundRVClass U) (gammaGroundRVClass V)⟩ : GradedMonoid (GammaGroundRVKPlus hc ground)) =
    ⟨l + k, gammaGroundRVClassMul (gammaGroundRVClass V) (gammaGroundRVClass U)⟩
  rw [gammaGroundRVClassMul_class, gammaGroundRVClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (gammaGroundRVClass_heq_of_reindexedIso (Nat.add_comm k l) _ _ finAddFlip (asIso (show _ ⟶ _ from gammaGroundRVProductCommBijection U V)))

theorem gammaGroundRVHomogeneous_mul_one (a : GradedMonoid (GammaGroundRVKPlus hc ground)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  change (⟨k + 0, gammaGroundRVClassMul (gammaGroundRVClass U) (gammaGroundRVClass (GammaGroundRVObject.unit hc ground))⟩ :
    GradedMonoid (GammaGroundRVKPlus hc ground)) = ⟨k, gammaGroundRVClass U⟩
  rw [gammaGroundRVClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (gammaGroundRVClass_iso (asIso (show _ ⟶ _ from gammaGroundRVProductRightUnitBijection U))))

theorem gammaGroundRVHomogeneous_mul_assoc (a b c : GradedMonoid (GammaGroundRVKPlus hc ground)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundRVClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundRVClass_surjective c
  change (⟨(k + l) + j, gammaGroundRVClassMul (gammaGroundRVClassMul (gammaGroundRVClass U) (gammaGroundRVClass V)) (gammaGroundRVClass W)⟩ :
    GradedMonoid (GammaGroundRVKPlus hc ground)) =
      ⟨k + (l + j), gammaGroundRVClassMul (gammaGroundRVClass U) (gammaGroundRVClassMul (gammaGroundRVClass V) (gammaGroundRVClass W))⟩
  rw [gammaGroundRVClassMul_class, gammaGroundRVClassMul_class, gammaGroundRVClassMul_class, gammaGroundRVClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (gammaGroundRVClass_heq_of_reindexedIso (Nat.add_assoc k l j) _ _ (finCongr (Nat.add_assoc k l j))
      (asIso (show _ ⟶ _ from gammaGroundRVProductAssocBijection U V W)))

instance gammaGroundRVKPlusGCommMonoid : GradedMonoid.GCommMonoid (GammaGroundRVKPlus hc ground) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [gammaGroundRVHomogeneous_mul_comm, gammaGroundRVHomogeneous_mul_one]
  mul_one := gammaGroundRVHomogeneous_mul_one
  mul_assoc := gammaGroundRVHomogeneous_mul_assoc
  mul_comm := gammaGroundRVHomogeneous_mul_comm

end DiamondIntegral.Section3
