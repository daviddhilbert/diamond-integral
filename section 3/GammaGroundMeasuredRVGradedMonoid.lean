import «section 3».GammaGroundMeasuredRVHomogeneousProducts
import «section 3».GammaGroundMeasuredRVProductLaws
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

def gammaGroundMeasuredRVKPlusCast {k l : ℕ} (h : k = l) (a : GammaGroundMeasuredRVKPlus hc ground k) : GammaGroundMeasuredRVKPlus hc ground l := h ▸ a

theorem gammaGroundMeasuredRVKPlusCast_add {k l : ℕ} (h : k = l) (a b : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVKPlusCast h (a + b) = gammaGroundMeasuredRVKPlusCast h a + gammaGroundMeasuredRVKPlusCast h b := by
  cases h
  rfl

theorem gammaGroundMeasuredRVClass_cast_reindex {k l : ℕ} (h : k = l)
    (U : GammaGroundMeasuredRVObject hc ground k) (e : Fin l ≃ Fin k) :
    gammaGroundMeasuredRVKPlusCast h (gammaGroundMeasuredRVClass U) = gammaGroundMeasuredRVClass (U.reindexVolume e) := by
  cases h
  exact gammaGroundMeasuredRVClass_iso (asIso (show U ⟶ U.reindexVolume e from ⟨GammaGroundBijection.id U.underlying.domain, fun a => (U.reindex_combinedWeight e a).symm⟩))

theorem gammaGroundMeasuredRVClassMul_comm_cast {k l : ℕ} (a : GammaGroundMeasuredRVKPlus hc ground k) (b : GammaGroundMeasuredRVKPlus hc ground l) :
    gammaGroundMeasuredRVKPlusCast (Nat.add_comm l k) (gammaGroundMeasuredRVClassMul b a) = gammaGroundMeasuredRVClassMul a b := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredRVClass_surjective b
  rw [gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVClassMul_class]
  exact (gammaGroundMeasuredRVClass_cast_reindex (Nat.add_comm l k) (V.product U) finAddFlip).trans
    (gammaGroundMeasuredRVClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredRVProductCommHom U V))).symm

theorem gammaGroundMeasuredRVClass_heq_of_reindexedIso {k l : ℕ} (h : k = l)
    (U : GammaGroundMeasuredRVObject hc ground k) (V : GammaGroundMeasuredRVObject hc ground l)
    (e : Fin k ≃ Fin l) (hi : U ≅ V.reindexVolume e) : HEq (gammaGroundMeasuredRVClass U) (gammaGroundMeasuredRVClass V) := by
  have hcast : (h.symm ▸ gammaGroundMeasuredRVClass V) = gammaGroundMeasuredRVClass U :=
    (gammaGroundMeasuredRVClass_cast_reindex h.symm V e).trans (gammaGroundMeasuredRVClass_iso hi).symm
  have hh : HEq (h.symm ▸ gammaGroundMeasuredRVClass V) (gammaGroundMeasuredRVClass V) := by cases h; rfl
  exact (heq_of_eq hcast.symm).trans hh

instance gammaGroundMeasuredRVKPlusGMul : GradedMonoid.GMul (GammaGroundMeasuredRVKPlus hc ground) := ⟨gammaGroundMeasuredRVClassMul⟩

instance gammaGroundMeasuredRVKPlusGOne : GradedMonoid.GOne (GammaGroundMeasuredRVKPlus hc ground) := ⟨gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.unit hc ground)⟩

theorem gammaGroundMeasuredRVHomogeneous_mul_comm (a b : GradedMonoid (GammaGroundMeasuredRVKPlus hc ground)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredRVClass_surjective b
  change (⟨k + l, gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass U) (gammaGroundMeasuredRVClass V)⟩ : GradedMonoid (GammaGroundMeasuredRVKPlus hc ground)) =
    ⟨l + k, gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass V) (gammaGroundMeasuredRVClass U)⟩
  rw [gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (gammaGroundMeasuredRVClass_heq_of_reindexedIso (Nat.add_comm k l) _ _ finAddFlip (asIso (show _ ⟶ _ from gammaGroundMeasuredRVProductCommHom U V)))

theorem gammaGroundMeasuredRVHomogeneous_mul_one (a : GradedMonoid (GammaGroundMeasuredRVKPlus hc ground)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  change (⟨k + 0, gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass U) (gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.unit hc ground))⟩ :
    GradedMonoid (GammaGroundMeasuredRVKPlus hc ground)) = ⟨k, gammaGroundMeasuredRVClass U⟩
  rw [gammaGroundMeasuredRVClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (gammaGroundMeasuredRVClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredRVProductRightUnitHom U))))

theorem gammaGroundMeasuredRVHomogeneous_mul_assoc (a b c : GradedMonoid (GammaGroundMeasuredRVKPlus hc ground)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredRVClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundMeasuredRVClass_surjective c
  change (⟨(k + l) + j, gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass U) (gammaGroundMeasuredRVClass V)) (gammaGroundMeasuredRVClass W)⟩ :
    GradedMonoid (GammaGroundMeasuredRVKPlus hc ground)) =
      ⟨k + (l + j), gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass U) (gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass V) (gammaGroundMeasuredRVClass W))⟩
  rw [gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (gammaGroundMeasuredRVClass_heq_of_reindexedIso (Nat.add_assoc k l j) _ _ (finCongr (Nat.add_assoc k l j))
      (asIso (show _ ⟶ _ from gammaGroundMeasuredRVProductAssocHom U V W)))

instance gammaGroundMeasuredRVKPlusGCommMonoid : GradedMonoid.GCommMonoid (GammaGroundMeasuredRVKPlus hc ground) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [gammaGroundMeasuredRVHomogeneous_mul_comm, gammaGroundMeasuredRVHomogeneous_mul_one]
  mul_one := gammaGroundMeasuredRVHomogeneous_mul_one
  mul_assoc := gammaGroundMeasuredRVHomogeneous_mul_assoc
  mul_comm := gammaGroundMeasuredRVHomogeneous_mul_comm

end DiamondIntegral.Section3
