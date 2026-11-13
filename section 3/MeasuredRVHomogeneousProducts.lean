import «section 3».MeasuredRVProductScissors
import Mathlib.Algebra.GradedMonoid

/-! Graded multiplication on actual measured positive classes. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def measuredRVRepresentative {k : ℕ} (a : MeasuredRVKPlus (M := M) hc S k) : MeasuredRVObject (M := M) S k :=
  Classical.choose (measuredRVClass_surjective hc a)

@[simp] theorem measuredRVRepresentative_class {k : ℕ} (a : MeasuredRVKPlus (M := M) hc S k) :
    measuredRVClass hc (measuredRVRepresentative a) = a := Classical.choose_spec (measuredRVClass_surjective hc a)

def measuredRVClassMul {k l : ℕ} (a : MeasuredRVKPlus (M := M) hc S k) (b : MeasuredRVKPlus (M := M) hc S l) :
    MeasuredRVKPlus (M := M) hc S (k + l) :=
  measuredRVClass hc ((measuredRVRepresentative a).product hc (measuredRVRepresentative b))

@[simp] theorem measuredRVClassMul_class {k l : ℕ} (U : MeasuredRVObject (M := M) S k)
    (V : MeasuredRVObject (M := M) S l) :
    measuredRVClassMul (measuredRVClass hc U) (measuredRVClass hc V) = measuredRVClass hc (U.product hc V) := by
  obtain ⟨e⟩ := measuredRVClass_eq_iff_iso.mp (measuredRVRepresentative_class (measuredRVClass hc U))
  obtain ⟨d⟩ := measuredRVClass_eq_iff_iso.mp (measuredRVRepresentative_class (measuredRVClass hc V))
  exact measuredRVClass_iso hc (asIso (show _ ⟶ _ from measuredRVProductHom hc e.hom d.hom))

def measuredRVKPlusCast {k l : ℕ} (h : k = l) (a : MeasuredRVKPlus (M := M) hc S k) : MeasuredRVKPlus (M := M) hc S l := h ▸ a

theorem measuredRVKPlusCast_add {k l : ℕ} (h : k = l) (a b : MeasuredRVKPlus (M := M) hc S k) :
    measuredRVKPlusCast h (a + b) = measuredRVKPlusCast h a + measuredRVKPlusCast h b := by
  cases h
  rfl

theorem measuredRVClass_cast_reindex {k l : ℕ} (h : k = l)
    (U : MeasuredRVObject (M := M) S k) (e : Fin l ≃ Fin k) :
    measuredRVKPlusCast h (measuredRVClass hc U) = measuredRVClass hc (U.reindexVolume e) := by
  cases h
  exact measuredRVClass_iso hc (asIso (show U ⟶ U.reindexVolume e from
    ⟨DefinableBijection.id _, fun a => (U.reindex_combinedWeight e a).symm⟩))

theorem measuredRVClassMul_comm_cast {k l : ℕ} (a : MeasuredRVKPlus (M := M) hc S k) (b : MeasuredRVKPlus (M := M) hc S l) :
    measuredRVKPlusCast (Nat.add_comm l k) (measuredRVClassMul b a) = measuredRVClassMul a b := by
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
  obtain ⟨V, rfl⟩ := measuredRVClass_surjective hc b
  rw [measuredRVClassMul_class, measuredRVClassMul_class]
  exact (measuredRVClass_cast_reindex (Nat.add_comm l k) (V.product hc U) finAddFlip).trans
    (measuredRVClass_iso hc (asIso (show _ ⟶ _ from measuredRVProductCommHom hc U V))).symm

theorem measuredRVClass_heq_of_reindexedIso {k l : ℕ} (h : k = l)
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l)
    (e : Fin k ≃ Fin l) (hi : U ≅ V.reindexVolume e) : HEq (measuredRVClass hc U) (measuredRVClass hc V) := by
  have hcast : (h.symm ▸ measuredRVClass hc V) = measuredRVClass hc U :=
    (measuredRVClass_cast_reindex h.symm V e).trans (measuredRVClass_iso hc hi).symm
  have hh : HEq (h.symm ▸ measuredRVClass hc V) (measuredRVClass hc V) := by cases h; rfl
  exact (heq_of_eq hcast.symm).trans hh

instance measuredRVKPlusGMul : GradedMonoid.GMul (MeasuredRVKPlus (M := M) hc S) := ⟨measuredRVClassMul⟩

instance measuredRVKPlusGOne : GradedMonoid.GOne (MeasuredRVKPlus (M := M) hc S) := ⟨measuredRVClass hc (MeasuredRVObject.unit hc S)⟩

theorem measuredRVHomogeneous_mul_comm (a b : GradedMonoid (MeasuredRVKPlus (M := M) hc S)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
  obtain ⟨V, rfl⟩ := measuredRVClass_surjective hc b
  change (⟨k + l, measuredRVClassMul (measuredRVClass hc U) (measuredRVClass hc V)⟩ : GradedMonoid (MeasuredRVKPlus hc S)) =
    ⟨l + k, measuredRVClassMul (measuredRVClass hc V) (measuredRVClass hc U)⟩
  rw [measuredRVClassMul_class, measuredRVClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (measuredRVClass_heq_of_reindexedIso (Nat.add_comm k l) _ _ finAddFlip (asIso (show _ ⟶ _ from measuredRVProductCommHom hc U V)))

theorem measuredRVHomogeneous_mul_one (a : GradedMonoid (MeasuredRVKPlus (M := M) hc S)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
  change (⟨k + 0, measuredRVClassMul (measuredRVClass hc U) (measuredRVClass hc (MeasuredRVObject.unit hc S))⟩ :
    GradedMonoid (MeasuredRVKPlus hc S)) = ⟨k, measuredRVClass hc U⟩
  rw [measuredRVClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (measuredRVClass_iso hc (asIso (show _ ⟶ _ from measuredRVProductRightUnitHom hc U))))

theorem measuredRVHomogeneous_mul_assoc (a b c : GradedMonoid (MeasuredRVKPlus (M := M) hc S)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
  obtain ⟨V, rfl⟩ := measuredRVClass_surjective hc b
  obtain ⟨W, rfl⟩ := measuredRVClass_surjective hc c
  change (⟨(k + l) + j, measuredRVClassMul (measuredRVClassMul (measuredRVClass hc U) (measuredRVClass hc V)) (measuredRVClass hc W)⟩ :
    GradedMonoid (MeasuredRVKPlus hc S)) =
      ⟨k + (l + j), measuredRVClassMul (measuredRVClass hc U) (measuredRVClassMul (measuredRVClass hc V) (measuredRVClass hc W))⟩
  rw [measuredRVClassMul_class, measuredRVClassMul_class, measuredRVClassMul_class, measuredRVClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (measuredRVClass_heq_of_reindexedIso (Nat.add_assoc k l j) _ _ (finCongr (Nat.add_assoc k l j))
      (asIso (show _ ⟶ _ from measuredRVProductAssocHom hc U V W)))

instance measuredRVKPlusGCommMonoid : GradedMonoid.GCommMonoid (MeasuredRVKPlus (M := M) hc S) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [measuredRVHomogeneous_mul_comm, measuredRVHomogeneous_mul_one]
  mul_one := measuredRVHomogeneous_mul_one
  mul_assoc := measuredRVHomogeneous_mul_assoc
  mul_comm := measuredRVHomogeneous_mul_comm

theorem measuredRVClassMul_zero {k l : ℕ} (a : MeasuredRVKPlus (M := M) hc S k) :
    measuredRVClassMul a (0 : MeasuredRVKPlus hc S l) = 0 := by
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
  rw [← measuredRVClass_empty hc (M := M) (S := S) (k := l), measuredRVClassMul_class]
  let f : MeasuredRVHom (U.product hc (MeasuredRVObject.empty S l)) (MeasuredRVObject.empty S (k + l)) := {
    bijection := DefinableBijection.ofEmpty (by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨a, _⟩
      exact a.property.2) rfl
    preserves := fun a => False.elim (by obtain ⟨p, _⟩ := a.property; exact p.property.2) }
  exact (measuredRVClass_iso hc (asIso (show _ ⟶ _ from f))).trans (measuredRVClass_empty hc)

theorem measuredRVKPlusCast_zero {k l : ℕ} (h : k = l) :
    measuredRVKPlusCast h (0 : MeasuredRVKPlus (M := M) hc S k) = 0 := by
  cases h
  rfl

theorem measuredRVClassMul_zero_left {k l : ℕ} (b : MeasuredRVKPlus (M := M) hc S l) :
    measuredRVClassMul (0 : MeasuredRVKPlus hc S k) b = 0 := by
  rw [← measuredRVClassMul_comm_cast, measuredRVClassMul_zero]
  exact measuredRVKPlusCast_zero _

theorem measuredRVClassMul_add {k l : ℕ} (a : MeasuredRVKPlus (M := M) hc S k)
    (b c : MeasuredRVKPlus hc S l) :
    measuredRVClassMul a (b + c) = measuredRVClassMul a b + measuredRVClassMul a c := by
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
  obtain ⟨V, rfl⟩ := measuredRVClass_surjective hc b
  obtain ⟨W, rfl⟩ := measuredRVClass_surjective hc c
  rw [← measuredRVClass_coprod hc V W, measuredRVClassMul_class,
    measuredRVClassMul_class, measuredRVClassMul_class]
  exact measuredRVClass_product_coprod hc U V W

theorem measuredRVClassMul_add_left {k l : ℕ} (a b : MeasuredRVKPlus (M := M) hc S k)
    (c : MeasuredRVKPlus hc S l) :
    measuredRVClassMul (a + b) c = measuredRVClassMul a c + measuredRVClassMul b c := by
  rw [← measuredRVClassMul_comm_cast (a + b) c, measuredRVClassMul_add, measuredRVKPlusCast_add,
    measuredRVClassMul_comm_cast, measuredRVClassMul_comm_cast]

end DiamondIntegral.Section3
