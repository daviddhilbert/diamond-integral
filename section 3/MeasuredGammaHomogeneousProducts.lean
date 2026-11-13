import «section 3».MeasuredGammaProductDistributivity
import Mathlib.Algebra.GradedMonoid

/-! Graded multiplication on actual Gamma positive classes. -/
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

def measuredGammaRepresentative {k : ℕ} (a : MeasuredGammaKPlus (M := M) hc S k) : MeasuredGammaObject (M := M) hc S k :=
  Classical.choose (measuredGammaClass_surjective a)

@[simp] theorem measuredGammaRepresentative_class {k : ℕ} (a : MeasuredGammaKPlus (M := M) hc S k) :
    measuredGammaClass (measuredGammaRepresentative a) = a := Classical.choose_spec (measuredGammaClass_surjective a)

def measuredGammaClassMul {k l : ℕ} (a : MeasuredGammaKPlus (M := M) hc S k) (b : MeasuredGammaKPlus (M := M) hc S l) :
    MeasuredGammaKPlus (M := M) hc S (k + l) :=
  measuredGammaClass ((measuredGammaRepresentative a).product (measuredGammaRepresentative b))

@[simp] theorem measuredGammaClassMul_class {k l : ℕ} (U : MeasuredGammaObject (M := M) hc S k)
    (V : MeasuredGammaObject (M := M) hc S l) :
    measuredGammaClassMul (measuredGammaClass U) (measuredGammaClass V) = measuredGammaClass (U.product V) := by
  obtain ⟨e⟩ := measuredGammaClass_eq_iff_iso.mp (measuredGammaRepresentative_class (measuredGammaClass U))
  obtain ⟨d⟩ := measuredGammaClass_eq_iff_iso.mp (measuredGammaRepresentative_class (measuredGammaClass V))
  exact measuredGammaClass_iso (asIso (show _ ⟶ _ from MeasuredGammaHom.product e.hom d.hom))

theorem measuredGammaClassMul_comm_cast {k l : ℕ} (a : MeasuredGammaKPlus (M := M) hc S k) (b : MeasuredGammaKPlus hc S l) :
    measuredGammaKPlusCast (Nat.add_comm l k) (measuredGammaClassMul b a) = measuredGammaClassMul a b := by
  obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := measuredGammaClass_surjective b
  rw [measuredGammaClassMul_class, measuredGammaClassMul_class]
  exact (measuredGammaClass_cast (Nat.add_comm l k) (V.product U)).trans
    (measuredGammaClass_iso (asIso (show _ ⟶ _ from measuredGammaProductCommHom U V))).symm

instance measuredGammaKPlusGMul : GradedMonoid.GMul (MeasuredGammaKPlus (M := M) hc S) := ⟨measuredGammaClassMul⟩

instance measuredGammaKPlusGOne : GradedMonoid.GOne (MeasuredGammaKPlus (M := M) hc S) := ⟨measuredGammaClass (MeasuredGammaObject.unit hc S)⟩

theorem measuredGammaHomogeneous_mul_comm (a b : GradedMonoid (MeasuredGammaKPlus (M := M) hc S)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := measuredGammaClass_surjective b
  change (⟨k + l, measuredGammaClassMul (measuredGammaClass U) (measuredGammaClass V)⟩ : GradedMonoid (MeasuredGammaKPlus hc S)) =
    ⟨l + k, measuredGammaClassMul (measuredGammaClass V) (measuredGammaClass U)⟩
  rw [measuredGammaClassMul_class, measuredGammaClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (measuredGammaClass_heq_of_castHom (Nat.add_comm k l) _ _ (measuredGammaProductCommHom U V))

theorem measuredGammaHomogeneous_mul_one (a : GradedMonoid (MeasuredGammaKPlus (M := M) hc S)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
  change (⟨k + 0, measuredGammaClassMul (measuredGammaClass U) (measuredGammaClass (MeasuredGammaObject.unit hc S))⟩ :
    GradedMonoid (MeasuredGammaKPlus hc S)) = ⟨k, measuredGammaClass U⟩
  rw [measuredGammaClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (measuredGammaClass_iso (asIso (show _ ⟶ _ from measuredGammaProductRightUnitHom U))))

theorem measuredGammaHomogeneous_mul_assoc (a b c : GradedMonoid (MeasuredGammaKPlus (M := M) hc S)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := measuredGammaClass_surjective b
  obtain ⟨W, rfl⟩ := measuredGammaClass_surjective c
  change (⟨(k + l) + j, measuredGammaClassMul (measuredGammaClassMul (measuredGammaClass U) (measuredGammaClass V)) (measuredGammaClass W)⟩ :
    GradedMonoid (MeasuredGammaKPlus hc S)) =
      ⟨k + (l + j), measuredGammaClassMul (measuredGammaClass U) (measuredGammaClassMul (measuredGammaClass V) (measuredGammaClass W))⟩
  rw [measuredGammaClassMul_class, measuredGammaClassMul_class, measuredGammaClassMul_class, measuredGammaClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (measuredGammaClass_heq_of_castHom (Nat.add_assoc k l j) _ _ (measuredGammaProductAssocHom U V W))

instance measuredGammaKPlusGCommMonoid : GradedMonoid.GCommMonoid (MeasuredGammaKPlus (M := M) hc S) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [measuredGammaHomogeneous_mul_comm, measuredGammaHomogeneous_mul_one]
  mul_one := measuredGammaHomogeneous_mul_one
  mul_assoc := measuredGammaHomogeneous_mul_assoc
  mul_comm := measuredGammaHomogeneous_mul_comm

theorem measuredGammaClassMul_zero {k l : ℕ} (a : MeasuredGammaKPlus (M := M) hc S k) :
    measuredGammaClassMul a (0 : MeasuredGammaKPlus hc S l) = 0 := by
  obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
  rw [← measuredGammaClass_empty (M := M) (hc := hc) (S := S) (k := l), measuredGammaClassMul_class]
  exact (measuredGammaClass_iso (measuredGammaProductEmptyIso U l)).trans measuredGammaClass_empty

theorem measuredGammaClassMul_zero_left {k l : ℕ} (b : MeasuredGammaKPlus (M := M) hc S l) :
    measuredGammaClassMul (0 : MeasuredGammaKPlus hc S k) b = 0 := by
  obtain ⟨V, rfl⟩ := measuredGammaClass_surjective b
  rw [← measuredGammaClass_empty (M := M) (hc := hc) (S := S) (k := k), measuredGammaClassMul_class]
  exact (measuredGammaClass_iso (measuredGammaEmptyProductIso V k)).trans measuredGammaClass_empty

theorem measuredGammaClassMul_add {k l : ℕ} (a : MeasuredGammaKPlus (M := M) hc S k)
    (b c : MeasuredGammaKPlus hc S l) :
    measuredGammaClassMul a (b + c) = measuredGammaClassMul a b + measuredGammaClassMul a c := by
  obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := measuredGammaClass_surjective b
  obtain ⟨W, rfl⟩ := measuredGammaClass_surjective c
  rw [← measuredGammaClass_coprod V W, measuredGammaClassMul_class,
    measuredGammaClassMul_class, measuredGammaClassMul_class]
  exact measuredGammaClass_product_coprod U V W

theorem measuredGammaClassMul_add_left {k l : ℕ} (a b : MeasuredGammaKPlus (M := M) hc S k)
    (c : MeasuredGammaKPlus hc S l) :
    measuredGammaClassMul (a + b) c = measuredGammaClassMul a c + measuredGammaClassMul b c := by
  rw [← measuredGammaClassMul_comm_cast (a + b) c, measuredGammaClassMul_add, measuredGammaKPlusCast_add,
    measuredGammaClassMul_comm_cast, measuredGammaClassMul_comm_cast]

end DiamondIntegral.Section3
