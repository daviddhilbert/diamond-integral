import «section 3».GammaProductDistributivity
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

def gammaRepresentative {k : ℕ} (a : GammaKPlus (M := M) hc S k) : GammaObject (M := M) hc S k :=
  Classical.choose (gammaClass_surjective a)

@[simp] theorem gammaRepresentative_class {k : ℕ} (a : GammaKPlus (M := M) hc S k) :
    gammaClass (gammaRepresentative a) = a := Classical.choose_spec (gammaClass_surjective a)

def gammaClassMul {k l : ℕ} (a : GammaKPlus (M := M) hc S k) (b : GammaKPlus (M := M) hc S l) :
    GammaKPlus (M := M) hc S (k + l) :=
  gammaClass ((gammaRepresentative a).product (gammaRepresentative b))

@[simp] theorem gammaClassMul_class {k l : ℕ} (U : GammaObject (M := M) hc S k)
    (V : GammaObject (M := M) hc S l) :
    gammaClassMul (gammaClass U) (gammaClass V) = gammaClass (U.product V) := by
  obtain ⟨e⟩ := gammaClass_eq_iff_iso.mp (gammaRepresentative_class (gammaClass U))
  obtain ⟨d⟩ := gammaClass_eq_iff_iso.mp (gammaRepresentative_class (gammaClass V))
  exact gammaClass_iso (asIso (show _ ⟶ _ from GammaHom.product e.hom d.hom))

theorem gammaClassMul_comm_cast {k l : ℕ} (a : GammaKPlus (M := M) hc S k) (b : GammaKPlus hc S l) :
    gammaKPlusCast (Nat.add_comm l k) (gammaClassMul b a) = gammaClassMul a b := by
  obtain ⟨U, rfl⟩ := gammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaClass_surjective b
  rw [gammaClassMul_class, gammaClassMul_class]
  exact (gammaClass_cast (Nat.add_comm l k) (V.product U)).trans
    (gammaClass_iso (asIso (show _ ⟶ _ from gammaProductCommHom U V))).symm

instance gammaKPlusGMul : GradedMonoid.GMul (GammaKPlus (M := M) hc S) := ⟨gammaClassMul⟩

instance gammaKPlusGOne : GradedMonoid.GOne (GammaKPlus (M := M) hc S) := ⟨gammaClass (GammaObject.unit hc S)⟩

theorem gammaHomogeneous_mul_comm (a b : GradedMonoid (GammaKPlus (M := M) hc S)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := gammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaClass_surjective b
  change (⟨k + l, gammaClassMul (gammaClass U) (gammaClass V)⟩ : GradedMonoid (GammaKPlus hc S)) =
    ⟨l + k, gammaClassMul (gammaClass V) (gammaClass U)⟩
  rw [gammaClassMul_class, gammaClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (gammaClass_heq_of_castHom (Nat.add_comm k l) _ _ (gammaProductCommHom U V))

theorem gammaHomogeneous_mul_one (a : GradedMonoid (GammaKPlus (M := M) hc S)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := gammaClass_surjective a
  change (⟨k + 0, gammaClassMul (gammaClass U) (gammaClass (GammaObject.unit hc S))⟩ :
    GradedMonoid (GammaKPlus hc S)) = ⟨k, gammaClass U⟩
  rw [gammaClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (gammaClass_iso (asIso (show _ ⟶ _ from gammaProductRightUnitHom U))))

theorem gammaHomogeneous_mul_assoc (a b c : GradedMonoid (GammaKPlus (M := M) hc S)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := gammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaClass_surjective b
  obtain ⟨W, rfl⟩ := gammaClass_surjective c
  change (⟨(k + l) + j, gammaClassMul (gammaClassMul (gammaClass U) (gammaClass V)) (gammaClass W)⟩ :
    GradedMonoid (GammaKPlus hc S)) =
      ⟨k + (l + j), gammaClassMul (gammaClass U) (gammaClassMul (gammaClass V) (gammaClass W))⟩
  rw [gammaClassMul_class, gammaClassMul_class, gammaClassMul_class, gammaClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (gammaClass_heq_of_castHom (Nat.add_assoc k l j) _ _ (gammaProductAssocHom U V W))

instance gammaKPlusGCommMonoid : GradedMonoid.GCommMonoid (GammaKPlus (M := M) hc S) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [gammaHomogeneous_mul_comm, gammaHomogeneous_mul_one]
  mul_one := gammaHomogeneous_mul_one
  mul_assoc := gammaHomogeneous_mul_assoc
  mul_comm := gammaHomogeneous_mul_comm

theorem gammaClassMul_zero {k l : ℕ} (a : GammaKPlus (M := M) hc S k) :
    gammaClassMul a (0 : GammaKPlus hc S l) = 0 := by
  obtain ⟨U, rfl⟩ := gammaClass_surjective a
  rw [← gammaClass_empty (M := M) (hc := hc) (S := S) (k := l), gammaClassMul_class]
  exact (gammaClass_iso (gammaProductEmptyIso U l)).trans gammaClass_empty

theorem gammaClassMul_zero_left {k l : ℕ} (b : GammaKPlus (M := M) hc S l) :
    gammaClassMul (0 : GammaKPlus hc S k) b = 0 := by
  obtain ⟨V, rfl⟩ := gammaClass_surjective b
  rw [← gammaClass_empty (M := M) (hc := hc) (S := S) (k := k), gammaClassMul_class]
  exact (gammaClass_iso (gammaEmptyProductIso V k)).trans gammaClass_empty

theorem gammaClassMul_add {k l : ℕ} (a : GammaKPlus (M := M) hc S k)
    (b c : GammaKPlus hc S l) :
    gammaClassMul a (b + c) = gammaClassMul a b + gammaClassMul a c := by
  obtain ⟨U, rfl⟩ := gammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaClass_surjective b
  obtain ⟨W, rfl⟩ := gammaClass_surjective c
  rw [← gammaClass_coprod V W, gammaClassMul_class,
    gammaClassMul_class, gammaClassMul_class]
  exact gammaClass_product_coprod U V W

theorem gammaClassMul_add_left {k l : ℕ} (a b : GammaKPlus (M := M) hc S k)
    (c : GammaKPlus hc S l) :
    gammaClassMul (a + b) c = gammaClassMul a c + gammaClassMul b c := by
  rw [← gammaClassMul_comm_cast (a + b) c, gammaClassMul_add, gammaKPlusCast_add,
    gammaClassMul_comm_cast, gammaClassMul_comm_cast]

end DiamondIntegral.Section3
