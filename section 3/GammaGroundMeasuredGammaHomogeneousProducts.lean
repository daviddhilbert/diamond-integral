import Mathlib.Algebra.GradedMonoid
import «section 3».GammaGroundMeasuredGammaProductDistributivity
/-! Graded multiplication on actual Gamma positive classes. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def gammaGroundMeasuredGammaRepresentative {k : ℕ} (a : GammaGroundMeasuredGammaKPlus (M := M) hc ground k) : GammaGroundMeasuredGammaObject (M := M) hc ground k :=
  Classical.choose (gammaGroundMeasuredGammaClass_surjective a)

@[simp] theorem gammaGroundMeasuredGammaRepresentative_class {k : ℕ} (a : GammaGroundMeasuredGammaKPlus (M := M) hc ground k) :
    gammaGroundMeasuredGammaClass (gammaGroundMeasuredGammaRepresentative a) = a := Classical.choose_spec (gammaGroundMeasuredGammaClass_surjective a)

def gammaGroundMeasuredGammaClassMul {k l : ℕ} (a : GammaGroundMeasuredGammaKPlus (M := M) hc ground k) (b : GammaGroundMeasuredGammaKPlus (M := M) hc ground l) :
    GammaGroundMeasuredGammaKPlus (M := M) hc ground (k + l) :=
  gammaGroundMeasuredGammaClass ((gammaGroundMeasuredGammaRepresentative a).product (gammaGroundMeasuredGammaRepresentative b))

@[simp] theorem gammaGroundMeasuredGammaClassMul_class {k l : ℕ} (U : GammaGroundMeasuredGammaObject (M := M) hc ground k)
    (V : GammaGroundMeasuredGammaObject (M := M) hc ground l) :
    gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass U) (gammaGroundMeasuredGammaClass V) = gammaGroundMeasuredGammaClass (U.product V) := by
  obtain ⟨e⟩ := gammaGroundMeasuredGammaClass_eq_iff_iso.mp (gammaGroundMeasuredGammaRepresentative_class (gammaGroundMeasuredGammaClass U))
  obtain ⟨d⟩ := gammaGroundMeasuredGammaClass_eq_iff_iso.mp (gammaGroundMeasuredGammaRepresentative_class (gammaGroundMeasuredGammaClass V))
  exact gammaGroundMeasuredGammaClass_iso (asIso (show _ ⟶ _ from GammaGroundMeasuredGammaHom.product e.hom d.hom))

theorem gammaGroundMeasuredGammaClassMul_comm_cast {k l : ℕ} (a : GammaGroundMeasuredGammaKPlus (M := M) hc ground k) (b : GammaGroundMeasuredGammaKPlus hc ground l) :
    gammaGroundMeasuredGammaKPlusCast (Nat.add_comm l k) (gammaGroundMeasuredGammaClassMul b a) = gammaGroundMeasuredGammaClassMul a b := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredGammaClass_surjective b
  rw [gammaGroundMeasuredGammaClassMul_class, gammaGroundMeasuredGammaClassMul_class]
  exact (gammaGroundMeasuredGammaClass_cast (Nat.add_comm l k) (V.product U)).trans
    (gammaGroundMeasuredGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaProductCommHom U V))).symm

instance gammaGroundMeasuredGammaKPlusGMul : GradedMonoid.GMul (GammaGroundMeasuredGammaKPlus (M := M) hc ground) := ⟨gammaGroundMeasuredGammaClassMul⟩

instance gammaGroundMeasuredGammaKPlusGOne : GradedMonoid.GOne (GammaGroundMeasuredGammaKPlus (M := M) hc ground) := ⟨gammaGroundMeasuredGammaClass (GammaGroundMeasuredGammaObject.unit hc ground)⟩

theorem gammaGroundMeasuredGammaHomogeneous_mul_comm (a b : GradedMonoid (GammaGroundMeasuredGammaKPlus (M := M) hc ground)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredGammaClass_surjective b
  change (⟨k + l, gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass U) (gammaGroundMeasuredGammaClass V)⟩ : GradedMonoid (GammaGroundMeasuredGammaKPlus hc ground)) =
    ⟨l + k, gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass V) (gammaGroundMeasuredGammaClass U)⟩
  rw [gammaGroundMeasuredGammaClassMul_class, gammaGroundMeasuredGammaClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (gammaGroundMeasuredGammaClass_heq_of_castHom (Nat.add_comm k l) _ _ (gammaGroundMeasuredGammaProductCommHom U V))

theorem gammaGroundMeasuredGammaHomogeneous_mul_one (a : GradedMonoid (GammaGroundMeasuredGammaKPlus (M := M) hc ground)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
  change (⟨k + 0, gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass U) (gammaGroundMeasuredGammaClass (GammaGroundMeasuredGammaObject.unit hc ground))⟩ :
    GradedMonoid (GammaGroundMeasuredGammaKPlus hc ground)) = ⟨k, gammaGroundMeasuredGammaClass U⟩
  rw [gammaGroundMeasuredGammaClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (gammaGroundMeasuredGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaProductRightUnitHom U))))

theorem gammaGroundMeasuredGammaHomogeneous_mul_assoc (a b c : GradedMonoid (GammaGroundMeasuredGammaKPlus (M := M) hc ground)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredGammaClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundMeasuredGammaClass_surjective c
  change (⟨(k + l) + j, gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass U) (gammaGroundMeasuredGammaClass V)) (gammaGroundMeasuredGammaClass W)⟩ :
    GradedMonoid (GammaGroundMeasuredGammaKPlus hc ground)) =
      ⟨k + (l + j), gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass U) (gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass V) (gammaGroundMeasuredGammaClass W))⟩
  rw [gammaGroundMeasuredGammaClassMul_class, gammaGroundMeasuredGammaClassMul_class, gammaGroundMeasuredGammaClassMul_class, gammaGroundMeasuredGammaClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (gammaGroundMeasuredGammaClass_heq_of_castHom (Nat.add_assoc k l j) _ _ (gammaGroundMeasuredGammaProductAssocHom U V W))

instance gammaGroundMeasuredGammaKPlusGCommMonoid : GradedMonoid.GCommMonoid (GammaGroundMeasuredGammaKPlus (M := M) hc ground) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [gammaGroundMeasuredGammaHomogeneous_mul_comm, gammaGroundMeasuredGammaHomogeneous_mul_one]
  mul_one := gammaGroundMeasuredGammaHomogeneous_mul_one
  mul_assoc := gammaGroundMeasuredGammaHomogeneous_mul_assoc
  mul_comm := gammaGroundMeasuredGammaHomogeneous_mul_comm

theorem gammaGroundMeasuredGammaClassMul_zero {k l : ℕ} (a : GammaGroundMeasuredGammaKPlus (M := M) hc ground k) :
    gammaGroundMeasuredGammaClassMul a (0 : GammaGroundMeasuredGammaKPlus hc ground l) = 0 := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
  rw [← gammaGroundMeasuredGammaClass_empty (M := M) (hc := hc) (ground := ground) (k := l), gammaGroundMeasuredGammaClassMul_class]
  exact (gammaGroundMeasuredGammaClass_iso (gammaGroundMeasuredGammaProductEmptyIso U l)).trans gammaGroundMeasuredGammaClass_empty

theorem gammaGroundMeasuredGammaClassMul_zero_left {k l : ℕ} (b : GammaGroundMeasuredGammaKPlus (M := M) hc ground l) :
    gammaGroundMeasuredGammaClassMul (0 : GammaGroundMeasuredGammaKPlus hc ground k) b = 0 := by
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredGammaClass_surjective b
  rw [← gammaGroundMeasuredGammaClass_empty (M := M) (hc := hc) (ground := ground) (k := k), gammaGroundMeasuredGammaClassMul_class]
  exact (gammaGroundMeasuredGammaClass_iso (gammaGroundMeasuredGammaEmptyProductIso V k)).trans gammaGroundMeasuredGammaClass_empty

theorem gammaGroundMeasuredGammaClassMul_add {k l : ℕ} (a : GammaGroundMeasuredGammaKPlus (M := M) hc ground k)
    (b c : GammaGroundMeasuredGammaKPlus hc ground l) :
    gammaGroundMeasuredGammaClassMul a (b + c) = gammaGroundMeasuredGammaClassMul a b + gammaGroundMeasuredGammaClassMul a c := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredGammaClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundMeasuredGammaClass_surjective c
  rw [← gammaGroundMeasuredGammaClass_coprod V W, gammaGroundMeasuredGammaClassMul_class,
    gammaGroundMeasuredGammaClassMul_class, gammaGroundMeasuredGammaClassMul_class]
  exact gammaGroundMeasuredGammaClass_product_coprod U V W

theorem gammaGroundMeasuredGammaClassMul_add_left {k l : ℕ} (a b : GammaGroundMeasuredGammaKPlus (M := M) hc ground k)
    (c : GammaGroundMeasuredGammaKPlus hc ground l) :
    gammaGroundMeasuredGammaClassMul (a + b) c = gammaGroundMeasuredGammaClassMul a c + gammaGroundMeasuredGammaClassMul b c := by
  rw [← gammaGroundMeasuredGammaClassMul_comm_cast (a + b) c, gammaGroundMeasuredGammaClassMul_add, gammaGroundMeasuredGammaKPlusCast_add,
    gammaGroundMeasuredGammaClassMul_comm_cast, gammaGroundMeasuredGammaClassMul_comm_cast]

end DiamondIntegral.Section3
