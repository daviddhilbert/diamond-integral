import Mathlib.Algebra.GradedMonoid
import «section 3».GammaGroundGammaProductDistributivity
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

def gammaGroundGammaRepresentative {k : ℕ} (a : GammaGroundGammaKPlus (M := M) hc ground k) : GammaGroundGammaObject (M := M) hc ground k :=
  Classical.choose (gammaGroundGammaClass_surjective a)

@[simp] theorem gammaGroundGammaRepresentative_class {k : ℕ} (a : GammaGroundGammaKPlus (M := M) hc ground k) :
    gammaGroundGammaClass (gammaGroundGammaRepresentative a) = a := Classical.choose_spec (gammaGroundGammaClass_surjective a)

def gammaGroundGammaClassMul {k l : ℕ} (a : GammaGroundGammaKPlus (M := M) hc ground k) (b : GammaGroundGammaKPlus (M := M) hc ground l) :
    GammaGroundGammaKPlus (M := M) hc ground (k + l) :=
  gammaGroundGammaClass ((gammaGroundGammaRepresentative a).product (gammaGroundGammaRepresentative b))

@[simp] theorem gammaGroundGammaClassMul_class {k l : ℕ} (U : GammaGroundGammaObject (M := M) hc ground k)
    (V : GammaGroundGammaObject (M := M) hc ground l) :
    gammaGroundGammaClassMul (gammaGroundGammaClass U) (gammaGroundGammaClass V) = gammaGroundGammaClass (U.product V) := by
  obtain ⟨e⟩ := gammaGroundGammaClass_eq_iff_iso.mp (gammaGroundGammaRepresentative_class (gammaGroundGammaClass U))
  obtain ⟨d⟩ := gammaGroundGammaClass_eq_iff_iso.mp (gammaGroundGammaRepresentative_class (gammaGroundGammaClass V))
  exact gammaGroundGammaClass_iso (asIso (show _ ⟶ _ from GammaGroundGammaHom.product e.hom d.hom))

theorem gammaGroundGammaClassMul_comm_cast {k l : ℕ} (a : GammaGroundGammaKPlus (M := M) hc ground k) (b : GammaGroundGammaKPlus hc ground l) :
    gammaGroundGammaKPlusCast (Nat.add_comm l k) (gammaGroundGammaClassMul b a) = gammaGroundGammaClassMul a b := by
  obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundGammaClass_surjective b
  rw [gammaGroundGammaClassMul_class, gammaGroundGammaClassMul_class]
  exact (gammaGroundGammaClass_cast (Nat.add_comm l k) (V.product U)).trans
    (gammaGroundGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundGammaProductCommHom U V))).symm

instance gammaGroundGammaKPlusGMul : GradedMonoid.GMul (GammaGroundGammaKPlus (M := M) hc ground) := ⟨gammaGroundGammaClassMul⟩

instance gammaGroundGammaKPlusGOne : GradedMonoid.GOne (GammaGroundGammaKPlus (M := M) hc ground) := ⟨gammaGroundGammaClass (GammaGroundGammaObject.unit hc ground)⟩

theorem gammaGroundGammaHomogeneous_mul_comm (a b : GradedMonoid (GammaGroundGammaKPlus (M := M) hc ground)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundGammaClass_surjective b
  change (⟨k + l, gammaGroundGammaClassMul (gammaGroundGammaClass U) (gammaGroundGammaClass V)⟩ : GradedMonoid (GammaGroundGammaKPlus hc ground)) =
    ⟨l + k, gammaGroundGammaClassMul (gammaGroundGammaClass V) (gammaGroundGammaClass U)⟩
  rw [gammaGroundGammaClassMul_class, gammaGroundGammaClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (gammaGroundGammaClass_heq_of_castHom (Nat.add_comm k l) _ _ (gammaGroundGammaProductCommHom U V))

theorem gammaGroundGammaHomogeneous_mul_one (a : GradedMonoid (GammaGroundGammaKPlus (M := M) hc ground)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
  change (⟨k + 0, gammaGroundGammaClassMul (gammaGroundGammaClass U) (gammaGroundGammaClass (GammaGroundGammaObject.unit hc ground))⟩ :
    GradedMonoid (GammaGroundGammaKPlus hc ground)) = ⟨k, gammaGroundGammaClass U⟩
  rw [gammaGroundGammaClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (gammaGroundGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundGammaProductRightUnitHom U))))

theorem gammaGroundGammaHomogeneous_mul_assoc (a b c : GradedMonoid (GammaGroundGammaKPlus (M := M) hc ground)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundGammaClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundGammaClass_surjective c
  change (⟨(k + l) + j, gammaGroundGammaClassMul (gammaGroundGammaClassMul (gammaGroundGammaClass U) (gammaGroundGammaClass V)) (gammaGroundGammaClass W)⟩ :
    GradedMonoid (GammaGroundGammaKPlus hc ground)) =
      ⟨k + (l + j), gammaGroundGammaClassMul (gammaGroundGammaClass U) (gammaGroundGammaClassMul (gammaGroundGammaClass V) (gammaGroundGammaClass W))⟩
  rw [gammaGroundGammaClassMul_class, gammaGroundGammaClassMul_class, gammaGroundGammaClassMul_class, gammaGroundGammaClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (gammaGroundGammaClass_heq_of_castHom (Nat.add_assoc k l j) _ _ (gammaGroundGammaProductAssocHom U V W))

instance gammaGroundGammaKPlusGCommMonoid : GradedMonoid.GCommMonoid (GammaGroundGammaKPlus (M := M) hc ground) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [gammaGroundGammaHomogeneous_mul_comm, gammaGroundGammaHomogeneous_mul_one]
  mul_one := gammaGroundGammaHomogeneous_mul_one
  mul_assoc := gammaGroundGammaHomogeneous_mul_assoc
  mul_comm := gammaGroundGammaHomogeneous_mul_comm

theorem gammaGroundGammaClassMul_zero {k l : ℕ} (a : GammaGroundGammaKPlus (M := M) hc ground k) :
    gammaGroundGammaClassMul a (0 : GammaGroundGammaKPlus hc ground l) = 0 := by
  obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
  rw [← gammaGroundGammaClass_empty (M := M) (hc := hc) (ground := ground) (k := l), gammaGroundGammaClassMul_class]
  exact (gammaGroundGammaClass_iso (gammaGroundGammaProductEmptyIso U l)).trans gammaGroundGammaClass_empty

theorem gammaGroundGammaClassMul_zero_left {k l : ℕ} (b : GammaGroundGammaKPlus (M := M) hc ground l) :
    gammaGroundGammaClassMul (0 : GammaGroundGammaKPlus hc ground k) b = 0 := by
  obtain ⟨V, rfl⟩ := gammaGroundGammaClass_surjective b
  rw [← gammaGroundGammaClass_empty (M := M) (hc := hc) (ground := ground) (k := k), gammaGroundGammaClassMul_class]
  exact (gammaGroundGammaClass_iso (gammaGroundGammaEmptyProductIso V k)).trans gammaGroundGammaClass_empty

theorem gammaGroundGammaClassMul_add {k l : ℕ} (a : GammaGroundGammaKPlus (M := M) hc ground k)
    (b c : GammaGroundGammaKPlus hc ground l) :
    gammaGroundGammaClassMul a (b + c) = gammaGroundGammaClassMul a b + gammaGroundGammaClassMul a c := by
  obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundGammaClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundGammaClass_surjective c
  rw [← gammaGroundGammaClass_coprod V W, gammaGroundGammaClassMul_class,
    gammaGroundGammaClassMul_class, gammaGroundGammaClassMul_class]
  exact gammaGroundGammaClass_product_coprod U V W

theorem gammaGroundGammaClassMul_add_left {k l : ℕ} (a b : GammaGroundGammaKPlus (M := M) hc ground k)
    (c : GammaGroundGammaKPlus hc ground l) :
    gammaGroundGammaClassMul (a + b) c = gammaGroundGammaClassMul a c + gammaGroundGammaClassMul b c := by
  rw [← gammaGroundGammaClassMul_comm_cast (a + b) c, gammaGroundGammaClassMul_add, gammaGroundGammaKPlusCast_add,
    gammaGroundGammaClassMul_comm_cast, gammaGroundGammaClassMul_comm_cast]

end DiamondIntegral.Section3
