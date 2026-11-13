import «section 3».GammaGroundMeasuredRVProductScissors
import «section 3».GammaGroundMeasuredRVGradedMonoid
import «section 3».GammaGroundEmptyBijections

/-! Cartesian multiplication distributes over actual positive scissors
and hence over arbitrary fixed-degree positive classes. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

theorem gammaGroundMeasuredRVClassMul_zero (a : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVClassMul a (0 : GammaGroundMeasuredRVKPlus hc ground l) = 0 := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  rw [← gammaGroundMeasuredRVClass_empty (M := M) (hc := hc) (ground := ground) (k := l), gammaGroundMeasuredRVClassMul_class]
  have he : (U.product (GammaGroundMeasuredRVObject.empty hc ground l)).underlying.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨a, _⟩
    exact a.property.2
  let f : GammaGroundMeasuredRVHom (U.product (GammaGroundMeasuredRVObject.empty hc ground l))
      (GammaGroundMeasuredRVObject.empty hc ground (k + l)) := {
    bijection := GammaGroundBijection.ofEmpty he rfl
    preserves := fun a => False.elim (by obtain ⟨p, _⟩ := a.property; exact p.property.2) }
  let hi : U.product (GammaGroundMeasuredRVObject.empty hc ground l) ≅ GammaGroundMeasuredRVObject.empty hc ground (k + l) := asIso f

  exact (gammaGroundMeasuredRVClass_iso hi).trans gammaGroundMeasuredRVClass_empty

theorem gammaGroundMeasuredRVKPlusCast_zero (h : k = l) :
    gammaGroundMeasuredRVKPlusCast h (0 : GammaGroundMeasuredRVKPlus hc ground k) = 0 := by cases h; rfl

theorem gammaGroundMeasuredRVClassMul_zero_left (b : GammaGroundMeasuredRVKPlus hc ground l) :
    gammaGroundMeasuredRVClassMul (0 : GammaGroundMeasuredRVKPlus hc ground k) b = 0 := by
  rw [← gammaGroundMeasuredRVClassMul_comm_cast, gammaGroundMeasuredRVClassMul_zero]
  exact gammaGroundMeasuredRVKPlusCast_zero _

theorem gammaGroundMeasuredRVClassMul_add (a : GammaGroundMeasuredRVKPlus hc ground k) (b c : GammaGroundMeasuredRVKPlus hc ground l) :
    gammaGroundMeasuredRVClassMul a (b + c) = gammaGroundMeasuredRVClassMul a b + gammaGroundMeasuredRVClassMul a c := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredRVClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundMeasuredRVClass_surjective c
  rw [← gammaGroundMeasuredRVClass_coprod V W, gammaGroundMeasuredRVClassMul_class,
    gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVClassMul_class]
  exact gammaGroundMeasuredRVClass_product_coprod U V W

theorem gammaGroundMeasuredRVClassMul_add_left (a b : GammaGroundMeasuredRVKPlus hc ground k) (c : GammaGroundMeasuredRVKPlus hc ground l) :
    gammaGroundMeasuredRVClassMul (a + b) c = gammaGroundMeasuredRVClassMul a c + gammaGroundMeasuredRVClassMul b c := by
  rw [← gammaGroundMeasuredRVClassMul_comm_cast (a + b) c, gammaGroundMeasuredRVClassMul_add, gammaGroundMeasuredRVKPlusCast_add,
    gammaGroundMeasuredRVClassMul_comm_cast, gammaGroundMeasuredRVClassMul_comm_cast]

end DiamondIntegral.Section3
