import «section 3».DefinableBijections
import Mathlib.Algebra.Order.Group.Abs

/-! Independent algebraic checks of R050 and the definable-point obstruction
behind R053. The R053 geometric existence argument is recorded separately;
the abstract no-bijection criterion does not assert that it has constructed
a particular ACVF model or parameter structure. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section3

variable {G : Type} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- An absolute value cannot be one affine homomorphism on a nontrivial
ordered group. Integer-linear maps are a special case of additive maps. -/
theorem abs_not_affine (a : G) (ha : 0 < a) :
    ¬ ∃ (f : G →+ G) (c : G), ∀ x, |x| = f x + c := by
  rintro ⟨f, c, h⟩
  have hc : c = 0 := by simpa only [abs_zero, map_zero, zero_add] using (h 0).symm
  have hp := h a
  have hn := h (-a)
  rw [hc, add_zero, abs_of_pos ha] at hp
  rw [hc, add_zero, abs_neg, abs_of_pos ha, map_neg, ← hp] at hn
  have hneg : -a < 0 := neg_neg_of_pos ha
  exact (not_lt_of_ge ha.le) (hn ▸ hneg)

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M}

theorem no_definable_bijection_of_point_obstruction
    (A : DefSet P S) (B : DefSet Q S)
    (hA : ¬ ∃ a : A, IsDefinablePoint S a.val)
    (hB : ∃ b : B, IsDefinablePoint S b.val) :
    IsEmpty (DefinableBijection A B) :=
  ⟨fun F => hA ((definableBijection_has_point_iff F).mpr hB)⟩

end DiamondIntegral.Section3
