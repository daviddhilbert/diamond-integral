import Section4.PositivePresentation

/-! Positive (scissor) semirings presented by chart relations. The chart
rings of this section are presented by five kinds of relations: actual
isomorphisms, the unit, products, empty charts and scissors. The same data
present a positive Grothendieck semiring, with no subtraction. A formal empty
object (`none`) represents zero; every empty chart is identified with it by a
scissor relation. -/

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section4.PositiveChartPresentation
open SpecialTransformations.Section4

universe u v
variable {Gen : Type u}

/-- Chart relations: isomorphisms, the unit, products, empty charts, and
scissor relations `[a] + [b] = [c] + [d]`. -/
structure ChartRelations (Gen : Type u) where
  iso : Gen → Gen → Prop
  unit : Gen
  product : Gen → Gen → Gen
  empty : Gen → Prop
  scissor : Gen → Gen → Gen → Gen → Prop

namespace ChartRelations
variable (R : ChartRelations Gen)

/-- Products, extended by the formal empty object. -/
def optionProduct : Option Gen → Option Gen → Option Gen
  | some a, some b => some (R.product a b)
  | _, _ => none

/-- The positive presentation on charts together with a formal empty object. -/
def presentation : PositiveGrothendieck.Presentation (Option Gen) where
  iso x y := ∃ a b, R.iso a b ∧ x = some a ∧ y = some b
  empty := none
  unit := some R.unit
  product := R.optionProduct
  scissor x y z w :=
    (∃ a b c d, R.scissor a b c d ∧ x = some a ∧ y = some b ∧ z = some c ∧ w = some d) ∨
    (∃ a, R.empty a ∧ x = some a ∧ y = none ∧ z = none ∧ w = none)

/-- The positive semiring presented by the chart relations. -/
abbrev KPlus := PositiveGrothendieck.KPlus R.presentation

/-- The class of a chart. -/
def cls (a : Gen) : R.KPlus := PositiveGrothendieck.of R.presentation (some a)

theorem none_zero : PositiveGrothendieck.of R.presentation none = 0 :=
  PositiveGrothendieck.of_empty R.presentation

theorem cls_iso {a b : Gen} (h : R.iso a b) : R.cls a = R.cls b :=
  PositiveGrothendieck.of_iso R.presentation ⟨a,b,h,rfl,rfl⟩

theorem cls_unit : R.cls R.unit = 1 := PositiveGrothendieck.of_unit R.presentation

theorem cls_product (a b : Gen) : R.cls (R.product a b) = R.cls a * R.cls b :=
  PositiveGrothendieck.of_product R.presentation (some a) (some b)

theorem cls_empty {a : Gen} (h : R.empty a) : R.cls a = 0 := by
  have hs := PositiveGrothendieck.of_scissor R.presentation
    (show R.presentation.scissor (some a) none none none from Or.inr ⟨a,h,rfl,rfl,rfl,rfl⟩)
  rw [R.none_zero,add_zero,add_zero] at hs
  exact hs

theorem cls_scissor {a b c d : Gen} (h : R.scissor a b c d) : R.cls a + R.cls b = R.cls c + R.cls d :=
  PositiveGrothendieck.of_scissor R.presentation (Or.inl ⟨a,b,c,d,h,rfl,rfl,rfl,rfl⟩)

/-- A function on charts respecting the chart relations. -/
structure Invariant (S : Type v) [CommSemiring S] where
  value : Gen → S
  iso : ∀ {a b}, R.iso a b → value a = value b
  unit : value R.unit = 1
  product : ∀ a b, value (R.product a b) = value a * value b
  empty : ∀ {a}, R.empty a → value a = 0
  scissor : ∀ {a b c d}, R.scissor a b c d → value a + value b = value c + value d

variable {R}

/-- An invariant extends to the presentation, with value `0` on the formal empty object. -/
def Invariant.extend {S : Type v} [CommSemiring S] (f : R.Invariant S) :
    PositiveGrothendieck.Invariant R.presentation (R := S) where
  toFun x := Option.elim x 0 f.value
  iso := by
    rintro x y ⟨a,b,h,rfl,rfl⟩
    exact f.iso h
  empty := rfl
  unit := f.unit
  product := by
    rintro (_ | a) (_ | b)
    · exact (zero_mul _).symm
    · exact (zero_mul _).symm
    · exact (mul_zero _).symm
    · exact f.product a b
  scissor := by
    rintro x y z w (⟨a,b,c,d,h,rfl,rfl,rfl,rfl⟩ | ⟨a,h,rfl,rfl,rfl,rfl⟩)
    · exact f.scissor h
    · change f.value a + 0 = 0 + 0
      rw [f.empty h]

variable (R)

/-- The universal property: an invariant defines a semiring map. -/
def lift {S : Type v} [CommSemiring S] (f : R.Invariant S) : R.KPlus →+* S :=
  PositiveGrothendieck.lift R.presentation f.extend

@[simp] theorem lift_cls {S : Type v} [CommSemiring S] (f : R.Invariant S) (a : Gen) :
    R.lift f (R.cls a) = f.value a :=
  PositiveGrothendieck.lift_of R.presentation f.extend (some a)

theorem hom_ext {S : Type v} [CommSemiring S] {F G : R.KPlus →+* S}
    (h : ∀ a, F (R.cls a) = G (R.cls a)) : F = G := by
  apply PositiveGrothendieck.hom_ext R.presentation
  rintro (_ | a)
  · rw [R.none_zero,map_zero,map_zero]
  · exact h a

/-- The classes of charts generate the positive semiring additively and
multiplicatively; in particular a map is determined by them. Every element is
a class difference only after group completion, which is not used here. -/
theorem cls_surjective_generators (x : R.KPlus) :
    ∃ p : MvPolynomial (Option Gen) ℕ, PositiveGrothendieck.quotientHom R.presentation p = x :=
  (PositiveGrothendieck.congruence R.presentation).mk'_surjective x

end ChartRelations
end DiamondIntegral.Section4.PositiveChartPresentation
