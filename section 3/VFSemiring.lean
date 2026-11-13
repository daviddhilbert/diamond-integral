import «section 3».VFProducts
import «section 3».VFScissors
import Section3.ModelContext
import Section4.PositivePresentation

/-! The filtered VF positive semiring identifies different dimension
bounds on the same definable set. Products are actual mixed products,
with the checked section 2 dimension bound and finite RV fibres. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

abbrev FilteredVFObject (S : Set M) := Σ k, VFObject (M := M) S k

def filteredVFScissor {S : Set M} (A B D E : FilteredVFObject (M := M) S) : Prop :=
  (∃ k, ∃ a b d e : VFObject S k,
    VFScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, VFObject.empty S k⟩ ∧ B = ⟨0, VFObject.empty S 0⟩ ∧
    D = ⟨0, VFObject.empty S 0⟩ ∧ E = ⟨0, VFObject.empty S 0⟩)

def vfSemiringPresentation :
    PositiveGrothendieck.Presentation (FilteredVFObject (M := M) (C.base : Set M)) where
  iso A B := Nonempty (DefinableBijection A.2.domain B.2.domain)
  empty := ⟨0, VFObject.empty (C.base : Set M) 0⟩
  unit := ⟨0, VFObject.unit (C.base : Set M)⟩
  product A B := ⟨A.1 + B.1, A.2.product hc C.saturated C.small hv B.2⟩
  scissor := filteredVFScissor

abbrev VFPositiveSemiring := PositiveGrothendieck.KPlus (vfSemiringPresentation C hc hv)
abbrev VFGrothendieckRing := Algebra.GrothendieckAddGroup (VFPositiveSemiring C hc hv)

def vfSemiringClass {k : ℕ} (U : VFObject (M := M) (C.base : Set M) k) : VFPositiveSemiring C hc hv :=
  PositiveGrothendieck.of (vfSemiringPresentation C hc hv) ⟨k, U⟩

theorem vfSemiringClass_bijection {k l : ℕ}
    {U : VFObject (M := M) (C.base : Set M) k} {V : VFObject (M := M) (C.base : Set M) l}
    (f : DefinableBijection U.domain V.domain) :
    vfSemiringClass C hc hv U = vfSemiringClass C hc hv V :=
  PositiveGrothendieck.of_iso (vfSemiringPresentation C hc hv) ⟨f⟩

theorem vfSemiringClass_raise {k l : ℕ} (U : VFObject (M := M) (C.base : Set M) k) (hkl : k ≤ l) :
    vfSemiringClass C hc hv (U.raise hkl) = vfSemiringClass C hc hv U :=
  vfSemiringClass_bijection C hc hv (DefinableBijection.id U.domain)

@[simp] theorem vfSemiringClass_empty {k : ℕ} :
    vfSemiringClass C hc hv (VFObject.empty (M := M) (C.base : Set M) k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (vfSemiringPresentation C hc hv)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (vfSemiringPresentation C hc hv)
      ⟨0, VFObject.empty (C.base : Set M) 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem vfSemiringClass_unit :
    vfSemiringClass C hc hv (VFObject.unit (M := M) (C.base : Set M)) = 1 :=
  PositiveGrothendieck.of_unit (vfSemiringPresentation C hc hv)

theorem vfSemiringClass_product {k l : ℕ}
    (U : VFObject (M := M) (C.base : Set M) k) (V : VFObject (M := M) (C.base : Set M) l) :
    vfSemiringClass C hc hv (U.product hc C.saturated C.small hv V) =
      vfSemiringClass C hc hv U * vfSemiringClass C hc hv V :=
  PositiveGrothendieck.of_product (vfSemiringPresentation C hc hv) ⟨k, U⟩ ⟨l, V⟩

theorem vfSemiringClass_scissor {k : ℕ}
    {A B D E : VFObject (M := M) (C.base : Set M) k} (h : VFScissor A B D E) :
    vfSemiringClass C hc hv A + vfSemiringClass C hc hv B =
      vfSemiringClass C hc hv D + vfSemiringClass C hc hv E :=
  PositiveGrothendieck.of_scissor (vfSemiringPresentation C hc hv)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def vfKPlusToSemiring {k : ℕ} : VFKPlus (M := M) (C.base : Set M) k →+ VFPositiveSemiring C hc hv :=
  PositiveAdditiveGrothendieck.lift (vfPresentation (C.base : Set M) k) {
    toFun := vfSemiringClass C hc hv
    iso := fun h => by obtain ⟨e⟩ := h; exact vfSemiringClass_bijection C hc hv e.hom
    empty := vfSemiringClass_empty C hc hv
    scissor := vfSemiringClass_scissor C hc hv }

@[simp] theorem vfKPlusToSemiring_class {k : ℕ} (U : VFObject (M := M) (C.base : Set M) k) :
    vfKPlusToSemiring C hc hv (vfClass U) = vfSemiringClass C hc hv U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def vfSemiringUniversal {R : Type} [CommSemiring R] :
    PositiveGrothendieck.Invariant (vfSemiringPresentation C hc hv) (R := R) ≃
      (VFPositiveSemiring C hc hv →+* R) := PositiveGrothendieck.universalEquiv _

end DiamondIntegral.Section3
