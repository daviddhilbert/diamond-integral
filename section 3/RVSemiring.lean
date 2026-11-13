import «section 3».RVProducts
import «section 3».RVScissors
import Section4.PositivePresentation

/-! The positive RV semiring is the universal commutative semiring on
the actual objects, definable isomorphisms, scissors and cartesian products.
Every degree has its own empty object representing zero. Comparison with
the direct sum of the fixed-degree additive quotients is separate. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def RVObject.unit (S : Set M) : RVObject (M := M) S 0 where
  arity := 0
  domain := DefSet.univ (rawRVSpace 0) S
  volume := Map.id _
  finite := Map.finiteFibres_of_injective Function.injective_id
  nonzero _ i := i.elim0

abbrev GradedRVObject (S : Set M) := Σ k, RVObject (M := M) S k

def gradedRVScissor (A B D E : GradedRVObject (M := M) S) : Prop :=
  (∃ k, ∃ a b d e : RVObject S k,
    RVScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, RVObject.empty S k⟩ ∧ B = ⟨0, RVObject.empty S 0⟩ ∧
    D = ⟨0, RVObject.empty S 0⟩ ∧ E = ⟨0, RVObject.empty S 0⟩)

def rvSemiringPresentation (S : Set M) :
    PositiveGrothendieck.Presentation (GradedRVObject (M := M) S) where
  iso A B := A.1 = B.1 ∧ Nonempty (DefinableBijection A.2.domain B.2.domain)
  empty := ⟨0, RVObject.empty S 0⟩
  unit := ⟨0, RVObject.unit S⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedRVScissor

abbrev RVPositiveSemiring (S : Set M) := PositiveGrothendieck.KPlus (rvSemiringPresentation (M := M) S)
abbrev RVGrothendieckRing (S : Set M) := Algebra.GrothendieckAddGroup (RVPositiveSemiring (M := M) S)

def rvSemiringClass (U : RVObject (M := M) S k) : RVPositiveSemiring S :=
  PositiveGrothendieck.of (rvSemiringPresentation S) ⟨k, U⟩

theorem rvSemiringClass_iso {U V : RVObject (M := M) S k} (e : U ≅ V) :
    rvSemiringClass U = rvSemiringClass V :=
  PositiveGrothendieck.of_iso (rvSemiringPresentation S) ⟨rfl, ⟨e.hom⟩⟩

@[simp] theorem rvSemiringClass_empty : rvSemiringClass (RVObject.empty (M := M) S k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (rvSemiringPresentation (M := M) S)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (rvSemiringPresentation (M := M) S)
      ⟨0, RVObject.empty S 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem rvSemiringClass_unit : rvSemiringClass (RVObject.unit (M := M) S) = 1 :=
  PositiveGrothendieck.of_unit (rvSemiringPresentation S)

theorem rvSemiringClass_product (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    rvSemiringClass (U.product V) = rvSemiringClass U * rvSemiringClass V :=
  PositiveGrothendieck.of_product (rvSemiringPresentation S) ⟨k, U⟩ ⟨l, V⟩

theorem rvSemiringClass_scissor {A B D E : RVObject (M := M) S k} (h : RVScissor A B D E) :
    rvSemiringClass A + rvSemiringClass B = rvSemiringClass D + rvSemiringClass E :=
  PositiveGrothendieck.of_scissor (rvSemiringPresentation S)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def rvKPlusToSemiring : RVKPlus (M := M) S k →+ RVPositiveSemiring S :=
  PositiveAdditiveGrothendieck.lift (rvPresentation S k) {
    toFun := rvSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact rvSemiringClass_iso e
    empty := rvSemiringClass_empty
    scissor := rvSemiringClass_scissor }

@[simp] theorem rvKPlusToSemiring_class (U : RVObject (M := M) S k) :
    rvKPlusToSemiring (rvClass U) = rvSemiringClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def rvSemiringUniversal {R : Type} [CommSemiring R] :
    PositiveGrothendieck.Invariant (rvSemiringPresentation (M := M) S) (R := R) ≃
      (RVPositiveSemiring S →+* R) := PositiveGrothendieck.universalEquiv _

end DiamondIntegral.Section3
