import «section 2».Conventions
import Section9.VFJacobian

/-!
# Definition 2.37: tuple values and punctured differentiation

The actual Gamma quotient has the paper's order, with infinity greatest.
Its group operation is written multiplicatively by the companion library:
division below represents subtraction of additive valuations. The denominator
is finite because increments are nonzero. Coordinatewise values remain a
separate map, as required for the boundedness convention.
-/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def coordinateValues (a : Fin n → VF M) : Fin n → GammaInfinity M :=
  fun i => vfValue (a i)

/-- Minimum coordinate valuation; the empty tuple has value infinity. -/
noncomputable def tupleValue (a : Fin n → VF M) : GammaInfinity M :=
  SpecialTransformations.Section8.vfTupleValue a

theorem tupleValue_le_coordinate (a : Fin n → VF M) (i : Fin n) :
    tupleValue a ≤ coordinateValues a i :=
  SpecialTransformations.Section8.vfTupleValue_le_component a i

theorem tupleValue_eq_coordinate (a : Fin n → VF M) (hn : 0 < n) :
    ∃ i, tupleValue a = coordinateValues a i :=
  SpecialTransformations.Section8.vfTupleValue_eq_component a hn

@[simp] theorem tupleValue_zero : tupleValue (0 : Fin n → VF M) = Values.infinity := by
  rw [tupleValue, SpecialTransformations.Section8.vfTupleValue_zero,
    Values.infinity_eq_zero]

@[simp] theorem tupleValue_eq_infinity_iff (a : Fin n → VF M) :
    tupleValue a = Values.infinity ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    exact SpecialTransformations.Section9.vfTupleValue_ne_zero hne
      (h.trans Values.infinity_eq_zero)
  · rintro rfl
    exact tupleValue_zero

theorem tupleValue_lower_bound_iff (γ : GammaInfinity M) (a : Fin n → VF M) :
    γ ≤ tupleValue a ↔ ∀ i, γ ≤ coordinateValues a i := by
  constructor
  · exact fun h i => h.trans (tupleValue_le_coordinate a i)
  · intro h
    by_cases hn : 0 < n
    · obtain ⟨i, hi⟩ := tupleValue_eq_coordinate a hn
      rw [hi]
      exact h i
    · have he : a = 0 := funext (fun i => (hn (Nat.zero_lt_of_lt i.isLt)).elim)
      rw [he, tupleValue_zero]
      exact Values.le_infinity γ

private theorem value_mul_lt_right {a b c : GammaInfinity M}
    (h : a < b) (hc : c ≠ 0) : a * c < b * c :=
  lt_of_le_of_ne (mul_le_mul' h.le le_rfl)
    (fun he => h.ne (mul_right_cancel₀ hc he))

private theorem value_quotient_iff (a b c : GammaInfinity M) (hc : c ≠ 0) :
    a < b / c ↔ a * c < b := by
  constructor
  · intro h
    simpa only [div_mul_cancel₀ _ hc] using value_mul_lt_right h hc
  · intro h
    have hi := value_mul_lt_right h (inv_ne_zero hc)
    simpa only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hc, mul_one] using hi

/-- The approved difference quotient, with the zero increment excluded. -/
def HasDerivativeAt (f : (Fin n → VF M) → Fin m → VF M) (a : Fin n → VF M)
    (L : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)) : Prop :=
  ∀ ε : Gamma M, ∃ δ : Gamma M, ∀ b : Fin n → VF M,
    b ≠ 0 → δ.val < tupleValue b →
      ε.val < tupleValue (f (a + b) - f a - L b) / tupleValue b

theorem hasDerivativeAt_iff_companion
    (f : (Fin n → VF M) → Fin m → VF M) (a : Fin n → VF M)
    (L : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)) :
    HasDerivativeAt f a L ↔ SpecialTransformations.Section9.HasVFDerivativeAt f a L := by
  constructor <;> intro h ε <;> obtain ⟨δ, hδ⟩ := h ε <;> refine ⟨δ, ?_⟩
  · intro b hb hnear
    exact (value_quotient_iff _ _ _
      (SpecialTransformations.Section9.vfTupleValue_ne_zero hb)).mp (hδ b hb hnear)
  · intro b hb hnear
    exact (value_quotient_iff _ _ _
      (SpecialTransformations.Section9.vfTupleValue_ne_zero hb)).mpr (hδ b hb hnear)

theorem HasDerivativeAt.unique
    {f : (Fin n → VF M) → Fin m → VF M} {a : Fin n → VF M}
    {L D : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)}
    (hL : HasDerivativeAt f a L) (hD : HasDerivativeAt f a D) : L = D :=
  ((hasDerivativeAt_iff_companion f a L).mp hL).unique
    ((hasDerivativeAt_iff_companion f a D).mp hD)

/-- Input index first; its matrix position is (output, input). -/
def HasPartialDerivativeAt (f : (Fin n → VF M) → Fin m → VF M)
    (a : Fin n → VF M) (i : Fin n) (j : Fin m) (d : VF M) : Prop :=
  SpecialTransformations.Section9.HasVFPartialAt f a i j d

theorem HasDerivativeAt.partial_matrix_entry
    {f : (Fin n → VF M) → Fin m → VF M} {a : Fin n → VF M}
    {L : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)}
    (hL : HasDerivativeAt f a L) (i : Fin n) (j : Fin m) :
    HasPartialDerivativeAt f a i j (LinearMap.toMatrix' L j i) :=
  ((hasDerivativeAt_iff_companion f a L).mp hL).hasPartialAt i j

end DiamondIntegral.Section2
