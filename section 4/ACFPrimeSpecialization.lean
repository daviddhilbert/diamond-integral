import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect

/-! Specialization of any true characteristic-zero algebraically closed
field sentence to positive characteristic, and a finite parameter field
inside an algebraic closure of a prime field. These are proved from the
checked Lefschetz and field-theoretic foundations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.ACFPrimeSpecialization
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem sentence_specializes {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [FirstOrder.Ring.CompatibleRing K] (φ : Language.ring.Sentence) (hφ : K ⊨ φ) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      AlgebraicClosure (ZMod p) ⊨ φ := by
  have ht : Theory.ACF 0 ⊨ᵇ φ :=
    (FirstOrder.Field.ACF_isComplete (Or.inr rfl)).realize_sentence_iff φ K |>.mp hφ
  obtain ⟨p, hp⟩ := (FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize.mp ht).nonempty
  refine ⟨p.val, p.property, ?_⟩
  letI : Fact p.val.Prime := ⟨p.property⟩
  exact hp.realize_sentence (AlgebraicClosure (ZMod p.val))

theorem finite_parameter_field (p : ℕ) [Fact p.Prime]
    (A : Set (AlgebraicClosure (ZMod p))) (hA : A.Finite) :
    ∃ E : IntermediateField (ZMod p) (AlgebraicClosure (ZMod p)),
      Finite E ∧ IsGalois E (AlgebraicClosure (ZMod p)) ∧ A ⊆ E := by
  letI : Finite A := hA
  let E := IntermediateField.adjoin (ZMod p) A
  letI : FiniteDimensional (ZMod p) E := inferInstance
  letI : Finite E := Module.finite_of_finite (ZMod p)
  refine ⟨E, inferInstance, ?_, IntermediateField.subset_adjoin (ZMod p) A⟩
  letI : Algebra.IsAlgebraic E (AlgebraicClosure (ZMod p)) :=
    Algebra.IsAlgebraic.tower_top (K := ZMod p) E
  letI : IsAlgClosure E (AlgebraicClosure (ZMod p)) := ⟨inferInstance, inferInstance⟩
  exact { to_isSeparable := inferInstance, to_normal := inferInstance }

end DiamondIntegral.Section4.ACFPrimeSpecialization
