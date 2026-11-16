import «section 6».QuotientCovariance
import «section 2».Conventions
import Section9.LimitGeometry

/-! Actual finite Gamma radii and the paper's valuation order. The
quotients are by open additive balls, not by RV classes. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

@[simp] theorem valueHom_eq_value (a : VF M) : Values.vfValueHom a = vfValue a := rfl

def Congruent (α : Fin n → Gamma M) (a b : Fin n → VF M) : Prop :=
  ∀ i, (α i).val < vfValue (a i - b i)

theorem Congruent.refl (α : Fin n → Gamma M) (a : Fin n → VF M) :
    Congruent α a a := by
  intro i
  change (α i).val < Values.vfValueHom (a i - a i)
  rw [sub_self]
  exact gamma_lt_value_zero (α i)

theorem Congruent.symm {α : Fin n → Gamma M} {a b : Fin n → VF M}
    (h : Congruent α a b) : Congruent α b a := by
  intro i
  change (α i).val < Values.vfValueHom (b i - a i)
  rw [vfValue_sub_comm]
  exact h i

theorem Congruent.trans {α : Fin n → Gamma M} {a b c : Fin n → VF M}
    (hab : Congruent α a b) (hbc : Congruent α b c) : Congruent α a c := by
  intro i
  have hv := vfValue_min_le_sub (a i - b i) (c i - b i)
  rw [show a i - b i - (c i - b i) = a i - c i by abel] at hv
  exact (lt_min (hab i) (hbc.symm i)).trans_le hv

def ballSetoid (α : Fin n → Gamma M) : Setoid (Fin n → VF M) where
  r := Congruent α
  iseqv := ⟨Congruent.refl α, Congruent.symm, Congruent.trans⟩

abbrev BallQuotient (α : Fin n → Gamma M) := Quotient (ballSetoid α)

def ballProjection (α : Fin n → Gamma M) : (Fin n → VF M) → BallQuotient α :=
  Quotient.mk _

theorem ballProjection_eq_iff (α : Fin n → Gamma M) (a b : Fin n → VF M) :
    ballProjection α a = ballProjection α b ↔ Congruent α a b := Quotient.eq

theorem Congruent.of_larger_radius {α β : Fin n → Gamma M}
    (hab : ∀ i, α i ≤ β i) {a b : Fin n → VF M} (h : Congruent β a b) :
    Congruent α a b := fun i => (show (α i).val ≤ (β i).val from hab i).trans_lt (h i)

def AlphaInvariant (α : Fin n → Gamma M) (A : Set (Fin n → VF M)) : Prop :=
  Invariant (ballSetoid α) A

def AlphaBetaCovariant (α : Fin n → Gamma M) (β : Fin m → Gamma M)
    (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M) : Prop :=
  CovariantOn (ballSetoid α) (ballSetoid β) A f

theorem alphaInvariant_iff_quotient (α : Fin n → Gamma M) (A : Set (Fin n → VF M)) :
    AlphaInvariant α A ↔ ballProjection α ⁻¹' (ballProjection α '' A) = A :=
  invariant_iff_quotient_saturated _ _

theorem AlphaInvariant.larger_radius {α β : Fin n → Gamma M}
    {A : Set (Fin n → VF M)} (hA : AlphaInvariant α A) (hab : ∀ i, α i ≤ β i) :
    AlphaInvariant β A := fun a b h => hA a b (h.of_larger_radius hab)

theorem AlphaInvariant.inter {α β : Fin n → Gamma M}
    {A B : Set (Fin n → VF M)} (hA : AlphaInvariant α A) (hB : AlphaInvariant β B) :
    AlphaInvariant (fun i => max (α i) (β i)) (A ∩ B) :=
  Invariant.inter (hA.larger_radius (fun i => le_max_left _ _))
    (hB.larger_radius (fun i => le_max_right _ _))

theorem AlphaInvariant.diff {α β : Fin n → Gamma M}
    {A B : Set (Fin n → VF M)} (hA : AlphaInvariant α A) (hB : AlphaInvariant β B) :
    AlphaInvariant (fun i => max (α i) (β i)) (A \ B) :=
  Invariant.diff (hA.larger_radius (fun i => le_max_left _ _))
    (hB.larger_radius (fun i => le_max_right _ _))

theorem alphaBetaCovariant_iff_contracts (α : Fin n → Gamma M)
    (β : Fin m → Gamma M) (A : Set (Fin n → VF M))
    (f : (Fin n → VF M) → Fin m → VF M) :
    AlphaBetaCovariant α β A f ↔
      ∃ down : Quotient ((ballSetoid α).comap (fun a : A => a.val)) → BallQuotient β,
        ∀ a : A, down (Quotient.mk _ a) = ballProjection β (f a.val) :=
  covariantOn_iff_contracts _ _ _ _

end DiamondIntegral.Section6
