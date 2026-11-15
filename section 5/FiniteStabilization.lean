import Section4.Imported.GrothendieckRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-! The algebraic finite-witness criterion used in the Fubini proof.
No cancellation is assumed for positive classes. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Algebra Algebra.GrothendieckAddGroup
variable {S : Type*} [CommSemiring S]

/-- A finite sum of positive multiples of generator pairs, in either direction. -/
inductive PositiveRelationSum (P : Set (S × S)) : S → S → Prop
  | zero : PositiveRelationSum P 0 0
  | step {L R : S} (h : PositiveRelationSum P L R) {a b : S}
      (hab : (a, b) ∈ P) (c : S) : PositiveRelationSum P (L + c * a) (R + c * b)
  | reverse {L R : S} (h : PositiveRelationSum P L R) {a b : S}
      (hab : (a, b) ∈ P) (c : S) : PositiveRelationSum P (L + c * b) (R + c * a)

theorem PositiveRelationSum.symm {P : Set (S × S)} {L R : S}
    (h : PositiveRelationSum P L R) : PositiveRelationSum P R L := by
  induction h with
  | zero => exact .zero
  | step h hab c ih => exact .reverse ih hab c
  | reverse h hab c ih => exact .step ih hab c

theorem PositiveRelationSum.add {P : Set (S × S)} {L R L' R' : S}
    (h : PositiveRelationSum P L R) (h' : PositiveRelationSum P L' R') :
    PositiveRelationSum P (L + L') (R + R') := by
  induction h' with
  | zero => simpa using h
  | step h' hab c ih => simpa only [← add_assoc] using ih.step hab c
  | reverse h' hab c ih => simpa only [← add_assoc] using ih.reverse hab c

theorem PositiveRelationSum.mul {P : Set (S × S)} {L R : S}
    (h : PositiveRelationSum P L R) (d : S) : PositiveRelationSum P (d * L) (d * R) := by
  induction h with
  | zero => simpa using (PositiveRelationSum.zero (P := P))
  | step h hab c ih => simpa only [mul_add, mul_assoc] using ih.step hab (d * c)
  | reverse h hab c ih => simpa only [mul_add, mul_assoc] using ih.reverse hab (d * c)

def OrientedPositivePair (P : Set (S × S)) (p : S × S) : Prop :=
  ∃ a b : S, (a, b) ∈ P ∧ ∃ c : S,
    p = (c * a, c * b) ∨ p = (c * b, c * a)

/-- The inductive witness is literally a finite list of oriented pairs. -/
theorem PositiveRelationSum.finite_list {P : Set (S × S)} {L R : S}
    (h : PositiveRelationSum P L R) :
    ∃ entries : List (S × S), (∀ p ∈ entries, OrientedPositivePair P p) ∧
      L = (entries.map Prod.fst).sum ∧ R = (entries.map Prod.snd).sum := by
  induction h with
  | zero => exact ⟨[], by simp, rfl, rfl⟩
  | @step L R h a b hab c ih =>
    obtain ⟨entries, he, hL, hR⟩ := ih
    refine ⟨entries ++ [(c * a, c * b)], ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact he p hp
      · obtain rfl := List.mem_singleton.mp hp
        exact ⟨a, b, hab, c, Or.inl rfl⟩
    · simp [hL]
    · simp [hR]
  | @reverse L R h a b hab c ih =>
    obtain ⟨entries, he, hL, hR⟩ := ih
    refine ⟨entries ++ [(c * b, c * a)], ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact he p hp
      · obtain rfl := List.mem_singleton.mp hp
        exact ⟨a, b, hab, c, Or.inr rfl⟩
    · simp [hL]
    · simp [hR]

def positiveRelationIdeal (P : Set (S × S)) : Ideal (GrothendieckAddGroup S) :=
  Ideal.span {x | ∃ p ∈ P, x = of p.1 - of p.2}

theorem PositiveRelationSum.difference_mem {P : Set (S × S)} {L R : S}
    (h : PositiveRelationSum P L R) : of L - of R ∈ positiveRelationIdeal P := by
  induction h with
  | zero => simp
  | @step L R h a b hab c ih =>
    have hm : of c * (of a - of b) ∈ positiveRelationIdeal P :=
      (positiveRelationIdeal P).mul_mem_left _ (Ideal.subset_span ⟨(a, b), hab, rfl⟩)
    convert (positiveRelationIdeal P).add_mem ih hm using 1 <;>
      simp only [map_add, mul_sub, of_mul_of] <;> abel
  | @reverse L R h a b hab c ih =>
    have hm : of c * (of a - of b) ∈ positiveRelationIdeal P :=
      (positiveRelationIdeal P).mul_mem_left _ (Ideal.subset_span ⟨(a, b), hab, rfl⟩)
    convert (positiveRelationIdeal P).sub_mem ih hm using 1 <;>
      simp only [map_add, mul_sub, of_mul_of] <;> abel

theorem mem_positiveRelationIdeal_iff (P : Set (S × S)) (x : GrothendieckAddGroup S) :
    x ∈ positiveRelationIdeal P ↔
      ∃ L R : S, PositiveRelationSum P L R ∧ x = of L - of R := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hy
      exact ⟨a, b, by simpa using (PositiveRelationSum.zero (P := P)).step hab 1, rfl⟩
    | zero => exact ⟨0, 0, .zero, by simp⟩
    | add y z hy hz ihy ihz =>
      obtain ⟨L, R, h, rfl⟩ := ihy
      obtain ⟨L', R', h', rfl⟩ := ihz
      exact ⟨L + L', R + R', h.add h', by simp only [map_add]; abel⟩
    | smul c y hy ih =>
      obtain ⟨a, b, rfl⟩ := exists_eq_sub_of c
      obtain ⟨L, R, h, rfl⟩ := ih
      refine ⟨a * L + b * R, a * R + b * L, (h.mul a).add (h.symm.mul b), ?_⟩
      simp only [smul_eq_mul, sub_mul, mul_sub, map_add, ← of_mul_of]
      abel
  · rintro ⟨L, R, h, rfl⟩
    exact h.difference_mem

theorem grothendieck_of_eq_iff (a b : S) :
    (of a : GrothendieckAddGroup S) = of b ↔ ∃ c : S, a + c = b + c := by
  change AddLocalization.addMonoidOf (⊤ : AddSubmonoid S) a =
    AddLocalization.addMonoidOf (⊤ : AddSubmonoid S) b ↔ _
  rw [(AddLocalization.addMonoidOf (⊤ : AddSubmonoid S)).eq_iff_exists]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.val, by simpa only [add_comm] using hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, trivial⟩, by simpa only [add_comm] using hc⟩

/-- Equality in the quotient has one common positive stabilizer and finitely
many oriented positive relation pairs. This is the finite algebraic core of
the manuscript's criterion (5.20). -/
theorem finite_stabilized_quotient_equality (P : Set (S × S)) (a b : S) :
    Ideal.Quotient.mk (positiveRelationIdeal P) (of a) =
      Ideal.Quotient.mk (positiveRelationIdeal P) (of b) ↔
    ∃ c L R : S, PositiveRelationSum P L R ∧ a + c + R = b + c + L := by
  rw [Ideal.Quotient.eq, mem_positiveRelationIdeal_iff]
  constructor
  · rintro ⟨L, R, h, he⟩
    have he' : (of (a + R) : GrothendieckAddGroup S) = of (b + L) := by
      simp only [map_add]
      apply sub_eq_zero.mp
      rw [sub_eq_iff_eq_add] at he
      linear_combination he
    obtain ⟨c, hc⟩ := (grothendieck_of_eq_iff (a + R) (b + L)).mp he'
    exact ⟨c, L, R, h, by simpa only [add_assoc, add_comm, add_left_comm] using hc⟩
  · rintro ⟨c, L, R, h, he⟩
    refine ⟨L, R, h, ?_⟩
    have hh := congrArg (of : S →+ GrothendieckAddGroup S) he
    simp only [map_add] at hh
    linear_combination hh

end DiamondIntegral.Section5
