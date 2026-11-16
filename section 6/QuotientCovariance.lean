import Mathlib

/-! The quotient part of Definition 6.1. These results apply before any
definability, saturation, or valued-field hypothesis is imposed. -/

namespace DiamondIntegral.Section6

variable {X Y Z : Type*}

def CovariantOn (s : Setoid X) (t : Setoid Y) (A : Set X) (f : X → Y) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, s a b → t (f a) (f b)

def Invariant (s : Setoid X) (A : Set X) : Prop :=
  ∀ a b, s a b → (a ∈ A ↔ b ∈ A)

theorem covariantOn_iff_contracts (s : Setoid X) (t : Setoid Y)
    (A : Set X) (f : X → Y) :
    CovariantOn s t A f ↔
      ∃ down : Quotient (s.comap (fun a : A => a.val)) → Quotient t,
        ∀ a : A, down (Quotient.mk _ a) = Quotient.mk t (f a.val) := by
  constructor
  · intro h
    refine ⟨Quotient.lift (fun a : A => Quotient.mk t (f a.val)) ?_, fun _ => rfl⟩
    intro a b hab
    exact Quotient.sound (h a a.property b b.property hab)
  · rintro ⟨down, hd⟩ a ha b hb hab
    apply Quotient.exact
    rw [← hd ⟨a, ha⟩, ← hd ⟨b, hb⟩]
    exact congrArg down (Quotient.sound hab)

theorem CovariantOn.mono {s : Setoid X} {t : Setoid Y} {A B : Set X}
    {f : X → Y} (h : CovariantOn s t A f) (hBA : B ⊆ A) : CovariantOn s t B f :=
  fun a ha b hb hab => h a (hBA ha) b (hBA hb) hab

theorem CovariantOn.comp {s : Setoid X} {t : Setoid Y} {u : Setoid Z}
    {A : Set X} {B : Set Y} {f : X → Y} {g : Y → Z}
    (hg : CovariantOn t u B g) (hf : CovariantOn s t A f)
    (hmap : Set.MapsTo f A B) : CovariantOn s u A (g ∘ f) :=
  fun a ha b hb hab => hg (f a) (hmap ha) (f b) (hmap hb) (hf a ha b hb hab)

theorem covariantOn_id (s : Setoid X) (A : Set X) : CovariantOn s s A id :=
  fun _ _ _ _ h => h

theorem covariantOn_const (s : Setoid X) (t : Setoid Y) (A : Set X) (y : Y) :
    CovariantOn s t A (fun _ => y) := fun _ _ _ _ _ => t.refl y

theorem Invariant.compl {s : Setoid X} {A : Set X} (hA : Invariant s A) :
    Invariant s Aᶜ := fun a b hab => not_congr (hA a b hab)

theorem Invariant.inter {s : Setoid X} {A B : Set X}
    (hA : Invariant s A) (hB : Invariant s B) : Invariant s (A ∩ B) :=
  fun a b hab => and_congr (hA a b hab) (hB a b hab)

theorem Invariant.union {s : Setoid X} {A B : Set X}
    (hA : Invariant s A) (hB : Invariant s B) : Invariant s (A ∪ B) :=
  fun a b hab => or_congr (hA a b hab) (hB a b hab)

theorem Invariant.diff {s : Setoid X} {A B : Set X}
    (hA : Invariant s A) (hB : Invariant s B) : Invariant s (A \ B) :=
  hA.inter hB.compl

theorem invariant_iff_quotient_saturated (s : Setoid X) (A : Set X) :
    Invariant s A ↔ (Quotient.mk s) ⁻¹' ((Quotient.mk s) '' A) = A := by
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨a, ha, he⟩
      exact (h a x (Quotient.exact he)).mp ha
    · intro hx
      exact ⟨x, hx, rfl⟩
  · intro h a b hab
    have hs (x y : X) (hxy : s x y) (hx : x ∈ A) : y ∈ A := by
      rw [← h]
      exact ⟨x, hx, Quotient.sound hxy⟩
    exact ⟨hs a b hab, hs b a (s.symm hab)⟩

theorem quotient_saturated_invariant (s : Setoid X) (B : Set (Quotient s)) :
    Invariant s ((Quotient.mk s) ⁻¹' B) := by
  intro a b hab
  change Quotient.mk s a ∈ B ↔ Quotient.mk s b ∈ B
  rw [Quotient.sound hab]

/-- R098: there is one empty output tuple, even for a nonempty source. -/
theorem zero_output_covariant (s : Setoid X) (A : Set X) (f : X → Fin 0 → Y)
    (t : Setoid (Fin 0 → Y)) : CovariantOn s t A f := by
  intro a _ b _ _
  have he : f a = f b := Subsingleton.elim _ _
  rw [he]

theorem quotient_zero_tuple_subsingleton (t : Setoid (Fin 0 → Y)) :
    Subsingleton (Quotient t) := inferInstance

end DiamondIntegral.Section6
