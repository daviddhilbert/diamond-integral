import Mathlib.Data.Set.Function

/-! An injective image retains the complete unique-membership
partition of its source, including all containment assertions. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical

theorem injective_image_unique_partition {X Y ι : Type*} {P : ι → Type*}
    (f : Y → X) (hf : Function.Injective f) (p : ∀ i, P i → Y)
    (hp : ∀ y, ∃! i, y ∈ Set.range (p i)) (x : X) :
    x ∈ Set.range f ↔ ∃! i, x ∈ Set.range (f ∘ p i) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, hi, huniq⟩ := hp y
    obtain ⟨a, ha⟩ := hi
    refine ⟨i, ⟨a, congrArg f ha⟩, ?_⟩
    intro j hj
    obtain ⟨b, hb⟩ := hj
    exact huniq j ⟨b, hf hb⟩
  · rintro ⟨i, ⟨a, ha⟩, _⟩
    exact ⟨p i a, ha⟩

end DiamondIntegral.Section5
