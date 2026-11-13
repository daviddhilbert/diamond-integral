import «section 4».DefinableBiUniqueRelation

/-! Transport a bijective relation along two actual decoding bijections. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.BiUniqueTransport
open DefinableBiUniqueRelation

theorem pullback {K F α β α' β' : Type*}
    {D : Set (α → K)} {E : Set (β → K)}
    {S : Set (α' → F)} {T : Set (β' → F)}
    (f : (α → K) → (α' → F)) (g : (β → K) → (β' → F))
    (hf : Set.BijOn f D S) (hg : Set.BijOn g E T)
    (R : Set ((α' ⊕ β') → F)) (h : BiUnique S T R) :
    BiUnique D E {z | Sum.elim (f (z ∘ Sum.inl)) (g (z ∘ Sum.inr)) ∈ R} := by
  constructor
  · intro x hx
    obtain ⟨y, hy, huniq⟩ := h.left (f x) (hf.mapsTo hx)
    obtain ⟨z, hz, hgz⟩ := hg.surjOn hy.1
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · change Sum.elim (f x) (g z) ∈ R
      simpa only [hgz] using hy.2
    · rintro z' ⟨hz', hr⟩
      apply hg.injOn hz' hz
      exact (huniq (g z') ⟨hg.mapsTo hz', hr⟩).trans hgz.symm
  · intro y hy
    obtain ⟨x, hx, huniq⟩ := h.right (g y) (hg.mapsTo hy)
    obtain ⟨z, hz, hfz⟩ := hf.surjOn hx.1
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · change Sum.elim (f z) (g y) ∈ R
      simpa only [hfz] using hx.2
    · rintro z' ⟨hz', hr⟩
      apply hf.injOn hz' hz
      exact (huniq (f z') ⟨hf.mapsTo hz', hr⟩).trans hfz.symm

end DiamondIntegral.Section4.BiUniqueTransport
