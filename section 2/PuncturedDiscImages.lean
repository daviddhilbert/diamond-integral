import «section 2».GammaPowerRadii

/-! The whole-disc image argument in 2.51. An actual increasing radius
law and control of inverse images on one target neighbourhood give equality
of the entire punctured discs, rather than just containment of images. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def PuncturedValueLaw (f : VF M → VF M) (a b : VF M) (ρ : Gamma M ≃o Gamma M)
    (η : Gamma M) : Prop := ∀ (x : VF M) (hx : x ∈ puncturedGammaDisc a η),
  ∃ hfx : f x ≠ b, finiteValue (f x-b) (sub_ne_zero.mpr hfx) =
    ρ (finiteValue (x-a) (sub_ne_zero.mpr hx.1))

theorem gammaPowerGerm_puncturedValueLaw {f : VF M → VF M} {a b : VF M} {p q : ℕ}
    {c r : Gamma M} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : gammaPowerGerm (fun x => f x-b) a p q c r) :
    PuncturedValueLaw f a b (gammaAffineRadius p q hp hq c) r := by
  intro x hx
  obtain ⟨hfx,he⟩ := gammaPowerGerm_finite_value hp hq h x hx.1 hx.2
  exact ⟨sub_ne_zero.mp hfx,he⟩

theorem PuncturedValueLaw.disc_iff {f : VF M → VF M} {a b : VF M} {ρ : Gamma M ≃o Gamma M}
    {η : Gamma M} (h : PuncturedValueLaw f a b ρ η) (x : VF M)
    (hx : x ∈ puncturedGammaDisc a η) (γ : Gamma M) :
    x ∈ puncturedGammaDisc a γ ↔ f x ∈ puncturedGammaDisc b (ρ γ) := by
  obtain ⟨hfx,he⟩ := h x hx
  change (x ≠ a ∧ γ.val < vfValue (x-a)) ↔ (f x ≠ b ∧ (ρ γ).val < vfValue (f x-b))
  rw [and_iff_right hx.1,and_iff_right hfx]
  change γ < finiteValue (x-a) (sub_ne_zero.mpr hx.1) ↔
    ρ γ < finiteValue (f x-b) (sub_ne_zero.mpr hfx)
  rw [he]
  exact ρ.lt_iff_lt.symm

theorem punctured_disc_images_of_value_law
    (f : VF M → VF M) (A B : Set (VF M)) (hbij : Set.BijOn f A B)
    (a b : VF M) (ρ : Gamma M ≃o Gamma M) (η : Gamma M)
    (hlaw : PuncturedValueLaw f a b ρ η)
    (hinverse : ∃ ζ : Gamma M, puncturedGammaDisc b ζ ⊆ B ∧
      ∀ x ∈ A, f x ∈ puncturedGammaDisc b ζ → x ∈ puncturedGammaDisc a η) :
    ∃ γ₀ : Gamma M, ∀ γ : Gamma M, γ₀ ≤ γ →
      f '' puncturedGammaDisc a γ = puncturedGammaDisc b (ρ γ) := by
  obtain ⟨ζ,hζB,hpre⟩ := hinverse
  refine ⟨max η (ρ.symm ζ),fun γ hγ => ?_⟩
  have hηγ : η ≤ γ := (le_max_left _ _).trans hγ
  have hζδ : ζ ≤ ρ γ := by
    have hh := ρ.monotone ((le_max_right η (ρ.symm ζ)).trans hγ)
    simpa only [ρ.apply_symm_apply] using hh
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact (hlaw.disc_iff x (puncturedGammaDisc_anti a hηγ hx) γ).mp hx
  · intro y hy
    have hyζ := puncturedGammaDisc_anti b hζδ hy
    obtain ⟨x,hxA,hxy⟩ := hbij.surjOn (hζB hyζ)
    have hfxζ : f x ∈ puncturedGammaDisc b ζ := hxy.symm ▸ hyζ
    have hxη := hpre x hxA hfxζ
    exact ⟨x,(hlaw.disc_iff x hxη γ).mpr (hxy.symm ▸ hy),hxy⟩

end DiamondIntegral.Section2
