import «section 6».TransportedGammaLevels

/-! One original-base named radius makes every Gamma level invariant,
including ambient membership. No individual Gamma level is assumed to
be definable over S and no finite enumeration of levels is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r : ℕ} {S : Set M}

theorem gamma_form_all_levels_uniform_invariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (ω : Mixed M n r → Gamma M)
    (hGraph : S.Definable LRV (mixedGammaGraph A ω))
    (hLevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A ∧ ω (a,u) = γ}) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ 1 ≤ δ ∧
      (∀ u, AlphaInvariant (fun _ => δ) (vfFibre A u)) ∧
      ∀ γ u, AlphaInvariant (fun _ => δ) (vfFibre {p | p ∈ A ∧ ω p = γ} u) := by
  obtain ⟨α,hα,hα1,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA
  obtain ⟨β,hβ,hβ1,hConst⟩ := gammaFunction_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA ω hGraph hLevels
  have hAmbient (u) : AlphaInvariant (fun _ => max α β) (vfFibre A u) :=
    (hInv u).larger_radius (fun _ => le_max_left α β)
  refine ⟨max α β,gamma_max_named α β hα hβ,hα1.trans (le_max_left _ _),hAmbient,?_⟩
  intro γ u x y hxy
  have hFormClose : Congruent (fun _ => β) x y := hxy.of_larger_radius (fun _ => le_max_right α β)
  constructor
  · rintro ⟨hx,hγ⟩
    have hy := (hAmbient u x y hxy).mp hx
    exact ⟨hy,(hConst u x hx y hy hFormClose).symm.trans hγ⟩
  · rintro ⟨hy,hγ⟩
    have hx := (hAmbient u x y hxy).mpr hy
    exact ⟨hx,(hConst u x hx y hy hFormClose).trans hγ⟩

end DiamondIntegral.Section6
