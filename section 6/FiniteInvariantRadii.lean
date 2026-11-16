import «section 6».UniformMixedRadius

/-! One original-base named invariant radius for a finite family of
proper invariant sets. This supplies the common aperture constraint for
the ambient set and every protected partition piece. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}

theorem gamma_one_named (hc : CanonicalStructure.IsCanonical (M := M)) :
    S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {(1 : Gamma M)}} := by
  apply (gamma_real_codes_iff hc S _).mp
  exact GammaParameters.real_definableAtBase (⟨S,∅⟩ : ParameterBase M) .rv _ (GammaSyntax.one_definable S)

theorem gamma_max_named (a b : Gamma M)
    (ha : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {a}})
    (hb : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {b}}) :
    S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {max a b}} := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

theorem finite_named_gamma_bound (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Fin k → Gamma M)
    (hf : ∀ i, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {f i}}) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      (1 : Gamma M) ≤ δ ∧ ∀ i, f i ≤ δ := by
  induction k with
  | zero => exact ⟨1,gamma_one_named hc,le_rfl,fun i => i.elim0⟩
  | succ k ih =>
      obtain ⟨δ,hδ,hδ0,hδf⟩ := ih (Fin.tail f) (fun i => hf i.succ)
      refine ⟨max δ (f 0),gamma_max_named _ _ hδ (hf 0),hδ0.trans (le_max_left _ _),?_⟩
      intro i
      refine Fin.cases (le_max_right _ _) (fun i => (hδf i).trans (le_max_left _ _)) i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finite_properInvariant_uniform_named_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (H : Fin k → Set (Mixed M n r)) (hH : ∀ i, ProperInvariant S (H i)) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      (1 : Gamma M) ≤ δ ∧ ∀ i u, AlphaInvariant (fun _ => δ) (vfFibre (H i) u) := by
  classical
  have hex (i) := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ (hH i)
  let f (i : Fin k) := (hex i).choose
  have hf (i) : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {f i}} := (hex i).choose_spec.1
  obtain ⟨δ,hδ,hδ0,hbound⟩ := finite_named_gamma_bound hc f hf
  refine ⟨δ,hδ,hδ0,fun i u => ?_⟩
  exact ((hex i).choose_spec.2.2 u).larger_radius (fun _ => hbound i)

end DiamondIntegral.Section6
