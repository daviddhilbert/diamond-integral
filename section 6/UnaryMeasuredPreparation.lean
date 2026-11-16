import «section 6».UnaryMeasuredProperPreparation

/-! Complete unary measured preparation of an arbitrary proper source,
with an actual transported Gamma map and all finite protected images.
The initial unmeasured preparation is followed by the measured root
construction; the source need not already be an RV-pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

theorem unary_measured_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    Nonempty (UnaryMeasuredPreparation (G := G) A C hCA ω) := by
  obtain ⟨s,A₀,f₀,hf₀,hA₀,hA₀D,hA₀RV,hPieces₀⟩ := unary_proper_preparation
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hCA hC
  let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
  have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₀ ⟨p.val,hCA i p.property⟩).property
  have hC₀ (i) : ProperInvariant S (C₀ i).carrier := by
    have hHomeo := (hPieces₀ i).1.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    exact hHomeo.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHomeo.bijective.surjective
  have hBij₀ := hf₀.bijective h00
  let ω₀ := ω.comp (f₀.inverse hBij₀)
  have hGeometry₀ := hf₀.gamma_levels_proper_geometry h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  have hLevels₀ (u γ) : IsOpen {a : Fin 1 → VF M | (a,u) ∈ A₀.carrier ∧ gammaFormExtension ω₀ (a,u) = γ} :=
    ((hGeometry₀ γ).clopen_fibres hv u).isOpen
  obtain ⟨T⟩ := unary_measured_preparation_of_rvPullback h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt A₀ hA₀ hA₀RV C₀ hC₀A₀ hC₀ ω₀ hLevels₀
  have hTransport₀ (p : A) : (ω₀ (f₀ p)).val = (ω p).val := by
    change (ω (f₀.inverse hBij₀ (f₀ p))).val = (ω p).val
    rw [Map.inverse_apply]
  exact ⟨T.precompose h00 C hCA f₀ hf₀ (fun i => (hPieces₀ i).1) hC₀A₀ ω ω₀ hTransport₀⟩

end DiamondIntegral.Section6
