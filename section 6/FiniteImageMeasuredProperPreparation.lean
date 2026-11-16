import «section 6».FiniteImageMeasuredPreparation

/-! Finite-image measured preparation from arbitrary proper invariant
sources. The actual preliminary map, exact form and all literal protected
restrictions are retained; no RV-pullback hypothesis is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finite_image_measured_proper_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (hC : ∀ i,ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (hFinite : ω.image.carrier.Finite)
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A C hCA ω) := by
  obtain ⟨s,A₀,f₀,hf₀,hA₀,hA₀D,hA₀RV,hPieces₀⟩ := proper_preparation
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hCA hC
  let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
  have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₀ ⟨p.val,hCA i p.property⟩).property
  have hC₀ (i) : ProperInvariant S (C₀ i).carrier := by
    have h := (hPieces₀ i).1.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective
  let ω₀ := ω.comp (f₀.inverse (hf₀.bijective h00))
  have hTransport₀ (p : A) : (ω₀ (f₀ p)).val=(ω p).val := by
    change (ω (f₀.inverse (hf₀.bijective h00) (f₀ p))).val=_
    rw [Map.inverse_apply]
  have hFinite₀ : ω₀.image.carrier.Finite := hFinite.subset (by
    rintro γ ⟨q,hq⟩
    exact ⟨f₀.inverse (hf₀.bijective h00) q,hq⟩)
  have hLevels₀ := hf₀.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels ω₀ hTransport₀
  obtain ⟨T⟩ := finite_image_measured_preparation h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    A₀ hA₀ hA₀D hA₀RV C₀ hC₀A₀ hC₀ ω₀ hFinite₀ hLevels₀
  exact ⟨T.precompose h00 C hCA f₀ hf₀ (fun i => (hPieces₀ i).1) hC₀A₀ ω ω₀ hTransport₀⟩

end DiamondIntegral.Section6
