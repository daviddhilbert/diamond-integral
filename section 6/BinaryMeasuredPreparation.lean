import «section 6».BinaryArbitraryProperPreparation

/-! Complete two-dimensional proper preparation over the original
base: actual finite obstacles, terminating root iteration, and the
common protected preliminary preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_measured_preparation_of_doublyBounded_tagged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (j : Fin r) (hHead : ∀ p ∈ A.carrier, rv M (p.1 (Fin.last 1)) = p.2 j)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A P hPA ω) := by
  obtain ⟨R,N,hN,hControl,hForm⟩ := exists_coordinate_measured_controlling_roots hc hs hsmall hv A hARV P ω
  exact binary_measured_preparation_of_root_bound h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt N
    A hA hAD hARV htag j hHead R hN P hPA hP hControl ω hLevels hForm

theorem binary_measured_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A C hCA ω) := by
  obtain ⟨s,A₀,f₀,hf₀,hA₀,hA₀D,hA₀RV,hPieces₀⟩ := binary_proper_preparation
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hCA hC
  let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
  have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₀ ⟨p.val,hCA i p.property⟩).property
  have hC₀ (i) : ProperInvariant S (C₀ i).carrier := by
    have h := (hPieces₀ i).1.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective
  have hC₀D (i) : VFDoublyBounded (C₀ i).carrier := by
    obtain ⟨γ,hγ⟩ := hA₀D
    exact ⟨γ,fun p hp => hγ p (hC₀A₀ i hp)⟩
  let ω₀ := ω.comp (f₀.inverse (hf₀.bijective h00))
  have hTransport₀ (p : A) : (ω₀ (f₀ p)).val = (ω p).val := by
    change (ω (f₀.inverse (hf₀.bijective h00) (f₀ p))).val = _
    rw [Map.inverse_apply]
  have hLevels₀ := hf₀.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels ω₀ hTransport₀
  let A₁ := (regularizeMap A₀).image
  let f₁ := regularization A₀
  let C₁ (i) := (f₁.restrict (hC₀A₀ i)).image
  have hf₁ : SpecialCovariantChain (G := G) A₀ A₁ f₁ := .regularize A₀ hA₀ hA₀D
  have hP₁ (i) := regularization_restriction_chain (G := G) h00 (hC₀A₀ i) (hC₀ i) (hC₀D i)
  have hC₁A₁ (i) : (C₁ i).carrier ⊆ A₁.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₁ ⟨p.val,hC₀A₀ i p.property⟩).property
  have hC₁ (i) : ProperInvariant S (C₁ i).carrier := by
    have h := (hP₁ i).properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective
  let ω₁ := ω₀.comp (f₁.inverse (hf₁.bijective h00))
  have hTransport₁ (p : A₀) : (ω₁ (f₁ p)).val = (ω₀ p).val := by
    change (ω₀ (f₁.inverse (hf₁.bijective h00) (f₁ p))).val = _
    rw [Map.inverse_apply]
  have hLevels₁ := hf₁.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω₀ hLevels₀ ω₁ hTransport₁
  have hA₁ : ProperInvariant S A₁.carrier := regularization_properInvariant h00 hc hκ hs hv _ hA₀ hA₀D
  have hTag₁ : ∀ p ∈ A₁.carrier, ∀ q ∈ A₁.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
    rw [show A₁.carrier = regularize '' A₀.carrier from regularization_carrier _]
    exact regularized_tagged _
  let j : Fin (2+s) := Fin.castAdd s (Fin.last 1)
  have hHead (p : Mixed M 2 (2+s)) (hp : p ∈ A₁.carrier) : rv M (p.1 (Fin.last 1)) = p.2 j := by
    obtain ⟨a,ha⟩ := hp
    rw [← ha]
    change rv M ((regularize a.val).1 (Fin.last 1)) = (regularize a.val).2 j
    simp only [j,regularize,Fin.append_left,Section2.tupleRV]
  obtain ⟨T⟩ := binary_measured_preparation_of_doublyBounded_tagged h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt A₁ hA₁ (regularized_vfDoublyBounded hA₀D) (regularization_rvPullback _ hA₀RV)
    hTag₁ j hHead C₁ hC₁A₁ hC₁ ω₁ hLevels₁
  let T₀ := T.precompose h00 C₀ hC₀A₀ f₁ hf₁ hP₁ hC₁A₁ ω₀ ω₁ hTransport₁
  exact ⟨T₀.precompose h00 C hCA f₀ hf₀ (fun i => (hPieces₀ i).1) hC₀A₀ ω ω₀ hTransport₀⟩

end DiamondIntegral.Section6
