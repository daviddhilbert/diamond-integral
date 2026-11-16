import «section 6».BinaryRootIteration

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

theorem binary_preparation_of_doublyBounded_tagged
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
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier) :
    ∃ t : ℕ, ∃ Z : DefSet (rawMixedSpace (M := M) 2 t) S, ∃ g : Map A Z,
      SpecialCovariantChain (G := G) A Z g ∧ ProperInvariant S Z.carrier ∧
      VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image
        (g.restrict (hPA i)).toImage ∧ IsRVPullback (g.restrict (hPA i)).image.carrier := by
  obtain ⟨R,N,hN,hControl⟩ := exists_finite_controlling_coordinate_roots hc hs hsmall hv A hARV P
  exact binary_preparation_of_root_bound h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt N
    A hA hAD hARV htag j hHead R hN P hPA hP hControl

/-- The complete binary case of Proposition 6.19, without initial
double bounds, regularization or a supplied root family. -/
theorem lemma_6_19_binary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 2 s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier := by
  obtain ⟨A₀,f₀,hf₀,hA₀,hA₀D,hA₀RV,htag₀,hPieces₀⟩ := exists_initial_preparation_protecting_family
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hCA hC
  let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
  have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₀ ⟨p.val,hCA i p.property⟩).property
  let A₁ := (regularizeMap A₀).image
  let f₁ := regularization A₀
  let C₁ (i) := (f₁.restrict (hC₀A₀ i)).image
  have hC₀ (i) : ProperInvariant S (C₀ i).carrier := (hPieces₀ i).2
  have hC₀D (i) : VFDoublyBounded (C₀ i).carrier := by
    obtain ⟨γ,hγ⟩ := hA₀D
    exact ⟨γ,fun p hp => hγ p (hC₀A₀ i hp)⟩
  have hf₁ : SpecialCovariantChain (G := G) A₀ A₁ f₁ := .regularize A₀ hA₀ hA₀D
  have hP₁ (i) := regularization_restriction_chain (G := G) h00 (hC₀A₀ i) (hC₀ i) (hC₀D i)
  have hC₁A₁ (i) : (C₁ i).carrier ⊆ A₁.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₁ ⟨p.val,hC₀A₀ i p.property⟩).property
  have hC₁ (i) : ProperInvariant S (C₁ i).carrier := by
    have h := (hP₁ i).properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective
  have hA₁ : ProperInvariant S A₁.carrier := regularization_properInvariant h00 hc hκ hs hv _ hA₀ hA₀D
  have htag₁ : ∀ p ∈ A₁.carrier, ∀ q ∈ A₁.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
    rw [show A₁.carrier = regularize '' A₀.carrier from regularization_carrier _]
    exact regularized_tagged _
  let j : Fin (2+(2+(2+r))) := Fin.castAdd (2+(2+r)) (Fin.last 1)
  have hHead (p : Mixed M 2 (2+(2+(2+r)))) (hp : p ∈ A₁.carrier) : rv M (p.1 (Fin.last 1)) = p.2 j := by
    obtain ⟨a,ha⟩ := hp
    rw [← ha]
    change rv M ((regularize a.val).1 (Fin.last 1)) = (regularize a.val).2 j
    simp only [j,regularize,Fin.append_left,Section2.tupleRV]
  obtain ⟨s,B,f,hf,hB,hBD,hBRV,hPieces⟩ := binary_preparation_of_doublyBounded_tagged
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A₁ hA₁ (regularized_vfDoublyBounded hA₀D)
    (regularization_rvPullback _ (hA₀RV hARV)) htag₁ j hHead C₁ hC₁A₁ hC₁
  let g := (f.comp f₁).comp f₀
  refine ⟨s,B,g,.comp hf₀ (.comp hf₁ hf),hB,hBD,hBRV,fun i => ?_⟩
  have hComp := SpecialCovariantChain.comp (.comp (hPieces₀ i).1 (hP₁ i)) (hPieces i).1
  have hImage : (f.restrict (hC₁A₁ i)).image = (g.restrict (hCA i)).image :=
    image_eq_of_surjective_liesOver g
      ((f.restrict (hC₁A₁ i)).toImage.comp
        ((f₁.restrict (hC₀A₀ i)).toImage.comp (f₀.restrict (hCA i)).toImage))
      (hComp.bijective h00).surjective (hCA i) (fun _ => rfl)
  exact ⟨hComp.restriction_of_liesOver h00 g (hCA i) (fun _ => rfl),hImage ▸ (hPieces i).2⟩

end DiamondIntegral.Section6
