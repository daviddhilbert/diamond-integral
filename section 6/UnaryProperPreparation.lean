import «section 6».ProtectedInitialPreparation

/-! The complete unary base case of Proposition 6.19, without extra
regularization or double-boundedness hypotheses on the source. The
initial preparation protects the same family over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The full unary case of Proposition 6.19. A finite proper invariant
family is prepared simultaneously, with its actual special restrictions. -/
theorem lemma_6_19_unary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier := by
  obtain ⟨A₀,f₀,hf₀,hA₀,hA₀D,hA₀RV,htag₀,hPieces₀⟩ := exists_initial_preparation_protecting_family
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hCA hC
  let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
  let g₀ (i : Fin k) := (f₀.restrict (hCA i)).toImage
  have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₀ ⟨p.val,hCA i p.property⟩).property
  have hC₀ (i) : ProperInvariant S (C₀ i).carrier := (hPieces₀ i).2
  obtain ⟨s,B,f,hf,hB,hBD,hBRV,hPieces⟩ := unary_proper_preparation_of_doublyBounded_tagged
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A₀ hA₀ hA₀D (hA₀RV hARV) htag₀ C₀ hC₀A₀ hC₀
  refine ⟨s,B,f.comp f₀,.comp hf₀ hf,hB,hBD,hBRV,fun i => ?_⟩
  have hg : SpecialCovariantChain (G := G) (C i) (f.restrict (hC₀A₀ i)).image
      ((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) := .comp (hPieces₀ i).1 (hPieces i).1
  have hpoint (p : C i) :
      (((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) p).val = ((f.comp f₀) ⟨p.val,hCA i p.property⟩).val := rfl
  have he := image_eq_of_surjective_liesOver (f.comp f₀)
    ((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) (hg.bijective h00).surjective (hCA i) hpoint
  exact ⟨hg.restriction_of_liesOver h00 (f.comp f₀) (hCA i) hpoint,by rw [← he]; exact (hPieces i).2⟩

/-- Unary proper preparation for an arbitrary proper invariant source,
using its actual RV hull and preparing source membership as well. -/
theorem unary_proper_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier := by
  let H : DefSet (rawMixedSpace (M := M) 1 r) S := ⟨rvHull A.carrier,hA.rvHull.definable⟩
  let D : Fin (k+1) → DefSet (rawMixedSpace (M := M) 1 r) S := Fin.cons A C
  have hDH : ∀ i, (D i).carrier ⊆ H.carrier := Fin.cases (subset_rvHull A.carrier)
    (fun i => (hCA i).trans (subset_rvHull A.carrier))
  have hD : ∀ i, ProperInvariant S (D i).carrier := Fin.cases hA hC
  obtain ⟨s,B,f,hf,hB,hBD,hBRV,hPieces⟩ := lemma_6_19_unary h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt H hA.rvHull (rvHull_idempotent A.carrier) D hDH hD
  let B' := (f.restrict (hDH 0)).image
  let f' := (f.restrict (hDH 0)).toImage
  have hf' : SpecialCovariantChain (G := G) A B' f' := (hPieces 0).1
  have hHomeo := hf'.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  have hB' : ProperInvariant S B'.carrier := hHomeo.covariant.target_properInvariant
    h00 hc linear hκ hs hv hsmall hΓ hHomeo.bijective.surjective
  have hB'sub : B'.carrier ⊆ B.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f ⟨p.val,hDH 0 p.property⟩).property
  have hB'D : VFDoublyBounded B'.carrier := by
    obtain ⟨γ,hγ⟩ := hBD
    exact ⟨γ,fun q hq => hγ q (hB'sub hq)⟩
  refine ⟨s,B',f',hf',hB',hB'D,(hPieces 0).2,fun i => ?_⟩
  let g := (f.restrict (hDH i.succ)).toImage
  have hg : SpecialCovariantChain (G := G) (C i) (f.restrict (hDH i.succ)).image g := (hPieces i.succ).1
  have hpoint (p : C i) : (g p).val = (f' ⟨p.val,hCA i p.property⟩).val := rfl
  have he := image_eq_of_surjective_liesOver f' g (hg.bijective h00).surjective (hCA i) hpoint
  exact ⟨hg.restriction_of_liesOver h00 f' (hCA i) hpoint,by rw [← he]; exact (hPieces i.succ).2⟩

end DiamondIntegral.Section6
