import «section 6».DiamondSurjectivity
import «section 6».RelativeApertureChains

/-! Remark 6.15 (`spec:is:iso`): a special covariant bijection between objects
of `μVF^◇[n]` whose forms agree outside a definable set of VF-dimension `< n`
is a morphism of `μVF^◇[n]`.

This holds for the revised bounded variable-aperture class of Definition 6.11
(`RelativeApertureChain`, which contains the original special covariant
chains): such chains factor into relatively unary proper covariant
homeomorphisms, and have unit derivative at VF-generic points (Lemma 6.14), so
the measure identity reduces to the agreement of the forms; generic points
avoid the exceptional set. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondSpecialIsomorphisms
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid DiamondIntegral.Section6.DiamondSurjectivity

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Chains in the revised class of Definition 6.11 factor into relatively
unary proper covariant homeomorphisms. -/
theorem relative_factor (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    (H : RelativeApertureChain (G := G) A B f) : UnaryFactorization G A B f := by
  induction H with
  | original h => exact special_factor h00 hc linear hκ hs hv hsmall hΓ h
  | relative A D =>
    refine UnaryFactorization.step (D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ)
      (Or.inr ⟨D.coordinate, D.coordinate, VFUnaryRelativeAt.relativelyUnary (fun p j hj => ?_)⟩)
    change (D.point p.val).1 j = p.val.1 j
    exact Function.update_of_ne hj _ _
  | comp _ _ ihf ihg => exact UnaryFactorization.comp ihf ihg

/-- Remark 6.15: a chain in the revised special class between objects of
`μVF^◇[n]`, with the forms agreeing outside a definable set of VF-dimension
`< n` (or everywhere in degree zero), is a morphism of `μVF^◇[n]`. -/
theorem remark_6_15 (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {A B : VFObject (M := M) S n} (F : Map A.carrier B.carrier)
    (H : RelativeApertureChain (G := G) A.carrier B.carrier F)
    (E : DefSet (rawMixedSpace (M := M) n A.labels) S)
    (hE : vfDim (rawRVSpace (M := M) 1) E < n ∨ E.carrier = ∅)
    (hform : ∀ p : A.carrier, p.val ∉ E.carrier → gammaMapValue A.form p = gammaMapValue B.form (F p)) :
    Nonempty (Morphism G A B) := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  refine morphism_of_generic h00 hc hs hsmall F (H.bijective h00)
    (relative_factor h00 hc linear hκ hs hv hsmall hΓ H) (fun p hp => ?_)
  obtain ⟨L, hL, hdet⟩ := H.unit_derivative_of_independent h00 hc hκ.le hs hsmall hv p hp
  have hpE : p.val ∉ E.carrier := by
    rcases hE with h | h
    · exact not_mem_small_set_of_independent hc E h p.val hp
    · rw [h]
      exact Set.notMem_empty _
  refine ⟨L, hL, ?_⟩
  rw [hdet, hform p hpE, div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one, map_one]

end DiamondIntegral.Section6.DiamondSpecialIsomorphisms
