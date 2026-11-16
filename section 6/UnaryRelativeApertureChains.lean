import «section 6».UnaryRelativeApertureHomeomorphism
import «section 6».SpecialCovariantRestrictions

/-! Finite auxiliary unary chains admitting the separately constructed
variable endpoint primitive. The original scalar chain remains unchanged.
Every auxiliary chain is an actual proper covariant homeomorphism with
unit total derivative outside a definable lower-dimensional set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive UnaryRelativeApertureChain : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) →
    (B : DefSet (rawMixedSpace (M := M) 1 s) S) → Map A B → Prop where
  | original {A : DefSet (rawMixedSpace (M := M) 1 r) S}
      {B : DefSet (rawMixedSpace (M := M) 1 s) S} {f : Map A B}
      (h : SpecialCovariantChain (G := G) A B f) : UnaryRelativeApertureChain A B f
  | relative (A : DefSet (rawMixedSpace (M := M) 1 r) S) (D : UnaryRelativeApertureData A) :
      UnaryRelativeApertureChain A D.map.image D.bijection
  | comp {A : DefSet (rawMixedSpace (M := M) 1 r) S}
      {B : DefSet (rawMixedSpace (M := M) 1 s) S}
      {C : DefSet (rawMixedSpace (M := M) 1 t) S} {f : Map A B} {g : Map B C}
      (hf : UnaryRelativeApertureChain A B f) (hg : UnaryRelativeApertureChain B C g) :
      UnaryRelativeApertureChain A C (g.comp f)

namespace UnaryRelativeApertureChain
variable {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {B : DefSet (rawMixedSpace (M := M) 1 s) S} {f : Map A B}

theorem bijective (h : UnaryRelativeApertureChain (G := G) A B f) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective f := by
  induction h with
  | original h => exact h.bijective h00
  | relative A D => exact D.bijective h00
  | comp hf hg ihf ihg => exact ihg.comp ihf

theorem properHomeomorphism (h : UnaryRelativeApertureChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) : ProperCovariantHomeomorphism f := by
  induction h with
  | original h => exact h.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  | relative A D => exact D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  | comp hf hg ihf ihg => exact lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ ihf ihg

theorem unit_derivative_of_independent [CharZero (VF M)]
    (h : UnaryRelativeApertureChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (p : A) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) : HasMixedUnitDerivativeAt f p := by
  induction h with
  | original h => exact h.unit_derivative_of_independent h00 hc hκ hs hsmall hv p hp
  | relative A D =>
      exact mixed_unit_derivative_of_shear_chart D.bijection p D.coordinate
        (D.branchFocus p.val.2 (D.core p.val)) (D.shear_chart hv p)
        (mixedDifferentiableAt_of_independent hc hκ hs hsmall hv D.bijection p hp)
  | @comp r s t A B C f g hf hg ihf ihg =>
      exact (ihg (f p) (independent_map_of_finiteFibres hc f
        (Map.finiteFibres_of_injective (hf.bijective h00).injective) p hp)).comp (ihf p hp)

theorem unit_derivative_ae [CharZero (VF M)]
    (h : UnaryRelativeApertureChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ E : DefSet (rawMixedSpace (M := M) 1 r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E<1 ∧
      ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p :=
  exists_mixed_unit_derivative_exception hc hs hsmall (by decide : 0<1) f
    (h.unit_derivative_of_independent h00 hc hκ hs hsmall hv)

theorem changeTarget {C : DefSet (rawMixedSpace (M := M) 1 s) S} {g : Map A C}
    (hBC : B=C) (hpoint : ∀ p : A,(f p).val=(g p).val)
    (h : UnaryRelativeApertureChain (G := G) A B f) : UnaryRelativeApertureChain (G := G) A C g := by
  subst C
  have he : f=g := Map.ext (fun p => Subtype.ext (hpoint p))
  simpa only [he] using h

end UnaryRelativeApertureChain
end DiamondIntegral.Section6
