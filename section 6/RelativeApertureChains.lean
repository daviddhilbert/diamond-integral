import «section 6».RelativeApertureHomeomorphism
import «section 6».SpecialCovariantRestrictions

/-! Finite arbitrary-arity chains for the revised bounded variable-aperture
Definition 6.11. The original scalar chain is retained as a subclass.
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive RelativeApertureChain : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B → Prop where
  | original {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
      (h : SpecialCovariantChain (G := G) A B f) : RelativeApertureChain A B f
  | relative (A : DefSet (rawMixedSpace (M := M) n r) S) (D : RelativeApertureData (G := G) A) :
      RelativeApertureChain A D.map.image D.bijection
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S}
      {C : DefSet (rawMixedSpace (M := M) n t) S} {f : Map A B} {g : Map B C}
      (hf : RelativeApertureChain A B f) (hg : RelativeApertureChain B C g) :
      RelativeApertureChain A C (g.comp f)

namespace RelativeApertureChain
variable {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}

theorem bijective (h : RelativeApertureChain (G := G) A B f) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective f := by
  induction h with
  | original h => exact h.bijective h00
  | relative A D => exact D.bijective h00
  | comp hf hg ihf ihg => exact ihg.comp ihf

theorem properHomeomorphism (h : RelativeApertureChain (G := G) A B f)
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
    (h : RelativeApertureChain (G := G) A B f)
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
    (h : RelativeApertureChain (G := G) A B f) (hn : 0<n)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E<n ∧
      ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p :=
  exists_mixed_unit_derivative_exception hc hs hsmall hn f
    (h.unit_derivative_of_independent h00 hc hκ hs hsmall hv)

theorem changeTarget {C : DefSet (rawMixedSpace (M := M) n s) S} {g : Map A C}
    (hBC : B=C) (hpoint : ∀ p : A,(f p).val=(g p).val)
    (h : RelativeApertureChain (G := G) A B f) : RelativeApertureChain (G := G) A C g := by
  subst C
  have he : f=g := Map.ext (fun p => Subtype.ext (hpoint p))
  simpa only [he] using h

end RelativeApertureChain
/-- Lemma 6.14 for the applied bounded variable-aperture definition. -/
theorem lemma_6_14_bounded_variable_apertures
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : RelativeApertureChain (G := G) A B f) :
    ProperCovariantHomeomorphism f ∧
      (n = 0 → ∀ p : A, HasMixedUnitDerivativeAt f p) ∧
      (0 < n → ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
        vfDim (rawRVSpace (M := M) 1) E < n ∧
        ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p) := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  refine ⟨h.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ,?_,?_⟩
  · intro hn p
    haveI : IsEmpty (Fin n) := ⟨fun i => by
      have hi : i.val < 0 := hn ▸ i.isLt
      exact (Nat.not_lt_zero i.val) hi⟩
    exact h.unit_derivative_of_independent h00 hc hκ.le hs hsmall hv p algebraicIndependent_empty_type
  · intro hn
    exact h.unit_derivative_ae hn h00 hc hκ.le hs hsmall hv

end DiamondIntegral.Section6
