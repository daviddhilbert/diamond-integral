import «section 6».ZeroCenteredHomeomorphism

/-! Finite chains of the actual Definition 6.11 operations. The index
retains every changing RV arity and the same original parameter base.
The permitted preliminary zero-centered translation is included explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive SpecialCovariantChain : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B → Prop where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) : SpecialCovariantChain A A (Map.id A)
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier) :
      SpecialCovariantChain A (regularizeMap A).image (regularization A)
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A) :
      SpecialCovariantChain A D.map.image D.bijection
  | zeroCentered (A : DefSet (rawMixedSpace (M := M) n r) S) (D : ZeroCenteredData A) :
      SpecialCovariantChain A D.map.image D.bijection
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S}
      {C : DefSet (rawMixedSpace (M := M) n t) S}
      {f : Map A B} {g : Map B C} (hf : SpecialCovariantChain A B f) (hg : SpecialCovariantChain B C g) :
      SpecialCovariantChain A C (g.comp f)

namespace SpecialCovariantChain

variable {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}

theorem bijective (h : SpecialCovariantChain (G := G) A B f) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective f := by
  induction h with
  | identity => exact Function.bijective_id
  | regularize => exact regularization_bijective _
  | centripetal A D => exact D.bijective h00
  | zeroCentered A D => exact D.bijective h00
  | comp hf hg ihf ihg => exact ihg.comp ihf

theorem properHomeomorphism (h : SpecialCovariantChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) : ProperCovariantHomeomorphism f := by
  induction h with
  | identity A hA => exact identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ hA
  | regularize A hA hVF => exact regularization_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ A hA hVF
  | centripetal A D => exact D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  | zeroCentered A D => exact D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  | comp hf hg ihf ihg => exact lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ ihf ihg

theorem unit_derivative_of_independent [CharZero (VF M)]
    (h : SpecialCovariantChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (p : A) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) : HasMixedUnitDerivativeAt f p := by
  induction h with
  | identity A hA => exact identity_unit_derivative hA p
  | regularize A hA hVF => exact regularization_unit_derivative A hA hVF p
  | centripetal A D =>
      exact mixed_unit_derivative_of_shear_chart D.bijection p D.coordinate
        (D.branchFocus p.val.2 (D.core p.val)) (D.shear_chart hv p)
        (mixedDifferentiableAt_of_independent hc hκ hs hsmall hv D.bijection p hp)
  | zeroCentered A D => exact D.unit_derivative hv p
  | @comp r s t A B C f g hf hg ihf ihg =>
      exact (ihg (f p) (independent_map_of_finiteFibres hc f
        (Map.finiteFibres_of_injective (hf.bijective h00).injective) p hp)).comp (ihf p hp)

theorem unit_derivative_ae [CharZero (VF M)] (h : SpecialCovariantChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p :=
  exists_mixed_unit_derivative_exception hc hs hsmall hn f
    (h.unit_derivative_of_independent h00 hc hκ hs hsmall hv)

theorem unit_derivative_zero_arity [CharZero (VF M)] {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) 0 r) S} {B : DefSet (rawMixedSpace (M := M) 0 s) S}
    {f : Map A B} (h : SpecialCovariantChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : A) :
    HasMixedUnitDerivativeAt f p :=
  h.unit_derivative_of_independent h00 hc hκ hs hsmall hv p algebraicIndependent_empty_type

end SpecialCovariantChain
end DiamondIntegral.Section6
