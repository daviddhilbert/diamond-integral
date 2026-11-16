import «section 6».RegularizedLoci

/-! Lemma 6.14 with the author's approved almost-everywhere conclusion.
The finite chain consists of actual same-base definable operations,
including preliminary zero-centered translations. No preparation or
lifting theorem is assumed to construct these operations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}

theorem vf_charZero_of_model00 (h00 : M ⊨ Axioms.ACVF00) : CharZero (VF M) := by
  apply charZero_of_inj_zero
  intro k hk
  by_contra hn
  have hv := Barycentre.natCast_value_one Values.presentationValuation Values.presentation_compatible h00 k hn
  rw [hk,map_zero] at hv
  exact zero_ne_one hv

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Every finite special covariant chain is a proper covariant
homeomorphism, with a full total derivative of determinant one outside
an original-base definable VF-small set. Arity zero has no exceptions. -/
theorem lemma_6_14
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : SpecialCovariantChain (G := G) A B f) :
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
  · exact h.unit_derivative_ae h00 hc hκ.le hs hsmall hv

end DiamondIntegral.Section6
