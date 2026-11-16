import «section 6».FiniteImageMeasuredExistence

/-! The finite-image case of 6.21 in every positive VF degree over the
actual VF-generated field base, with all literal selected-piece lifts. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r k : ℕ}

theorem lemma_6_21_finite_image_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) (S : Set M))
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier)
    (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M (n+1) r → Gamma M) (hGraph : (S : Set M).Definable LRV (mixedGammaGraph A.carrier ω))
    (hFinite : (gammaFormMap A ω hGraph).image.carrier.Finite)
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin (n+1) → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B₀ hnt
  exact lemma_6_21_finite_image h00 hc linear hκ hs hv (vfFieldNames B₀.field) hsmall hΓ
    hV hVS hSV hnt' A C hCA hC hCover ω hGraph hFinite hLevels

end DiamondIntegral.Section6
