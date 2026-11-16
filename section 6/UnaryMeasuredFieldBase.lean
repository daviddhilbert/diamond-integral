import «section 6».UnaryMeasuredContraction

/-! Unary measured preparation over the actual VF-generated field base,
including the finite proper partition formulation. Standing nontriviality,
smallness and saturation remain explicit. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ}

theorem unary_measured_preparation_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M)) (hA : ProperInvariant (S : Set M) A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hLevels : ∀ γ, ProperInvariantGeometry {p | p ∈ A.carrier ∧ gammaFormExtension ω p = γ}) :
    Nonempty (UnaryMeasuredPreparation (G := G) A C hCA ω) := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B₀ hnt
  exact unary_measured_preparation h00 hc linear hκ hs hv (vfFieldNames B₀.field) hsmall hΓ
    hV hVS hSV hnt' A hA C hCA hC ω (fun u γ => ((hLevels γ).clopen_fibres hv u).isOpen)

theorem unary_measured_partition_preparation_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier)
    (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M 1 r → Gamma M) (hGraph : (S : Set M).Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    Nonempty (UnaryMeasuredPreparation (G := G) A C hCA (gammaFormMap A ω hGraph)) := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B₀ hnt
  exact unary_measured_partition_preparation h00 hc linear hκ hs hv (vfFieldNames B₀.field) hsmall hΓ
    hV hVS hSV hnt' A C hCA hC hCover ω hGraph hLevels

end DiamondIntegral.Section6
