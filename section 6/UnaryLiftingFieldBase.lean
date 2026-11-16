import «section 6».MixedDerivativeContinuity

/-! Literal unary lifting over the manuscript's actual VF-generated
field base. No abstract Gamma-generation or closure-smallness premise
is substituted for the field-base convention. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_6_30_vfGenerated
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (R : M → M → Prop)
    (hR : (S : Set M).Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))})
    (hFin : ∀ u, {v | R u v}.Finite)
    (hRV : ∀ u v, R u v → iRV v) (hNonzero : ∀ u v, R u v → u ≠ iRVZero) :
    Nonempty (UnaryFinitaryLift R hR) := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B₀ hnt
  exact lemma_6_30 hc h00 hκ hs hv (vfFieldNames B₀.field) (S : Set M)
    hV hVS hSV hnt' hsmall R hR hFin hRV hNonzero

end DiamondIntegral.Section6
