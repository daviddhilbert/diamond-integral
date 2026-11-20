import «section 7».Lemma720EHU

/-! Lemma 7.20, step 14: definability of the uniform cell data over the base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace Final
variable {B : DefSet (rawMixedSpace (M := M) 1 a) S} (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
  (lead : Fin a) (Q : Finset (VF M)) (T₂ : StandardContractionStage (G := G) B)
  (hD₂ : SameLabelShearDisplacement T₂.lift (Fin.last 0))
variable (hc : CanonicalStructure.IsCanonical (M := M))
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))))
  (hlead : ∀ q ∈ B.carrier, q.2 lead ≠ rvZero M)
include hc hv hQ hlead

theorem def_eps : S.Definable LRV {z : Fin (2 + T₂.arity) → M | ∃ s : T₂.contracted, ∃ x ∈ Dof T₂ hD₂ s.val.2,
    z = Fin.append ![x.val, (εU ε lead Q T₂ s.val.2 x).val] (rvValues s.val.2)} := by
  sorry

theorem def_t : S.Definable LRV {z : Fin (1 + T₂.arity) → M | ∃ s : T₂.contracted,
    z = Fin.append ![(tU lead T₂ s.val.2).val.val] (rvValues s.val.2)} := by
  sorry

theorem def_t₁ : S.Definable LRV {z : Fin (1 + T₂.arity) → M | ∃ s : T₂.contracted,
    kindU ε lead Q T₂ hD₂ s.val.2 = 2 ∧ z = Fin.append ![(t₁U ε lead Q T₂ hD₂ s.val.2).val] (rvValues s.val.2)} := by
  sorry

theorem def_kind (i : Fin 3) : S.Definable LRV {z : Fin T₂.arity → M | ∃ s : T₂.contracted,
    kindU ε lead Q T₂ hD₂ s.val.2 = i ∧ z = rvValues s.val.2} := by
  sorry

end Final

end DiamondIntegral.Section7.Lemma720
