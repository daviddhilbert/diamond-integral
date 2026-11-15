import IntegrationSection5.GammaPreparation
import Section3.SmallFiniteParameters

/-! A common real presentation is constructed internally from finite
Gamma codes for the two domains and the complete graph. No code is named
in the original base or added to the smallness hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {n m u w : ℕ}

theorem common_gamma_presentation_small {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsmall : Cardinal.mk P.real < κ)
    (A : Set (Point (M := M) n m)) (B : Set (Point (M := M) u w)) (f : A → B)
    (hA : GammaSetDefinable P A) (hB : GammaSetDefinable P B)
    (hf : GammaGraphDefinable P (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q)) :
    ∃ S : Set M, P.real ⊆ S ∧ Cardinal.mk S < κ ∧ SetDefinable (pointSpace n m) S A ∧
      SetDefinable (pointSpace u w) S B ∧
      RelationDefinable (pointSpace n m) (pointSpace u w) S
        (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q) := by
  obtain ⟨_, tA, _, DA, hDA⟩ := gammaPresentationInput P A hA
  obtain ⟨_, tB, _, DB, hDB⟩ := gammaPresentationInput P B hB
  obtain ⟨_, tF, hF⟩ := GammaGraphDefinable.real_specialize hf
  let SA := P.real ∪ Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tA)
  let SB := P.real ∪ Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tB)
  let SF := P.real ∪ Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tF)
  let E := (Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tA) ∪
    Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tB)) ∪
    Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tF)
  let S := P.real ∪ E
  have hAS : SA ⊆ S := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl (Or.inl hx))
  have hBS : SB ⊆ S := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl (Or.inr hx))
  have hFS : SF ⊆ S := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  have hE : E.Finite := (Set.finite_range _ |>.union (Set.finite_range _)).union (Set.finite_range _)
  have hS : Cardinal.mk S < κ := small_union_finite hκ P.real hsmall E hE
  refine ⟨S, (fun _ h => hAS (Or.inl h)), hS, ?_, ?_, ?_⟩
  · exact hDA ▸ SetDefinable.mono _ (setDefinable DA) hAS
  · exact hDB ▸ SetDefinable.mono _ (setDefinable DB) hBS
  · exact RelationDefinable.mono _ _ hF hFS

end IntegrationInACVF.Section5
