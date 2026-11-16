import «section 6».ParametricRVCenters
import Section4.VFFibreFiniteness

/-! A unary mixed definable map has a finite VF projection of its full
nondifferentiability locus, uniformly across all auxiliary RV labels.
This uses genuine saturation and the checked total generic derivative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_unary_differentiability_exception
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S} (f : Map A B) :
    ∃ E : DefSet (rawMixedSpace (M := M) 1 r) S,
      E.carrier ⊆ A.carrier ∧ (Prod.fst '' E.carrier).Finite ∧
      ∀ p : A, p.val ∉ E.carrier →
        ∃ L : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M), HasMixedVFDerivativeAt f p L := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let D : Set (Mixed M 1 r) :=
    {x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L}
  let E : DefSet (rawMixedSpace (M := M) 1 r) S :=
    ⟨A.carrier \ D,A.definable.sdiff _ (mixedDifferentiabilityLocus_definable (by decide) f)⟩
  have hAlg (p : E) : AlgebraicAt S .vf (p.val.1 0).val := by
    by_contra hn
    have hi : AlgebraicIndependent (vfParameterField S) p.val.1 := by
      apply algebraicIndependent_unique_type_iff.mpr
      intro h
      exact hn ((algebraicAt_vf_iff_parameterField S _).mpr h)
    let q : A := ⟨p.val,p.property.1⟩
    obtain ⟨L,hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f q hi
    exact p.property.2 ⟨q,rfl,L,hL⟩
  refine ⟨E,Set.sdiff_subset,finite_vf_projection_of_algebraic hs hsmall E
    (fun p i => by fin_cases i; exact hAlg p),?_⟩
  intro p hp
  have hgood : p.val ∈ D := by
    by_contra hn
    exact hp ⟨p.property,hn⟩
  obtain ⟨q,hq,L,hL⟩ := hgood
  have he : q = p := Subtype.ext hq
  subst q
  exact ⟨L,hL⟩

end DiamondIntegral.Section6
