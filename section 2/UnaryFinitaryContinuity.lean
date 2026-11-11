import «section 2».FinitaryContinuity
import Section3.AlgebraicFinite

/-!
# Finite exceptional set for unary finite-valued correspondences

The existing generic continuity proof excludes every transcendental VF
input. Its same-base definable bad set is therefore algebraic and finite
by genuine saturation. This is the unary specialization used in curve
selection; no dimension-to-finiteness principle is an extra premise.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_2_44_unary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {m : ℕ} (A : Set (Fin 1 → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (F : (Fin 1 → VF M) → Set (Fin m → VF M))
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) (hfin : ∀ a ∈ A, (F a).Finite) :
    ∃ E ⊆ A, E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      ∀ a ∈ A \ E, HasMinimalLimitSet A a F (F a) := by
  obtain ⟨C⟩ := exists_finitaryRVCode h00 hs hsmall A F hG hfin
  let U : Set M := {x | (fun _ : Fin 1 => x) ∈ C.badRaw}
  have heta (z : Fin 1 → M) : (fun _ : Fin 1 => z 0) = z := by
    funext i
    fin_cases i
    rfl
  have hU : S.Definable₁ LRV U := by
    change S.Definable LRV {z : Fin 1 → M | (fun _ : Fin 1 => z 0) ∈ C.badRaw}
    simpa only [heta, Set.ofPred_mem_eq] using C.badRaw_definable hG
  have hUf : U.Finite := by
    apply RawClosure.finite_of_definable_subset_algebraic hs S hsmall U hU
    intro x hx
    by_cases halg : AlgebraicAt S .vf x
    · exact halg.raw_finite_witness
    · let a : Fin 1 → VF M := fun _ => ⟨x,hx.1 0⟩
      have hind : AlgebraicIndependent (vfParameterField S) a := by
        apply algebraicIndependent_unique_type_iff.mpr
        intro h
        exact halg ((algebraicAt_vf_iff_parameterField S _).mpr h)
      exact (C.not_mem_badRaw_of_independent hc hκ hs hsmall hv hG a hind hx).elim
  let E : Set (Fin 1 → VF M) := {a ∈ A | vfValues a ∈ C.badRaw}
  have heval : Function.Injective (fun a : Fin 1 → VF M => (a 0).val) := by
    intro a b h
    funext i
    fin_cases i
    exact Subtype.ext h
  have hEf : E.Finite := (hUf.preimage heval.injOn).subset (by
    intro a ha
    change (fun _ : Fin 1 => (a 0).val) ∈ C.badRaw
    exact (heta (vfValues a)).symm ▸ ha.2)
  have he : vfValues '' E = (vfValues '' A) ∩ C.badRaw := by
    ext z
    constructor
    · rintro ⟨a,⟨ha,hb⟩,rfl⟩
      exact ⟨⟨a,ha,rfl⟩,hb⟩
    · rintro ⟨⟨a,ha,rfl⟩,hb⟩
      exact ⟨a,⟨ha,hb⟩,rfl⟩
  refine ⟨E,fun _ h => h.1,hEf,he.symm ▸ hA.inter (C.badRaw_definable hG),?_⟩
  intro a ⟨ha,hbad⟩
  exact C.minimalLimit_of_good S A F hv (by decide) a ha (hfin a ha)
    (fun h => hbad ⟨ha,h⟩)

end DiamondIntegral.Section2
