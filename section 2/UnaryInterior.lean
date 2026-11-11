import «section 2».UnaryFinitaryContinuity
import «section 2».SmallVFGeneratedBase
import Section3.SortedTuples

/-! A definable unary VF set with empty interior is finite. The proof
uses the checked neighbourhood theorem at independent points and genuine
saturation, and retains the original small base when one is supplied. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unary_definable_finite_of_interior_empty
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin 1 → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hInt : interior A = ∅) : A.Finite := by
  classical
  let U : Set M := {x | (fun _ : Fin 1 => x) ∈ vfValues '' A}
  have heta (z : Fin 1 → M) : (fun _ : Fin 1 => z 0) = z := by
    funext i
    fin_cases i
    rfl
  have hU : S.Definable₁ LRV U := by
    change S.Definable LRV {z : Fin 1 → M | (fun _ : Fin 1 => z 0) ∈ vfValues '' A}
    simpa only [heta,Set.ofPred_mem_eq] using hA
  have hAsorted : DefinableOver S (fun _ : Fin 1 => .vf) (vfValues '' A) :=
    raw_definableOver_sorted hc S _ _ hA (by rintro z ⟨a,ha,rfl⟩ i; exact (a i).property)
  have hUf : U.Finite := by
    apply RawClosure.finite_of_definable_subset_algebraic hs S hsmall U hU
    intro x hx
    by_cases halg : AlgebraicAt S .vf x
    · exact halg.raw_finite_witness
    · obtain ⟨a,ha,he⟩ := hx
      have hax : (a 0).val = x := congrFun he 0
      have hind : AlgebraicIndependent (vfParameterField S) a := by
        apply algebraicIndependent_unique_type_iff.mpr
        intro h
        exact halg (hax ▸ (algebraicAt_vf_iff_parameterField S (a 0)).mpr h)
      have hN := independent_definable_mem_nhds hv S (vfValues '' A) hAsorted a hind ⟨a,ha,rfl⟩
      have heA : {y : Fin 1 → VF M | vfValues y ∈ vfValues '' A} = A := by
        ext y
        constructor
        · rintro ⟨z,hz,he⟩
          exact vfValues_injective he ▸ hz
        · exact fun hy => ⟨y,hy,rfl⟩
      rw [heA] at hN
      have haInt : a ∈ interior A := mem_interior_iff_mem_nhds.mpr hN
      rw [hInt] at haInt
      exact haInt.elim
  have heval : Function.Injective (fun a : Fin 1 → VF M => (a 0).val) := by
    intro a b h
    funext i
    fin_cases i
    exact Subtype.ext h
  apply (hUf.preimage heval.injOn).subset
  intro a ha
  change (fun _ : Fin 1 => (a 0).val) ∈ vfValues '' A
  exact ⟨a,ha,(heta (vfValues a)).symm⟩

theorem unary_definable_finite_of_interior_empty_any_base
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin 1 → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hInt : interior A = ∅) : A.Finite := by
  obtain ⟨C,hsmall,hAC,_⟩ := exists_small_vf_generated_base_for_definable hv hκ (vfValues '' A) hA
  exact unary_definable_finite_of_interior_empty hc hs hsmall hv A hAC hInt

end DiamondIntegral.Section2
