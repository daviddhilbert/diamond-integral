import «section 2».VFFiniteChoice

/-!
# A finite nonempty definable subset over the same VF-generated base

An elementary algebraic-closure model supplies a tuple in A. Keep a finite
definable algebraic cover of each coordinate, then intersect their product
with A. No individual conjugate is asserted definable. Saturation is not
needed for this fixed-set version.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem exists_nonempty_finite_definable_vf_subset
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    {n : ℕ} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hne : A.Nonempty) :
    ∃ C ⊆ A, C.Finite ∧ C.Nonempty ∧ S.Definable LRV (vfValues '' C) := by
  classical
  obtain ⟨a,ha,halg⟩ := acl_meets_definable_tuple v hv hc h00 V S hV hSV hnt
    (vfValues '' A) hA (hne.image _)
  have halgS (i : Fin n) : RawClosure.AlgebraicOver S (a i) := by
    obtain ⟨U,hU,hUf,haU⟩ := halg i
    exact ⟨U,hU.mono hVS,hUf,haU⟩
  choose U hU hUf haU using halgS
  let P : Set (Fin n → M) := {z | ∀ i, z i ∈ U i}
  have hP : S.Definable LRV P := by
    have hcoord (i : Fin n) : S.Definable LRV {z : Fin n → M | z i ∈ U i} :=
      (hU i).preimage_comp (fun _ : Fin 1 => i)
    convert Set.definable_iInter_of_finite hcoord using 1
    ext z
    simp only [P,Set.mem_ofPred_eq,Set.mem_iInter]
  let R := (vfValues '' A) ∩ P
  have hRf : R.Finite := (Set.Finite.pi' hUf).subset (fun _ h => h.2)
  have hR : S.Definable LRV R := hA.inter hP
  have haR : a ∈ R := ⟨ha,haU⟩
  let C : Set (Fin n → VF M) := vfValues ⁻¹' R
  have hCA : C ⊆ A := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hx.1
    exact vfValues_injective he ▸ hy
  have hCimage : vfValues '' C = R := by
    apply Set.image_preimage_eq_of_subset
    exact (Set.inter_subset_left).trans (Set.image_subset_range _ _)
  refine ⟨C,hCA,hRf.preimage vfValues_injective.injOn,?_,hCimage.symm ▸ hR⟩
  obtain ⟨x,hx,he⟩ := ha
  refine ⟨x,?_⟩
  change vfValues x ∈ R
  rwa [he]

end DiamondIntegral.Section2
