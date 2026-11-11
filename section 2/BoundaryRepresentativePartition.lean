import «section 2».BoundaryRepresentativeDefinability
import «section 2».FinitaryRVPartition

/-! The actual representative correspondence and original-base finite
partition used in the inductive proof of Lemma 2.35. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rawCoordinateProjection (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) :
    Set (Fin n → M) := Fin.removeNth i '' A

theorem rawCoordinateProjection_definable (S : Set M)
    (A : Set (Fin (n+1) → M)) (hA : DefinableOver S (fun _ => .vf) A)
    (i : Fin (n+1)) : DefinableOver S (fun _ => .vf) (rawCoordinateProjection A i) := by
  have hAB := (GammaParameters.base_empty_iff S (fun _ => .vf) A).mpr hA
  exact (GammaParameters.base_empty_iff S _ _).mp (hAB.image_real i.succAbove)

theorem boundary_representative_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    (A : Set (Fin (n+1) → M)) (hA : DefinableOver S (fun _ => .vf) A) (i : Fin (n+1)) :
    ∃ (F : (Fin n → M) → Set M) (Q : Set (Set (Fin n → M))),
      DefinableOver S (fun _ : Fin (n+1) => .vf)
        {z | Fin.init z ∈ rawCoordinateProjection A i ∧ z (Fin.last n) ∈ F (Fin.init z)} ∧
      (∀ a ∈ rawCoordinateProjection A i, (F a).Finite ∧ Set.InjOn iRv (F a) ∧
        Subtype.val '' boundaryTagSet A i a ⊆ iRv '' F a) ∧
      Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ rawCoordinateProjection A i ∧
        DefinableOver S (fun _ => .vf) V ∧ RVPolydiscRowsConstant F V) ∧
      ∀ a ∈ rawCoordinateProjection A i, ∃ V ∈ Q, a ∈ V := by
  have hD := rawCoordinateProjection_definable S A hA i
  obtain ⟨F,hF,hvalues⟩ := boundary_representative_correspondence_exists hc h00 hs S hsmall
    A hA i _ hD
  obtain ⟨Q,hQ,hdis,hpieces,hcover⟩ := finitary_rv_partition hc h00 hs S hsmall hΓ
    unary rvbase image _ hD F hF
    (fun a ha => (hvalues a ha).1) (fun a ha => (hvalues a ha).2.1)
  exact ⟨F,Q,hF,hvalues,hQ,hdis,hpieces,hcover⟩

end DiamondIntegral.Section2
