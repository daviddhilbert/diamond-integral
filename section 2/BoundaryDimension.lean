import «section 2».BoundaryCover
import «section 2».BoundaryGraphDimension

/-! Lemma 2.35, following the approved main-text induction. Its only
cited geometric inputs are the three explicitly replaceable unary results
from [18, Section 3] already used in Corollary 2.30. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem boundaryCoverPiece_dimension (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n : ℕ} (i : Fin (n+1)) (V : Set (Fin n → M))
    (hV : DefinableOver S (fun _ => .vf) V) (F : (Fin n → M) → Set M)
    (hF : DefinableOver S (fun _ => .vf) (rawScalarCorrespondenceGraph V F))
    (hfinite : ∀ a ∈ V, (F a).Finite) (hconstant : RVPolydiscRowsConstant F V)
    (hboundary : rvDimension S (rawRVBoundary V) < (n : WithBot ℕ)) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' boundaryCoverPiece i V F) ∧
      rvDimension S (boundaryCoverPiece i V F) < ((n+1 : ℕ) : WithBot ℕ) := by
  have hB := rvCoordinateCylinder_definable hc S i _ (rawRVBoundary_definable hc S V hV)
  have hdB := rvDimension_coordinate_cylinder_lt hc S i _ (rawRVBoundary_definable hc S V hV) hboundary
  have hC := boundaryRVGraph_definable hc S i V hV F hF
  have hdC := boundaryRVGraph_dimension_lt hc S i V hV F hF hfinite hconstant
  have hmB := (rvDimension_lt_succ_iff_finite_map hc S _ hB).mp hdB
  have hmC := (rvDimension_lt_succ_iff_finite_map hc S _ hC).mp hdC
  have hm : RVHasFiniteMap S (boundaryCoverPiece i V F) n := hmB.union hc hmC hB
  exact ⟨hm.domain_definable,
    (rvDimension_lt_succ_iff_finite_map hc S _ hm.domain_definable).mpr hm⟩

theorem rawRVBoundary_zero_empty (A : Set (Fin 0 → M)) : rawRVBoundary A = ∅ := by
  ext t
  constructor
  · rintro ⟨⟨x,hx,hxA⟩,y,hy,hyA⟩
    exact hyA ((Subsingleton.elim x y) ▸ hxA)
  · exact False.elim

theorem lemma_2_35
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOver S (fun _ => .vf) A) :
    rvDimension S (rawRVBoundary A) < (n : WithBot ℕ) := by
  classical
  induction n with
  | zero =>
    rw [rawRVBoundary_zero_empty,rvDimension_empty]
    simp
  | succ n ih =>
    have hdata (i : Fin (n+1)) := boundary_representative_partition hc h00 hs S hsmall hΓ
      unary rvbase image A hA i
    choose F Q hF hvalues hQfinite hdis hpieces hcover using hdata
    have hproper : ∀ i, ∀ a ∈ rawCoordinateProjection A i, ∀ y ∈ F i a, iVF y := by
      intro i a ha y hy
      have hw : (Fin.snoc a y : Fin (n+1) → M) ∈
          {z : Fin (n+1) → M | Fin.init z ∈ rawCoordinateProjection A i ∧ z (Fin.last n) ∈ F i (Fin.init z)} := by
        simpa only [Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last] using And.intro ha hy
      have hp := ((GammaParameters.base_empty_iff S _ _).mpr (hF i)).proper _ hw (Fin.last n)
      simpa only [Fin.snoc_last,sortEval,iVF] using hp
    have hpack (i : Fin (n+1)) (V : Set (Fin n → M)) (hV : V ∈ Q i) := by
      obtain ⟨hne,hVD,hVdef,hconst⟩ := hpieces i V hV
      have hFV := rawScalarCorrespondenceGraph_restrict_definable hc S _ V hVdef hVD (F i) (hF i)
      exact boundaryCoverPiece_dimension hc S i V hVdef (F i) hFV
        (fun a ha => (hvalues i a (hVD ha)).1) hconst (ih V hVdef)
    let H : Set (Set (Fin (n+1) → RVInfinity M)) :=
      ⋃ i, (fun V => boundaryCoverPiece i V (F i)) '' Q i
    have hH : H.Finite := Set.finite_iUnion (fun i => (hQfinite i).image _)
    have hHdef : ∀ W ∈ H, DefinableOver S (fun _ => .rv) (rvInputValues '' W) := by
      intro W hW
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hW
      obtain ⟨V,hV,rfl⟩ := hi
      exact (hpack i V hV).1
    have hHmap : ∀ W ∈ H, RVHasFiniteMap S W n := by
      intro W hW
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hW
      obtain ⟨V,hV,rfl⟩ := hi
      exact (rvDimension_lt_succ_iff_finite_map hc S _ (hpack i V hV).1).mp (hpack i V hV).2
    have hmap := rv_finite_map_finite_union hc S H hH hHmap hHdef
    have hsubset : rawRVBoundary A ⊆ ⋃₀ H := rawRVBoundary_subset_cover A F Q hproper
      (fun i a ha => (hvalues i a ha).2.2) hcover
    exact lt_of_le_of_lt (rvDimension_le_of_finite_map
      (hmap.restrict hc hsubset (rawRVBoundary_definable hc S A hA)))
      (by exact_mod_cast Nat.lt_succ_self n)

end DiamondIntegral.Section2
