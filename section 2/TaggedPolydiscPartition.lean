import «section 2».FiniteGoodPartition
import «section 2».TypeLoci
import «section 2».TypeGoodTaggedPolydiscs

/-! The two actual compactness steps and finite Boolean refinement for
Corollary 2.30. Every partition piece is defined over the original base.
Only the accepted unary results from [18] remain as geometric inputs. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem good_tagged_polydisc_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOver S (fun _ => .vf) A)
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOver S (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (hrv : ∀ x ∈ A, Set.InjOn iRv {y | (x,y) ∈ F}) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧ DefinableOver S (fun _ => .vf) V ∧
        ∀ d, rawOpenPolydiscProper d → rawOpenPolydisc d ⊆ V →
          d ∈ rawGoodTaggedPolydiscCodes F) ∧ ∀ x ∈ A, ∃ V ∈ Q, x ∈ V := by
  let B : ParameterBase M := ⟨S,∅⟩
  have hAsort : A ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
    obtain ⟨p,φ,hφ,rfl⟩ := hA
    exact fun _ hx => hx.1
  have hFB : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F} :=
    (GammaParameters.base_empty_iff S _ _).mpr hF
  have htype : ∀ x ∈ A, ∀ d : Fin (n+n) → M, rawOpenPolydiscProper d →
      rawOpenPolydisc d ⊆ rawTypeLocus S x → d ∈ rawGoodTaggedPolydiscCodes F := by
    intro x hx d hd hsub
    have hTA : rawTypeLocus S x ⊆ A := fun _ hy => hy A hA.raw_definable hx
    exact type_good_tagged_polydisc_code h00 B hΓ unary rvbase image d hd
      (rawTypeLocus S x) (rawTypeLocus_generates S (fun _ => .vf) x (hAsort hx))
      hsub F hFB (fun y hy => hrv y (hTA (hsub hy)))
  obtain ⟨Q,hQf,hQdis,hQ,hcov⟩ := type_local_finite_good_partition hs S hsmall A hA.raw_definable
    {d : Fin (n+n) → M | rawOpenPolydiscProper d} (rawGoodTaggedPolydiscCodes F)
    (rawOpenPolydiscProper_definable S n) (rawGoodTaggedPolydiscCodes_definable S F hF.raw_definable)
    rawOpenPolydisc (rawOpenPolydisc_membership_definable S n) htype
  refine ⟨Q,hQf,hQdis,?_,hcov⟩
  intro V hV
  obtain ⟨hne,hVA,hVdef,hgood⟩ := hQ V hV
  exact ⟨hne,hVA,raw_definableOver_sorted hc S (fun _ => .vf) V hVdef
    (hVA.trans hAsort),hgood⟩

end DiamondIntegral.Section2
