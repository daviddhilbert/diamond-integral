import «section 3».RVUnitMixedLogic
import «section 3».RVUnitDomains
import «section 3».ResidueGammaTupleRectangles
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

/-- Actual definable mixed sets with finite residue-coordinate value
support have finite disjoint rectangles over their real ground. -/
theorem rvUnitMixed_finite_rectangles {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : Section2.NontrivialDefinableGamma (⟨S,∅⟩ : Base (M := M)))
    (T : DefSet ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))) S)
    (A : DefSet (rawRVUnitSpace (M := M) n) S)
    (hA : (rvUnitTupleValues '' A.carrier).Finite)
    (hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ A.carrier) :
    ∃ P : Finset (Set (Fin n → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ rvUnitValues '' A.carrier ∧
        DefinableOver S (fun _ => .rv) W ∧
        FullGammaSyntax.Definable (integrationGammaBase (⟨S,∅⟩ : Base (M := M)))
          (fun γ => γ ∈ gammaTupleFamilyValues (rvUnitMixedRelation T) W)) ∧
      (P : Set (Set (Fin n → M))).Pairwise Disjoint ∧
      ∀ x γ, (x,γ) ∈ T.carrier ↔
        ∃ W ∈ P, rvUnitValues x ∈ W ∧ γ ∈ gammaTupleFamilyValues (rvUnitMixedRelation T) W := by
  let B : Base (M := M) := ⟨S,∅⟩
  have hγsmall : Cardinal.mk B.gamma < κ := by
    simpa only [B,Cardinal.mk_eq_zero] using (lt_of_lt_of_le Cardinal.aleph0_pos hκ)
  have ha := real_definableOverBase B (fun _ => .rv) _ (rvUnitDomain_native_definable hc A)
  have hD := fun i => real_definableAtBase B .rv _ (rvUnitCoordinateDomain_definable hc A i)
  have hmem : ∀ a ∈ rvUnitValues '' A.carrier, ∀ i, a i ∈ rvUnitCoordinateDomain A i :=
    fun a ha i => ⟨a,ha,rfl⟩
  obtain ⟨P,hP,hdis,hcov⟩ := residue_gamma_tuple_finite_rectangles hκ hs h00 B hsmall hγsmall hΓ
    (rvUnitMixedRelation T) (rvUnitMixedRelation_definable hc T) (rvUnitMixedRelation_proper T)
    _ ha _ hD (rvUnitCoordinateDomain_finite_values A hA) hmem
  refine ⟨P,?_,hdis,?_⟩
  · intro W hW
    refine ⟨(hP W hW).1,(hP W hW).2.1,?_,(hP W hW).2.2.2⟩
    simpa only [B,commonRealNames,Set.image_empty,Set.union_empty] using (hP W hW).2.2.1.common_names
  · intro x γ
    constructor
    · intro hx
      exact (hcov (rvUnitValues x) ⟨x,hsub x γ hx,rfl⟩ γ).mp ((rvUnitMixedRelation_unit T x γ).mpr hx)
    · rintro ⟨W,hW,hx,hγ⟩
      have haX := (hP W hW).2.1 hx
      exact (rvUnitMixedRelation_unit T x γ).mp ((hcov _ haX γ).mpr ⟨W,hW,hx,hγ⟩)
end DiamondIntegral.Section3
