import «section 3».GammaGroundRVUnitMixedLogic
import «section 3».GammaGroundRVUnitCoordinates
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- The mixed quotient has finite disjoint rectangles over its original
real/Gamma ground, with no common-name extension in the conclusion. -/
theorem gammaGroundRVUnitMixed_finite_rectangles {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))))
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hA : (rvUnitTupleValues '' A.carrier).Finite)
    (hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ A.carrier) :
    ∃ P : Finset (Set (Fin n → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ rvUnitValues '' A.carrier ∧
        DefinableOverBase B (fun _ => .rv) W ∧
        FullGammaSyntax.Definable (integrationGammaBase B)
          (fun γ => γ ∈ gammaTupleFamilyValues (gammaGroundRVUnitMixedRelation T) W)) ∧
      (P : Set (Set (Fin n → M))).Pairwise Disjoint ∧
      ∀ x γ, (x,γ) ∈ T.carrier ↔
        ∃ W ∈ P, rvUnitValues x ∈ W ∧ γ ∈ gammaTupleFamilyValues (gammaGroundRVUnitMixedRelation T) W := by
  have ha := (gammaGroundRVUnit_definable_iff A.carrier).mp A.definable
  have hD := gammaGroundRVUnitCoordinate_definable A
  have hmem : ∀ a ∈ rvUnitValues '' A.carrier, ∀ i, a i ∈ rvUnitRawCoordinateImage A.carrier i :=
    fun a ha i => ⟨a,ha,rfl⟩
  obtain ⟨P,hP,hdis,hcov⟩ := residue_gamma_tuple_finite_rectangles hκ hs h00 B hsmall hγsmall hΓ
    (gammaGroundRVUnitMixedRelation T) (gammaGroundRVUnitMixedRelation_definable hc T)
    (gammaGroundRVUnitMixedRelation_proper T) _ ha _ hD
    (rvUnitRawCoordinateImage_finite_values A.carrier hA) hmem
  refine ⟨P,hP,hdis,?_⟩
  intro x γ
  constructor
  · intro hx
    exact (hcov (rvUnitValues x) ⟨x,hsub x γ hx,rfl⟩ γ).mp ((gammaGroundRVUnitMixedRelation_unit T x γ).mpr hx)
  · rintro ⟨W,hW,hx,hγ⟩
    have haX := (hP W hW).2.1 hx
    exact (gammaGroundRVUnitMixedRelation_unit T x γ).mp ((hcov _ haX γ).mpr ⟨W,hW,hx,hγ⟩)
end DiamondIntegral.Section3
