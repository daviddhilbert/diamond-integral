import «section 3».GammaGroundRVUnitProducts
import «section 3».GammaGroundRVAngularQuotient
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- A definable angular cell is a finite disjoint union of products in
its integral monomial coordinates. Gamma factors lift by their full
value preimage; residue factors have finite Gamma support. -/
theorem gammaGroundRVAngularCell_finite_products {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    ∃ N : ℕ, ∃ R : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity),
      ∃ G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity)),
      (∀ i, (rvUnitTupleValues '' (R i).carrier).Finite) ∧
      (∀ i j, i ≠ j → Disjoint (R i).carrier (R j).carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i,
        (E.coordinateEquiv K x).1 ∈ (R i).carrier ∧
        (E.coordinateEquiv K x).2 ∈ (gammaGroundRVUnitGammaPreimage (G i)).carrier := by
  let T := gammaGroundRVAngularMixedDomain X E K
  let A := gammaGroundRVAngularResidueDomain X E K
  have hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ A.carrier := by
    intro x γ hx
    exact ⟨⟨(x,γ),hx⟩,rfl⟩
  obtain ⟨N,R,G,hR,hdis,hcov⟩ := gammaGroundRVUnitMixed_definable_products hκ hs h00 hsmall hγsmall hΓ T A
    (gammaGroundRVAngularResidueDomain_finite_values X E K) hsub
  refine ⟨N,R,G,hR,hdis,?_⟩
  intro x
  have he : x ∈ X.carrier ↔ E.coordinateEquiv K x ∈ (gammaGroundRVAngularCoordinateMap X E K).image.carrier := by
    rw [gammaGroundRVAngularCoordinateMap_image]
    exact ⟨fun hx => ⟨x,hx,rfl⟩,fun ⟨y,hy,he⟩ => (E.coordinateEquiv K).injective he ▸ hy⟩
  have hf := Set.ext_iff.mp (gammaGroundRVAngularMixedDomain_full_preimage X E K) (E.coordinateEquiv K x)
  rw [he,← hf]
  exact hcov _ _
end DiamondIntegral.Section3
