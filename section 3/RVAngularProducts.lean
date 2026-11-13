import «section 3».RVUnitProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

/-- A definable angular cell is a finite disjoint union of products in
its integral monomial coordinates. Gamma factors lift by their full
value preimage; residue factors have finite Gamma support. -/
theorem rvAngularCell_finite_products {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : Section2.NontrivialDefinableGamma (⟨S,∅⟩ : Base (M := M)))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    ∃ N : ℕ, ∃ R : Fin N → DefSet (rawRVUnitSpace (M := M) K.zeroArity) S,
      ∃ G : Fin N → DefSet ((volumeGammaSpace hc).power (Fin K.freeArity)) S,
      (∀ i, (rvUnitTupleValues '' (R i).carrier).Finite) ∧
      (∀ i j, i ≠ j → Disjoint (R i).carrier (R j).carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i,
        (E.coordinateEquiv K x).1 ∈ (R i).carrier ∧
        (E.coordinateEquiv K x).2 ∈ (rvUnitGammaPreimage hc (G i)).carrier := by
  let T := rvAngularMixedDomain hc X E K
  let A := rvAngularResidueDomain hc X E K
  have hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ A.carrier := by
    intro x γ hx
    exact ⟨⟨(x,γ),hx⟩,rfl⟩
  obtain ⟨N,R,G,hR,hdis,hcov⟩ := rvUnitMixed_definable_products hκ hs h00 hc hsmall hΓ T A
    (rvAngularResidueDomain_finite_values hc X E K) hsub
  refine ⟨N,R,G,hR,hdis,?_⟩
  intro x
  have he : x ∈ X.carrier ↔ E.coordinateEquiv K x ∈ (rvAngularCoordinateMap X E K).image.carrier := by
    rw [rvAngularCoordinateMap_image]
    exact ⟨fun hx => ⟨x,hx,rfl⟩,fun ⟨y,hy,he⟩ => (E.coordinateEquiv K).injective he ▸ hy⟩
  have hf := Set.ext_iff.mp (rvAngularMixedDomain_full_preimage hc X E K) (E.coordinateEquiv K x)
  rw [he,← hf]
  exact hcov _ _
end DiamondIntegral.Section3
