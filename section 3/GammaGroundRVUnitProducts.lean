import «section 3».GammaGroundRVUnitRectangles
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

def gammaGroundRVUnitGammaPreimage
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m) :=
  ⟨{x | rvUnitTupleValues x ∈ G.carrier},G.definable.preimage (rvUnitGammaMap hc B.real m)⟩

/-- Actual disjoint product factors over the original real/Gamma ground. -/
theorem gammaGroundRVUnitMixed_definable_products {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))))
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hA : (rvUnitTupleValues '' A.carrier).Finite)
    (hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ A.carrier) :
    ∃ N : ℕ, ∃ R : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)),
      (∀ i, (rvUnitTupleValues '' (R i).carrier).Finite) ∧
      (∀ i j, i ≠ j → Disjoint (R i).carrier (R j).carrier) ∧
      ∀ x γ, (x,γ) ∈ T.carrier ↔ ∃ i, x ∈ (R i).carrier ∧ γ ∈ (G i).carrier := by
  obtain ⟨P,hP,hdis,hcov⟩ := gammaGroundRVUnitMixed_finite_rectangles hκ hs h00 hsmall hγsmall hΓ T A hA hsub
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  let R : Fin (Fintype.card P) → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun i =>
    gammaGroundRVUnitSetOfBase (e i).val (hP _ (e i).property).2.2.1
  let G : Fin (Fintype.card P) → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)) := fun i =>
    ⟨{γ | γ ∈ gammaTupleFamilyValues (gammaGroundRVUnitMixedRelation T) (e i).val},
      gammaGroundGammaPower_predicate_definable _ (hP _ (e i).property).2.2.2⟩
  have hRA : ∀ i, (R i).carrier ⊆ A.carrier := by
    intro i x hx
    obtain ⟨y,hy,he⟩ := (hP _ (e i).property).2.1 hx
    exact rvUnitValues_injective he ▸ hy
  refine ⟨Fintype.card P,R,G,fun i => hA.subset (Set.image_mono (hRA i)),?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hne : (e i).val ≠ (e j).val := fun he => hij (e.injective (Subtype.ext he))
    exact Set.disjoint_left.mp (hdis (e i).property (e j).property hne) hi hj
  · intro x γ
    rw [hcov x γ]
    constructor
    · rintro ⟨W,hW,hx,hγ⟩
      obtain ⟨i,hi⟩ := e.surjective ⟨W,hW⟩
      refine ⟨i,?_,?_⟩
      · change rvUnitValues x ∈ (e i).val
        simpa only [hi] using hx
      · change γ ∈ gammaTupleFamilyValues (gammaGroundRVUnitMixedRelation T) (e i).val
        simpa only [hi] using hγ
    · rintro ⟨i,hx,hγ⟩
      exact ⟨(e i).val,(e i).property,hx,hγ⟩
end DiamondIntegral.Section3
