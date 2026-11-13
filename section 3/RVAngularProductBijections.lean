import «section 3».RVAngularProducts
import «section 3».DefinableBijectionRestrictions
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

/-- Actual finite product charts: both pieces and bijections are
definable over the original real ground, with full Gamma fibres. -/
theorem rvAngularCell_product_bijections {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : Section2.NontrivialDefinableGamma (⟨S,∅⟩ : Base (M := M)))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    ∃ N : ℕ, ∃ R : Fin N → DefSet (rawRVUnitSpace (M := M) K.zeroArity) S,
      ∃ G : Fin N → DefSet ((volumeGammaSpace hc).power (Fin K.freeArity)) S,
      ∃ Y : Fin N → DefSet (rawRVUnitSpace (M := M) n) S,
      (∀ i, (rvUnitTupleValues '' (R i).carrier).Finite) ∧
      (∀ i, Nonempty (DefinableBijection (Y i) ((R i).prod (rvUnitGammaPreimage hc (G i))))) ∧
      (∀ i j, i ≠ j → Disjoint (Y i).carrier (Y j).carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (Y i).carrier := by
  obtain ⟨N,R,G,hR,hdis,hcov⟩ := rvAngularCell_finite_products hκ hs h00 hc hsmall hΓ X E K
  let f := rvAngularCoordinateBijection X E K
  let Z := fun i => (R i).prod (rvUnitGammaPreimage hc (G i))
  let Y := fun i => f.inverseImage (Z i)
  have hZ : ∀ i, (Z i).carrier ⊆ (rvAngularCoordinateMap X E K).image.carrier := by
    intro i z hz
    let x := (E.coordinateEquiv K).symm z
    have he : E.coordinateEquiv K x = z := (E.coordinateEquiv K).apply_symm_apply z
    have hx : x ∈ X.carrier := (hcov x).mpr ⟨i,by rw [he]; exact hz.1,by rw [he]; exact hz.2⟩
    exact ⟨⟨x,hx⟩,he⟩
  refine ⟨N,R,G,Y,hR,fun i => ⟨f.restrictTarget (Z i) (hZ i)⟩,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,hai⟩ ⟨b,hb,hbj⟩
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    rw [hab] at hai
    exact Set.disjoint_left.mp (hdis i j hij) hai.1 hbj.1
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := (hcov x).mp hx
      exact ⟨i,⟨x,hx⟩,rfl,hi⟩
    · rintro ⟨i,hx⟩
      exact f.inverseImage_subset (Z i) hx
end DiamondIntegral.Section3
