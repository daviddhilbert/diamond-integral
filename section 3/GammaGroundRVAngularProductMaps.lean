import «section 3».GammaGroundRVAngularProducts
import «section 3».GammaGroundBijectionRestrictions
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

/-- Product charts with the actual monomial coordinate-map formula
retained, so Gamma-valued forms can be reconstructed through them. -/
theorem gammaGroundRVAngularCell_product_maps {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    ∃ N : ℕ, ∃ R : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity),
      ∃ G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity)),
      ∃ Y : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ F : (i : Fin N) → GammaGroundBijection (Y i) ((R i).prod (gammaGroundRVUnitGammaPreimage (G i))),
      (∀ i, (rvUnitTupleValues '' (R i).carrier).Finite) ∧
      (∀ i, (Y i).carrier ⊆ X.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (Y i).carrier (Y j).carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (Y i).carrier) ∧
      ∀ i (y : Y i), ((F i).map y).val = E.coordinateEquiv K y.val := by
  obtain ⟨N,R,G,hR,hdis,hcov⟩ := gammaGroundRVAngularCell_finite_products hκ hs h00 hsmall hγsmall hΓ X E K
  let f := gammaGroundRVAngularCoordinateBijection X E K
  let Z := fun i => (R i).prod (gammaGroundRVUnitGammaPreimage (G i))
  let Y := fun i => f.inverseImage (Z i)
  have hZ : ∀ i, (Z i).carrier ⊆ (gammaGroundRVAngularCoordinateMap X E K).image.carrier := by
    intro i z hz
    let x := (E.coordinateEquiv K).symm z
    have he : E.coordinateEquiv K x = z := (E.coordinateEquiv K).apply_symm_apply z
    have hx : x ∈ X.carrier := (hcov x).mpr ⟨i,by rw [he]; exact hz.1,by rw [he]; exact hz.2⟩
    exact ⟨⟨x,hx⟩,he⟩
  refine ⟨N,R,G,Y,fun i => f.restrictTarget (Z i) (hZ i),hR,fun i => f.inverseImage_subset (Z i),?_,?_,fun _ _ => rfl⟩
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
