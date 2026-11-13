import «section 3».GammaGroundRVGenericValueImage
import «section 3».RVGenericResidueFold
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {κ : Cardinal} {hc : CanonicalStructure.IsCanonical (M := M)}
variable (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
variable (hsmall : Cardinal.mk B.real < κ) {n : ℕ}

def rvNormalizedUnitTuple (a : Fin n → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) (hx0 : ∀ i, x i ≠ 0) : Fin n → (CanonicalRV.RVSort M)ˣ :=
  fun i => a i * residueUnitToRV (Units.mk0 (x i) (hx0 i))

@[simp] theorem rvNormalizedUnitTuple_values (a : Fin n → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) (hx0 : ∀ i, x i ≠ 0) :
    rvUnitTupleValues (rvNormalizedUnitTuple a x hx0) = rvUnitTupleValues a := by
  funext i
  simp only [rvUnitTupleValues,rvNormalizedUnitTuple,map_mul,residueUnitToRV_value_one,mul_one]

@[simp] theorem rvNormalizedUnitTuple_raw (a : Fin n → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) (hx0 : ∀ i, x i ≠ 0) :
    rvUnitValues (rvNormalizedUnitTuple a x hx0) = rvNormalizedTuple a x := rfl

/-- Testing the actual full-fibre generic at any independent normalized
residue tuple agrees with membership in the original unit set. -/
theorem gammaGroundRVGeneric_normalized_test
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (E : Subfield (ModelResidue M))
    (hR : ∀ k ≤ n, (E : Set (ModelResidue M)).Definable Language.ring
      {x : Fin n → ModelResidue M | rvNormalizedTuple a x ∈
        ((List.finRange n).take k).foldl rvGenericCoordinate (rvUnitValues '' A.carrier)})
    (x : Fin n → ModelResidue M) (hx : AlgebraicIndependent E x)
    (hx0 : ∀ i, x i ≠ 0) :
    rvUnitTupleValues a ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall A).carrier ↔
      rvNormalizedUnitTuple a x hx0 ∈ A.carrier := by
  have hA := (gammaGroundRVUnit_definable_iff A.carrier).mp A.definable
  have hh := gammaGroundRVGenericValueImage_mem_iff hs h00 B hsmall A (rvNormalizedUnitTuple a x hx0)
  rw [rvNormalizedUnitTuple_values,rvNormalizedUnitTuple_raw] at hh
  have hR' : ∀ k ≤ (List.finRange n).length, (E : Set (ModelResidue M)).Definable Language.ring
      {z : Fin n → ModelResidue M | rvNormalizedTuple a z ∈
        ((List.finRange n).take k).foldl rvGenericCoordinate (rvUnitValues '' A.carrier)} := by
    simpa using hR
  have ht := rvGenericCoordinate_fold_at_residue_generic hc hs h00 B hsmall
    (rvUnitValues '' A.carrier) hA a E (List.finRange n) hR' x hx
  have hm : rvNormalizedTuple a x ∈ rvUnitValues '' A.carrier ↔
      rvNormalizedUnitTuple a x hx0 ∈ A.carrier := by
    rw [← rvNormalizedUnitTuple_raw a x hx0]
    simp only [Set.mem_image,rvUnitValues_injective.eq_iff,exists_eq_right]
  exact hh.trans (ht.trans hm)

end DiamondIntegral.Section3
