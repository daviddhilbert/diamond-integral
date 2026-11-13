import «section 3».RVNormalizedMapMonomialWeights
import «section 3».GeneratedDiagonalWeightGroup
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {A D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}

def rvOriginalPointWeights (B : Base (M := M)) (a : Fin n → (CanonicalRV.RVSort M)ˣ) :
    Fin n → (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) :=
  fun i => QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (a i))

abbrev RVOriginalDiagonalWeightGroup (B : Base (M := M))
    (a b : Fin n → (CanonicalRV.RVSort M)ˣ) :=
  diagonalWeightGroup (rvOriginalPointWeights B a) (rvOriginalPointWeights B b)

/-- The actual original-ground coefficient conclusion, with the weight
group and its joint generation constructed here. Only the stated cited
classification remains an explicit replaceable input. -/
theorem rvMap_residue_generic_original_coefficients [CharZero (ModelResidue M)]
    (E : Subfield (ModelResidue M)) [IsAlgClosed E]
    (f : GammaGroundMap A D) (hf : Function.Injective f)
    (a b : Fin n → (CanonicalRV.RVSort M)ˣ)
    (H : ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (hR : (E : Set (ModelResidue M)).Definable Language.ring (rvNormalizedMapRelation f a b))
    (x y : Fin n → ModelResidue M) (hx : AlgebraicIndependent E x)
    (hxy : Sum.elim x y ∈ rvNormalizedMapRelation f a b) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, ∃ c : Fin n → (CanonicalRV.RVSort M)ˣ,
      IsUnit C.det ∧ (∀ i, DefinableClosureAtBase B .rv (rvUnitValues c i)) ∧
      rvUnitTupleValues b = rvUnitTupleValues c * integerMonomialMap C (rvUnitTupleValues a) ∧
      GammaGroundDefinable hc B (rawRVUnitSpace n) {c} := by
  let u := rvOriginalPointWeights B a
  let v := rvOriginalPointWeights B b
  exact rvNormalizedMapRelation_original_coefficients E H
    (diagonalWeightGroupEmbedding u v) (diagonalWeightGroupEmbedding_injective u v) f hf a b
    (sourceDiagonalWeights u v) (targetDiagonalWeights u v)
    (fun _ => rfl) (fun _ => rfl) (diagonalWeightGroup_joint_generation u v) hR x y hx hxy

end DiamondIntegral.Section3
