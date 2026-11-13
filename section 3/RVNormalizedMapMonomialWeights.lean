import «section 3».RVNormalizedMapCharacters
import «section 3».ACFDiagonalClassification
import «section 3».GammaGroundTorusWeightLifts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open scoped BigOperators
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (ModelResidue M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {A D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}

/-- An actual injective original-ground RV map, at a residue-generic
pair, supplies exactly the weight classification claimed in C002. The
only cited input is the stated diagonal-action classification. -/
theorem rvNormalizedMapRelation_monomial_weights {W : Type*} [AddCommGroup W]
    (E : Subfield (ModelResidue M)) [IsAlgClosed E] (H : ReichsteinYoussinInput E W)
    (ι : Multiplicative W →* (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B))
    (hι : Function.Injective ι) (f : GammaGroundMap A D) (hf : Function.Injective f)
    (a b : Fin n → (CanonicalRV.RVSort M)ˣ) (w z : Fin n → W)
    (ha : ∀ i, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (a i)) = ι (Multiplicative.ofAdd (w i)))
    (hb : ∀ i, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (b i)) = ι (Multiplicative.ofAdd (z i)))
    (hgen : AddSubgroup.closure (Set.range w ∪ Set.range z) = ⊤)
    (hR : (E : Set (ModelResidue M)).Definable Language.ring (rvNormalizedMapRelation f a b))
    (x y : Fin n → ModelResidue M) (hx : AlgebraicIndependent E x)
    (hxy : Sum.elim x y ∈ rvNormalizedMapRelation f a b) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, IsUnit C.det ∧ ∀ i, z i = ∑ j, C i j • w j := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  have hu := rvNormalizedMapRelation_functional f a b
  have hv := fun t ht => rvNormalizedMapRelation_inverse_functional f hf a b x t y hxy ht
  have hy := acf_definable_bijection_target_independent E (rvNormalizedMapRelation f a b) hR x y hxy
    (fun t ht => hu x t y ht hxy) hv hx
  exact acf_definable_diagonal_monomial_weights E H (rvNormalizedMapRelation f a b) hR x y hxy hu hv hx hy w z hgen
    (fun χ => rvNormalizedMapRelation_weight_character_invariant E ι hι f a b w z ha hb x y hxy χ)

/-- Applying the classified matrix in the original value quotient
recovers actual original-ground RV coefficients, not new root choices. -/
theorem rvNormalizedMapRelation_original_coefficients {W : Type*} [AddCommGroup W]
    (E : Subfield (ModelResidue M)) [IsAlgClosed E] (H : ReichsteinYoussinInput E W)
    (ι : Multiplicative W →* (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B))
    (hι : Function.Injective ι) (f : GammaGroundMap A D) (hf : Function.Injective f)
    (a b : Fin n → (CanonicalRV.RVSort M)ˣ) (w z : Fin n → W)
    (ha : ∀ i, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (a i)) = ι (Multiplicative.ofAdd (w i)))
    (hb : ∀ i, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (b i)) = ι (Multiplicative.ofAdd (z i)))
    (hgen : AddSubgroup.closure (Set.range w ∪ Set.range z) = ⊤)
    (hR : (E : Set (ModelResidue M)).Definable Language.ring (rvNormalizedMapRelation f a b))
    (x y : Fin n → ModelResidue M) (hx : AlgebraicIndependent E x)
    (hxy : Sum.elim x y ∈ rvNormalizedMapRelation f a b) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, ∃ c : Fin n → (CanonicalRV.RVSort M)ˣ,
      IsUnit C.det ∧ (∀ i, DefinableClosureAtBase B .rv (rvUnitValues c i)) ∧
      rvUnitTupleValues b = rvUnitTupleValues c * integerMonomialMap C (rvUnitTupleValues a) ∧
      GammaGroundDefinable hc B (rawRVUnitSpace n) {c} := by
  obtain ⟨C,hC,hweights⟩ := rvNormalizedMapRelation_monomial_weights E H ι hι f hf a b w z ha hb hgen hR x y hx hxy
  have hq : ∀ i, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (b i)) =
      integerMonomialMap C (fun j => QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (a j))) i := by
    intro i
    rw [hb i,hweights i,ofAdd_sum,map_prod]
    simp only [ofAdd_zsmul,map_zpow,integerMonomialMap]
    apply Finset.prod_congr rfl
    intro j _
    rw [ha j]
  obtain ⟨c,hc,hv,hdef⟩ := gammaGroundTorusWeight_coefficients (hc := hc) (rvUnitTupleValues a) (rvUnitTupleValues b) C hq
  exact ⟨C,c,hC,hc,hv,hdef⟩

end DiamondIntegral.Section3
