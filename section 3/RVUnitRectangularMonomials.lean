import «section 3».RVUnitSpace
import «section 3».RVMonomialSyntax
import «section 3».IntegerMonomialMaps
import «section 3».GammaGroundMapRestrictions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

def rvUnitRectangularMonomialCode (A : Matrix (Fin n) (Fin m) ℤ) (z : Fin m → M) : Fin n → M :=
  fun i => (rvIntegerMonomialTerm (A i)).realize z

theorem rvUnitRectangularMonomialCode_values (A : Matrix (Fin n) (Fin m) ℤ)
    (x : Fin m → (CanonicalRV.RVSort M)ˣ) :
    rvUnitRectangularMonomialCode A (rvUnitValues x) = rvUnitValues (integerMonomialMap A x) := by
  funext i
  have ht := rvIntegerMonomialTerm_realize (A i) (fun j => (x j : CanonicalRV.RVSort M))
  change (rvIntegerMonomialTerm (A i)).realize (rvUnitValues x) =
    (((∏ j, (x j) ^ A i j : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M)).val
  change (rvIntegerMonomialTerm (A i)).realize (rvUnitValues x) = (∏ j, (x j : CanonicalRV.RVSort M) ^ A i j).val at ht
  rw [ht]
  congr 1
  simp only [Units.coe_prod,Units.val_zpow_eq_zpow_val]

/-- Every rectangular integral monomial map has its actual parameter-free
RV-unit code graph, in arbitrary source and target ambient arities. -/
def rvUnitRectangularMonomialMap (S : Set M) (A : Matrix (Fin n) (Fin m) ℤ) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) m) S) (DefSet.univ (rawRVUnitSpace n) S) := by
  let F := rvUnitRectangularMonomialCode (M := M) A
  have hc (c : (rawRVUnitSpace (M := M) m).domain) : F c.val =
      rvUnitValues (integerMonomialMap A ((rawRVUnitSpace m).decode c)) := by
    have h := rvUnitRectangularMonomialCode_values A ((rawRVUnitSpace m).decode c)
    rwa [rvUnitValues_decode] at h
  have hd (c : (rawRVUnitSpace (M := M) m).domain) : F c.val ∈ (rawRVUnitSpace (M := M) n).domain :=
    ⟨integerMonomialMap A ((rawRVUnitSpace m).decode c),(hc c).symm⟩
  refine Map.ofCodes _ (integerMonomialMap A) F
    (fun i => Set.DefinableFun.of_empty (rvIntegerMonomialTerm (A i)).definableFun_realize) hd ?_
  intro c
  apply rvUnitValues_injective
  exact (rvUnitValues_decode _).trans (hc c)

def gammaGroundRVUnitRectangularMonomialMap {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (A : Matrix (Fin n) (Fin m) ℤ) :
    GammaGroundMap R (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) :=
  GammaGroundMap.ofGlobal _ _ (rvUnitRectangularMonomialMap B.real A) (fun _ => Set.mem_univ _)
end DiamondIntegral.Section3
