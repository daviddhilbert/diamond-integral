import Section3.GuardedRVTerms
import Section4.RVCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GuardedRVNormalForm
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def rvIntegerMonomialTerm (e : Fin n → ℤ) : LRV.Term (Fin n) :=
  (RVExpr.variableWord (Finsupp.equivFunOnFinite.symm e) : RVExpr Empty Empty (Fin n)).toTerm Empty.elim Empty.elim id

theorem rvIntegerMonomialTerm_realize (e : Fin n → ℤ) (x : Fin n → CanonicalRV.RVSort M) :
    (rvIntegerMonomialTerm e).realize (rvValues x) = (∏ j, x j ^ e j).val := by
  have hh := RVExpr.toTerm_realize (M := M) (Empty.elim : Empty → Fin n) Empty.elim id
    (rvValues x) (Empty.elim : Empty → VFType (M := M)) (Empty.elim : Empty → CanonicalRV.RVSort M)
    x (fun i => i.elim) (fun i => i.elim) (fun _ => rfl)
    (RVExpr.variableWord (Finsupp.equivFunOnFinite.symm e))
  rw [RVExpr.eval_variableWord,Finsupp.prod_zpow] at hh
  exact hh

def rvIntegerMonomialRawMap (A : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → M) : Fin n → M :=
  fun i => (rvIntegerMonomialTerm (A i)).realize z

theorem rvIntegerMonomialRawMap_definable (S : Set M) (A : Matrix (Fin n) (Fin n) ℤ) :
    S.DefinableMap LRV (rvIntegerMonomialRawMap A : (Fin n → M) → (Fin n → M)) :=
  fun i => Set.DefinableFun.of_empty (rvIntegerMonomialTerm (A i)).definableFun_realize

theorem rvIntegerMonomialRawMap_values (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → CanonicalRV.RVSort M) :
    rvIntegerMonomialRawMap A (rvValues x) = rvValues (fun i => ∏ j, x j ^ A i j) := by
  funext i
  exact rvIntegerMonomialTerm_realize (A i) x
end DiamondIntegral.Section3
