import «section 3».RVMonomialSyntax
import «section 3».IntegerMonomialMaps
import «section 3».RVZeroStrata
import Mathlib.Algebra.GroupWithZero.Units.Equiv
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def rvMonomialSetMap (S : Set M) (A : Matrix (Fin n) (Fin n) ℤ)
    (X : DefSet (rawRVSpace (M := M) n) S) : Map X (DefSet.univ (rawRVSpace n) S) := by
  let f (x : Fin n → CanonicalRV.RVSort M) := fun i => ∏ j, x j ^ A i j
  have hval (c : (rawRVSpace (M := M) n).domain) :
      rvIntegerMonomialRawMap A c.val = rvValues (f ((rawRVSpace n).decode c)) := by
    have hh := rvIntegerMonomialRawMap_values A ((rawRVSpace n).decode c)
    rwa [rvValues_decode] at hh
  have hdom (c : (rawRVSpace (M := M) n).domain) :
      rvIntegerMonomialRawMap A c.val ∈ (rawRVSpace (M := M) n).domain :=
    ⟨f ((rawRVSpace n).decode c),(hval c).symm⟩
  refine Map.ofCodes X f (rvIntegerMonomialRawMap A) (rvIntegerMonomialRawMap_definable S A) hdom ?_
  intro c
  exact rvValues_injective ((rvValues_decode ⟨_,hdom c⟩).trans (hval c))

def rvTorusUnitsEquiv (S : Set M) (n : ℕ) :
    rvZeroPattern (M := M) S (∅ : Set (Fin n)) ≃ (Fin n → (CanonicalRV.RVSort M)ˣ) where
  toFun a i := Units.mk0 (a.val i) (by
    intro h
    have he : (a.val i).val = iRVZero := (congrArg Subtype.val h).trans RVOperations.zero_val
    exact (a.property i).mp he)
  invFun x := ⟨fun i => (x i : CanonicalRV.RVSort M),fun i => ⟨fun h =>
    Units.ne_zero (x i) (Subtype.ext (h.trans RVOperations.zero_val.symm)),False.elim⟩⟩
  left_inv a := Subtype.ext rfl
  right_inv x := by funext i; exact Units.ext rfl

def rvMonomialTorusMap (S : Set M) (A : Matrix (Fin n) (Fin n) ℤ) :
    Map (rvZeroPattern (M := M) S (∅ : Set (Fin n))) (rvZeroPattern S (∅ : Set (Fin n))) := by
  let f := rvMonomialSetMap S A (rvZeroPattern S (∅ : Set (Fin n)))
  apply f.corestrict
  intro a i
  refine ⟨?_,False.elim⟩
  intro he
  have hn : ∀ j, a.val j ≠ 0 := fun j h => (a.property j).mp
    ((congrArg Subtype.val h).trans RVOperations.zero_val)
  have hz : (∏ j, a.val j ^ A i j) = (0 : CanonicalRV.RVSort M) :=
    Subtype.ext (he.trans RVOperations.zero_val.symm)
  exact (Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (hn j))) hz

/-- Every integral monomial change with an integral inverse is an actual
same-ground definable bijection of nonzero RV tuples. -/
def rvMonomialTorusBijection (S : Set M) (A B : Matrix (Fin n) (Fin n) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    DefinableBijection (rvZeroPattern (M := M) S (∅ : Set (Fin n))) (rvZeroPattern S (∅ : Set (Fin n))) where
  map := rvMonomialTorusMap S A
  bijective := by
    let E := (rvTorusUnitsEquiv (M := M) S n).trans
      ((integerMonomialEquiv A B hAB hBA).toEquiv.trans (rvTorusUnitsEquiv S n).symm)
    have he : (fun a => rvMonomialTorusMap S A a) = (fun a => E a) := by
      funext a
      apply Subtype.ext
      funext i
      change (∏ j, a.val j ^ A i j) =
        ((∏ j, (rvTorusUnitsEquiv (M := M) S n a j) ^ A i j : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M)
      simp only [Units.coe_prod,Units.val_zpow_eq_zpow_val]
      rfl
    change Function.Bijective (fun a => rvMonomialTorusMap S A a)
    rw [he]
    exact E.bijective
end DiamondIntegral.Section3
