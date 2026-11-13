import «section 4».EulerRationalBranches
import «section 4».GammaDefinableMaps
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.MonotoneContinuity

/-! Global rational-affine Gamma branches are continuous in the order
topology and definable over exactly their named Gamma constants. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaTopology
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
scoped instance topology : TopologicalSpace (Values.Gamma (M := M)) := Preorder.topology _
scoped instance orderTopology : OrderTopology (Values.Gamma (M := M)) := ⟨rfl⟩
end DiamondIntegral.Section4.GammaTopology

namespace DiamondIntegral.Section4.GammaRationalAffineContinuity
variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [RootableBy G ℕ]

def rationalAffine {n : ℕ} (p : Fin n → ℤ) (q : ℕ) (hq : q ≠ 0) (c : G)
    (x : Fin n → G) : G :=
  (EulerFunction.positivePowerIso q hq).symm (c * ∏ i, x i ^ p i)

theorem rationalAffine_spec {n : ℕ} (p : Fin n → ℤ) (q : ℕ) (hq : q ≠ 0) (c : G)
    (x : Fin n → G) : rationalAffine p q hq c x ^ q = c * ∏ i, x i ^ p i :=
  RootableBy.root_cancel _ hq

theorem rationalAffine_unique {n : ℕ} (p : Fin n → ℤ) (q : ℕ) (hq : q ≠ 0) (c : G)
    (x : Fin n → G) (y : G) (hy : y ^ q = c * ∏ i, x i ^ p i) :
    rationalAffine p q hq c x = y := by
  apply HasUniqueRoots.pow_left_injective hq
  exact (rationalAffine_spec p q hq c x).trans hy.symm

theorem rationalAffine_continuous [TopologicalSpace G] [OrderTopology G]
    {n : ℕ} (p : Fin n → ℤ) (q : ℕ) (hq : q ≠ 0) (c : G) :
    Continuous (rationalAffine p q hq c) := by
  have hp : Continuous (fun x : Fin n → G => ∏ i, x i ^ p i) :=
    continuous_finset_prod _ (fun i _ => (continuous_apply i).zpow (p i))
  exact (EulerFunction.positivePowerIso q hq).symm.continuous.comp (continuous_const.mul hp)

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
open GammaDefinableMaps

theorem monomial_definable (B : Base (M := M)) {n : ℕ} (p : Fin n → ℤ) :
    MapDefinable B (fun x : Fin n → Values.Gamma (M := M) => ∏ i, x i ^ p i) := by
  have hs (s : Finset (Fin n)) :
      MapDefinable B (fun x : Fin n → Values.Gamma (M := M) => ∏ i ∈ s, x i ^ p i) := by
    induction s using Finset.induction_on with
    | empty => simpa using constant_definable B 1 (GammaGroupNames.one_definable_base B)
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        mul_definable B _ _ (int_power_definable B _ (projection_definable B i) (p i)) ih
  exact hs Finset.univ

theorem rationalAffine_definable (B : Base (M := M)) {n : ℕ} (p : Fin n → ℤ)
    (q : ℕ) (hq : q ≠ 0) (c : Values.Gamma (M := M)) (hc : GammaDefinableClosureAtBase B c) :
    MapDefinable B (rationalAffine p q hq c) :=
  root_definable B _ (mul_definable B _ _ (constant_definable B c hc) (monomial_definable B p)) q hq

structure Branch (B : Base (M := M)) (n : ℕ) where
  exponent : Fin n → ℤ
  denominator : ℕ
  denominator_ne_zero : denominator ≠ 0
  constant : Values.Gamma (M := M)
  constant_definable : GammaDefinableClosureAtBase B constant

def Branch.eval {B : Base (M := M)} {n : ℕ} (a : Branch B n) :
    (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
  rationalAffine a.exponent a.denominator a.denominator_ne_zero a.constant

theorem Branch.definable {B : Base (M := M)} {n : ℕ} (a : Branch B n) : MapDefinable B a.eval :=
  rationalAffine_definable B _ _ _ _ a.constant_definable

open scoped GammaTopology in
theorem Branch.continuous {B : Base (M := M)} {n : ℕ} (a : Branch B n) : Continuous a.eval :=
  rationalAffine_continuous _ _ _ _

end DiamondIntegral.Section4.GammaRationalAffineContinuity
