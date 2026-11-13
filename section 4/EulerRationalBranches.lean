module

public import «section 4».EulerUnaryPushforward
public import Mathlib.GroupTheory.Divisible
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.GroupTheory.ArchimedeanDensely

/-! Rational-affine power laws give genuine increasing, decreasing or
constant unary branches in a divisible ordered Gamma group. The branch
classification is proved from the power equation, with no linearity input. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [RootableBy G ℕ]

def positivePowerIso (n : ℕ) (hn : n ≠ 0) : G ≃o G where
  toFun x := x ^ n
  invFun x := RootableBy.root x n
  left_inv x := HasUniqueRoots.pow_left_injective hn (RootableBy.root_cancel (x ^ n) hn)
  right_inv x := RootableBy.root_cancel x hn
  map_rel_iff' := pow_le_pow_iff_left hn

def positiveRationalAffineIso (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (c : G) : G ≃o G :=
  ((positivePowerIso p hp).trans (OrderIso.mulLeft c)).trans (positivePowerIso q hq).symm

theorem positiveRationalAffineIso_spec (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (c x : G) :
    positiveRationalAffineIso p q hp hq c x ^ q = c * x ^ p :=
  RootableBy.root_cancel (c * x ^ p) hq

theorem power_law_branch (p : ℤ) (q : ℕ) (hq : q ≠ 0) (c : G) :
    ∃ b : UnaryBranch (Additive G) (Additive G), ∀ x y : G,
      y ^ q = c * x ^ p → b.apply (Additive.ofMul x) = Additive.ofMul y := by
  rcases lt_trichotomy 0 p with hp | hp | hp
  · have hp0 : p ≠ 0 := ne_of_gt hp
    let e := positiveRationalAffineIso p.natAbs q (Int.natAbs_ne_zero.mpr hp0) hq c
    refine ⟨.increasing (show Additive G ≃o Additive G from e), ?_⟩
    intro x y hxy
    change e x = y
    apply HasUniqueRoots.pow_left_injective hq
    change positiveRationalAffineIso p.natAbs q (Int.natAbs_ne_zero.mpr hp0) hq c x ^ q = y ^ q
    rw [positiveRationalAffineIso_spec]
    have hpow : x ^ p.natAbs = x ^ p := by
      rw [← zpow_natCast, Int.natCast_natAbs, abs_of_pos hp]
    rw [hpow]
    exact hxy.symm
  · subst p
    refine ⟨.constant (Additive.ofMul (RootableBy.root c q)), ?_⟩
    intro x y hxy
    change RootableBy.root c q = y
    apply HasUniqueRoots.pow_left_injective hq
    change RootableBy.root c q ^ q = y ^ q
    rw [RootableBy.root_cancel c hq]
    simpa only [zpow_zero, mul_one] using hxy.symm
  · have hp0 : p ≠ 0 := ne_of_lt hp
    let e := positiveRationalAffineIso p.natAbs q (Int.natAbs_ne_zero.mpr hp0) hq c
    refine ⟨.decreasing (show Additive G ≃o Additive G from e), ?_⟩
    intro x y hxy
    change e x⁻¹ = y
    apply HasUniqueRoots.pow_left_injective hq
    change positiveRationalAffineIso p.natAbs q (Int.natAbs_ne_zero.mpr hp0) hq c x⁻¹ ^ q = y ^ q
    rw [positiveRationalAffineIso_spec]
    have hpow : (x⁻¹) ^ p.natAbs = x ^ p := by
      rw [← zpow_natCast, Int.natCast_natAbs, abs_of_neg hp, zpow_neg, inv_zpow, inv_inv]
    rw [hpow]
    exact hxy.symm

variable [DenselyOrdered G] [Nontrivial G]

theorem exists_pushforward_of_power_laws {ι : Type*} (k : EulerKind) (s : Finset ι)
    (p : ι → ℤ) (q : ι → ℕ) (c : ι → G) (hq : ∀ i, q i ≠ 0)
    (T : G → G) (w : ι → EulerFunction k (Additive G))
    (hcover : ∀ i ∈ s, ∀ x : G, w i (Additive.ofMul x) ≠ 0 →
      T x ^ q i = c i * x ^ p i) :
    ∃ P : EulerFunction k (Additive G), ∃ F : Additive G → EulerFunction k (Additive G),
      (∀ y x, F y x = if Additive.ofMul (T (Additive.toMul x)) = y
        then (∑ i ∈ s, w i) x else 0) ∧
      (∀ y, P y = totalEuler k (F y)) ∧
      totalEuler k P = totalEuler k (∑ i ∈ s, w i) := by
  choose b hb using (fun i => power_law_branch (p i) (q i) (hq i) (c i))
  let T' : Additive G → Additive G := fun x => Additive.ofMul (T (Additive.toMul x))
  have hT : ∀ i ∈ s, ∀ x : Additive G, w i x ≠ 0 → (b i).apply x = T' x := by
    intro i hi x hx
    exact hb i (Additive.toMul x) (T (Additive.toMul x))
      (hcover i hi (Additive.toMul x) hx)
  refine ⟨unaryPushforward k s b w, unaryFibre k s b w, ?_, ?_, ?_⟩
  · intro y x
    exact unaryFibre_eval_of_compatible k s b w T' hT y x
  · intro y
    exact unaryPushforward_eval k s b w y
  · exact unary_pushforward_fubini k s b w

end DiamondIntegral.Section4.EulerFunction
