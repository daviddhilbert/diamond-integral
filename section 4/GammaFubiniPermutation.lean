import «section 4».GammaParametricFubini
import «section 4».GammaCoordinatePullback
import «section 4».FinitePermutationGeneration

/-! The actual iterated Gamma integral is invariant under every coordinate
permutation. The proof uses parametric two-coordinate Fubini and induction;
no higher-dimensional Fubini theorem is taken as an input. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFubiniPermutation
open GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaIteratedIntegral
open GammaParametricFubini GammaCoordinatePullback

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
  (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
  (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
  (k : EulerKind)

def integralStabilizer (n : ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {π : Equiv.Perm (Fin n) | ∀ f, integrateAll h00 hκ hs B hr hγ k n (pullback B π f) =
    integrateAll h00 hκ hs B hr hγ k n f}
  one_mem' := by intro f; rfl
  mul_mem' := by
    intro σ τ hσ hτ f
    exact (hσ (pullback B τ f)).trans (hτ f)
  inv_mem' := by
    intro σ hσ f
    have h := hσ (pullback B (σ⁻¹ : Equiv.Perm (Fin n)) f)
    have he : pullback B σ (pullback B (σ⁻¹ : Equiv.Perm (Fin n)) f) = f := by
      apply Subtype.ext
      funext z
      change f.val ((z ∘ σ) ∘ (σ⁻¹ : Equiv.Perm (Fin n))) = f.val z
      apply congrArg f.val
      funext i
      simp
    rw [he] at h
    exact h.symm

theorem integral_front_swap
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (hΓ : Section2.NontrivialDefinableGamma B) (n : ℕ) (f : familySubgroup B (n + 2)) :
    integrateAll h00 hκ hs B hr hγ k (n + 2) (pullback B (swapFirstTwoIndex n) f) =
      integrateAll h00 hκ hs B hr hγ k (n + 2) f := by
  have hf : IntegerFamilyDefinable B f.val := f.property
  have he : integrateFirst h00 hκ hs B hr hγ k n
      (integrateFirst h00 hκ hs B hr hγ k (n + 1) (pullback B (swapFirstTwoIndex n) f)) =
      integrateFirst h00 hκ hs B hr hγ k n (integrateFirst h00 hκ hs B hr hγ k (n + 1) f) := by
    apply Subtype.ext
    funext y
    exact (commute_first_two h00 linear hκ hs B hr hγ hΓ k f.val hf y).symm
  exact congrArg (integrateAll h00 hκ hs B hr hγ k n) he

theorem lift_eq_keepFirst {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (FinitePermutationGeneration.lift e : Fin (n + 1) → Fin (n + 1)) = keepFirst e := by
  funext i
  exact Fin.cases (by simp [keepFirst]) (fun j => by simp [keepFirst]) i

theorem front_swap_eq (n : ℕ) :
    (Equiv.swap (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ : Fin (n + 2) → Fin (n + 2)) =
      swapFirstTwoIndex n := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
  · change Equiv.swap (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ 0 = (0 : Fin (n + 1)).succ
    exact Equiv.swap_apply_left _ _
  · change Equiv.swap (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ (0 : Fin (n + 1)).succ = 0
    exact Equiv.swap_apply_right _ _
  · change Equiv.swap (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ l.succ.succ = l.succ.succ
    apply Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
    exact fun h => Fin.succ_ne_zero l (Fin.succ_injective _ h)

theorem permutation_mem
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (hΓ : Section2.NontrivialDefinableGamma B) :
    ∀ n (π : Equiv.Perm (Fin n)), π ∈ integralStabilizer h00 hκ hs B hr hγ k n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro π; have : π = 1 := Subsingleton.elim _ _; simp [this]
  | one => intro π; have : π = 1 := Subsingleton.elim _ _; simp [this]
  | more n _ ih =>
    apply FinitePermutationGeneration.all_mem
    · intro e f
      have hn := congrArg (fun H => H f) (integrateFirst_naturality h00 hκ hs B hr hγ k e)
      change integrateFirst h00 hκ hs B hr hγ k (n + 1) (pullback B (keepFirst e) f) =
        pullback B e (integrateFirst h00 hκ hs B hr hγ k (n + 1) f) at hn
      change integrateAll h00 hκ hs B hr hγ k (n + 1)
        (integrateFirst h00 hκ hs B hr hγ k (n + 1) (pullback B (FinitePermutationGeneration.lift e) f)) = _
      rw [lift_eq_keepFirst, hn]
      exact ih e (integrateFirst h00 hκ hs B hr hγ k (n + 1) f)
    · intro f
      change integrateAll h00 hκ hs B hr hγ k (n + 2)
        (pullback B (Equiv.swap 0 (0 : Fin (n + 1)).succ) f) = _
      rw [front_swap_eq]
      exact integral_front_swap h00 hκ hs B hr hγ k linear hΓ n f

theorem integrateAll_permutation
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (hΓ : Section2.NontrivialDefinableGamma B) (n : ℕ) (π : Equiv.Perm (Fin n))
    (f : familySubgroup B n) :
    integrateAll h00 hκ hs B hr hγ k n (pullback B π f) =
      integrateAll h00 hκ hs B hr hγ k n f :=
  permutation_mem h00 hκ hs B hr hγ k linear hΓ n π f

theorem integrateAll_equiv
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (hΓ : Section2.NontrivialDefinableGamma B) (a b : ℕ) (e : Fin a ≃ Fin b)
    (f : familySubgroup B a) :
    integrateAll h00 hκ hs B hr hγ k b (pullback B e f) =
      integrateAll h00 hκ hs B hr hγ k a f := by
  have hab : a = b := by simpa using Fintype.card_congr e
  subst b
  exact integrateAll_permutation h00 hκ hs B hr hγ k linear hΓ a e f

end DiamondIntegral.Section4.GammaFubiniPermutation
