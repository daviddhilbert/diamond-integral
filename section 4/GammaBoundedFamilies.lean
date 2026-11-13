import «section 4».GammaIteratedIntegral
import «section 4».EulerBoundedComparison

/-! Both actual iterated Euler integrals agree on every finite-dimensional
integer family supported in a bounded box. No Fubini theorem or Gamma
linearity input is needed for this comparison. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedFamilies
open GammaDefinableEuler GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies
open GammaIteratedIntegral EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def BoxSupported {n : ℕ} (a b : Values.Gamma (M := M))
    (f : (Fin n → Values.Gamma (M := M)) → ℤ) : Prop :=
  ∀ z, f z ≠ 0 → ∀ i, a ≤ z i ∧ z i ≤ b

theorem fibreFunction_bounded (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (a b : Values.Gamma (M := M)) (hb : BoxSupported a b f) (y : Fin n → Values.Gamma (M := M)) :
    IsDoublyBounded (fibreFunction h00 B k f hf y) := by
  refine ⟨toPaperGamma a, toPaperGamma b, ?_⟩
  intro x hx
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  have hnonzero : f (Fin.cons γ y) ≠ 0 := by
    rwa [fibreFunction_eval] at hx
  exact hb (Fin.cons γ y) hnonzero 0

theorem fibreFunction_changeKind (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k l : EulerKind)
    {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) :
    fibreFunction h00 B l f hf y = changeKind k l (fibreFunction h00 B k f hf y) := by
  apply eval_injective l
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change fibreFunction h00 B l f hf y (toPaperGamma γ) =
    changeKind k l (fibreFunction h00 B k f hf y) (toPaperGamma γ)
  rw [changeKind_eval, fibreFunction_eval, fibreFunction_eval]

theorem integralFirst_bounded_comparison (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (k l : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (a b : Values.Gamma (M := M)) (hb : BoxSupported a b f) (y : Fin n → Values.Gamma (M := M)) :
    integralFirst h00 B k f hf y = integralFirst h00 B l f hf y := by
  change totalEuler k _ = totalEuler l _
  rw [fibreFunction_changeKind h00 B k l]
  exact (totalEuler_changeKind k l _ (fibreFunction_bounded h00 B k f hf a b hb y)).symm

theorem integralFirst_boxSupported (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (a b : Values.Gamma (M := M)) (hb : BoxSupported a b f) :
    BoxSupported a b (integralFirst h00 B k f hf) := by
  intro y hy i
  by_contra hout
  have hz (γ : Values.Gamma (M := M)) : f (Fin.cons γ y) = 0 := by
    by_contra hn
    exact hout (hb (Fin.cons γ y) hn i.succ)
  have he : fibreFunction h00 B k f hf y = 0 := by
    apply eval_injective k
    funext x
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    change fibreFunction h00 B k f hf y (toPaperGamma γ) = (0 : EulerFunction k _) (toPaperGamma γ)
    rw [fibreFunction_eval, hz, eval_zero]
  exact hy (by rw [integralFirst, he, map_zero])

theorem integrateAll_bounded_comparison (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k l : EulerKind) (n : ℕ) (f : familySubgroup B n)
    (a b : Values.Gamma (M := M)) (hb : BoxSupported a b f.val) :
    integrateAll h00 hκ hs B hr hγ k n f = integrateAll h00 hκ hs B hr hγ l n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hf : IntegerFamilyDefinable B f.val := f.property
    have hbound : BoxSupported a b (integrateFirst h00 hκ hs B hr hγ k n f).val :=
      integralFirst_boxSupported h00 B k f.val hf a b hb
    have he : integrateFirst h00 hκ hs B hr hγ k n f = integrateFirst h00 hκ hs B hr hγ l n f := by
      apply Subtype.ext
      funext y
      exact integralFirst_bounded_comparison h00 B k l f.val hf a b hb y
    exact (ih _ hbound).trans (congrArg (integrateAll h00 hκ hs B hr hγ l n) he)

end DiamondIntegral.Section4.GammaBoundedFamilies
