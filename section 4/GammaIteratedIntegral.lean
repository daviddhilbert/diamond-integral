import «section 4».GammaWeightedFamilies
import «section 4».GammaIndicators

/-! Iterated actual coordinate integration in a fixed order. Each step
preserves original-base definability. Coordinate-order independence is a
separate Fubini theorem, not an assumption of this construction. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaIteratedIntegral
open GammaDefinableEuler GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaIndicators
open EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def emptyTuple : Fin 0 → Values.Gamma (M := M) := fun i => Fin.elim0 i

def evaluateZero (B : Base (M := M)) : familySubgroup B 0 →+ ℤ where
  toFun f := f.val emptyTuple
  map_zero' := rfl
  map_add' _ _ := rfl

def unaryFunction (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (f : (Fin 1 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    EulerFunction k (PaperGamma (M := M)) := fibreFunction h00 B k f hf emptyTuple

theorem unaryFunction_eval (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (f : (Fin 1 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (γ : Values.Gamma (M := M)) : unaryFunction h00 B k f hf (toPaperGamma γ) = f ![γ] := by
  rw [unaryFunction, fibreFunction_eval]
  congr 1

def integrateAll (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) : (n : ℕ) → familySubgroup B n →+ ℤ
  | 0 => evaluateZero B
  | n + 1 => (integrateAll h00 hκ hs B hr hγ k n).comp (integrateFirst h00 hκ hs B hr hγ k n)

theorem integrateAll_unary (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (f : familySubgroup B 1) :
    integrateAll h00 hκ hs B hr hγ k 1 f =
      totalEuler k (fibreFunction h00 B k f.val f.property emptyTuple) := rfl

theorem integrateAll_unary_from_euler (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (f : familySubgroup B 1) (F : EulerFunction k (PaperGamma (M := M)))
    (hF : ∀ γ : Values.Gamma (M := M), f.val ![γ] = F (toPaperGamma γ)) :
    integrateAll h00 hκ hs B hr hγ k 1 f = totalEuler k F := by
  have hf : IntegerFamilyDefinable B f.val := f.property
  rw [integrateAll_unary]
  apply congrArg (totalEuler k)
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change unaryFunction h00 B k f.val hf (toPaperGamma γ) = F (toPaperGamma γ)
  exact (unaryFunction_eval h00 B k f.val hf γ).trans (hF γ)

theorem integrateAll_scissor (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (R S : Set (Fin n → Values.Gamma (M := M)))
    (hR : GammaOrderLogic.GammaDefinable B R) (hS : GammaOrderLogic.GammaDefinable B S)
    (hU : GammaOrderLogic.GammaDefinable B (R ∪ S)) (hI : GammaOrderLogic.GammaDefinable B (R ∩ S)) :
    integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B (R ∪ S) hU) +
      integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B (R ∩ S) hI) =
    integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B R hR) +
      integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B S hS) := by
  have h := congrArg (integrateAll h00 hκ hs B hr hγ k n) (indicator_scissor B R S hR hS hU hI)
  simpa only [map_add] using h

end DiamondIntegral.Section4.GammaIteratedIntegral
