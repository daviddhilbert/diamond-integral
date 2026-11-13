import «section 4».GammaGraphIntegration
import «section 4».GammaUnaryFamilyBridge

/-! Actual weighted pushforward from Gamma^n to Gamma. It is an additive
map on original-base definable families, its value is the integral of the
actual fibre, and it preserves the total Euler integral. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaHigherPushforward
open GammaDefinableEuler GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies
open GammaIteratedIntegral GammaCoordinatePullback GammaPrefixIntegration GammaFubiniPermutation
open GammaGraphIntegration FiniteTupleBlocks GammaBlockSlices GammaParameterExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
  (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
  (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
  (k : EulerKind)

def pushforwardFamily {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)}) :
    familySubgroup B n →+ familySubgroup B 1 :=
  (integratePrefix h00 hκ hs B hr hγ k 1 n).comp
    ((pullback B (outputToLast n)).comp (graphWeightMap B T hT))

def fibreFamily {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (a : Values.Gamma (M := M)) :
    familySubgroup (GammaBaseExtension.withGamma B (Set.range ![a])) n :=
  let g := pullback B (outputToLast n) (graphWeight B T hT f)
  ⟨slice g.val ![a], slice_definable B 1 n g.val g.property ![a]⟩

theorem fibreFamily_eval {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (a : Values.Gamma (M := M)) (u : Fin n → Values.Gamma (M := M)) :
    (fibreFamily B T hT f a).val u = if T u = a then f.val u else 0 := by
  change (graphWeight B T hT f).val ((join 1 n u ![a]) ∘ outputToLast n) = _
  rw [join_rotate]
  change f.val u * (if a = T u then 1 else 0) = if T u = a then f.val u else 0
  by_cases h : T u = a
  · simp [h]
  · simp [h, Ne.symm h]

theorem pushforwardFamily_fibre {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (a : Values.Gamma (M := M)) :
    (pushforwardFamily h00 hκ hs B hr hγ k T hT f).val ![a] =
      integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range ![a])) hr
        (finite_gamma_extension_small hκ B hγ ![a]) k n (fibreFamily B T hT f a) :=
  integratePrefix_fibre h00 hκ hs B hr hγ k 1 n
    (pullback B (outputToLast n) (graphWeight B T hT f)) ![a]

theorem pushforwardFamily_integral
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (hΓ : Section2.NontrivialDefinableGamma B) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) :
    integrateAll h00 hκ hs B hr hγ k 1 (pushforwardFamily h00 hκ hs B hr hγ k T hT f) =
      integrateAll h00 hκ hs B hr hγ k n f := by
  have hfactor := congrArg (fun H => H (pullback B (outputToLast n) (graphWeight B T hT f)))
    (integrateAll_factor h00 hκ hs B hr hγ k 1 n)
  exact hfactor.symm.trans
    ((integrateAll_equiv h00 hκ hs B hr hγ k linear hΓ (n + 1) (1 + n)
      (outputToLast n) (graphWeight B T hT f)).trans
      (integrate_graphWeight h00 hκ hs B hr hγ k T hT f))

def pushforward {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)}) :
    familySubgroup B n →+ GammaDefinableConvolution.baseSubgroup B k :=
  (GammaUnaryFamilyBridge.toEuler h00 B k).comp (pushforwardFamily h00 hκ hs B hr hγ k T hT)

theorem pushforward_eval {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (a : Values.Gamma (M := M)) :
    (pushforward h00 hκ hs B hr hγ k T hT f).val (toPaperGamma a) =
      integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range ![a])) hr
        (finite_gamma_extension_small hκ B hγ ![a]) k n (fibreFamily B T hT f a) :=
  (GammaUnaryFamilyBridge.toEuler_eval h00 B k _ a).trans
    (pushforwardFamily_fibre h00 hκ hs B hr hγ k T hT f a)

theorem pushforward_integral
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (hΓ : Section2.NontrivialDefinableGamma B) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) :
    EulerFunction.totalEuler k (pushforward h00 hκ hs B hr hγ k T hT f).val =
      integrateAll h00 hκ hs B hr hγ k n f :=
  (GammaUnaryFamilyBridge.toEuler_integral h00 hκ hs B hr hγ k _).trans
    (pushforwardFamily_integral h00 hκ hs B hr hγ k linear hΓ T hT f)

end DiamondIntegral.Section4.GammaHigherPushforward
