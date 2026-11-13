import «section 4».GammaSumMap
import «section 4».GammaHigherPushforward

/-! Actual inner fibre integration for a sum of two Gamma target maps.
This is the weighted section computation needed for convolution products. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaSumFibres
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaSumMap GammaIntegerFamilies
open GammaHigherPushforward GammaProductFamilies GammaPrefixIntegration GammaIntegralCongruence
open GammaParameterExtension GammaBaseExtension GammaBlockSlices GammaIteratedIntegral FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem prefix_sum_fibre (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n m : ℕ)
    (T : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) (hU : MapDefinable B U)
    (f : familySubgroup B m) (g : familySubgroup B n) (c : Values.Gamma (M := M))
    (y : Fin n → Values.Gamma (M := M)) :
    (integratePrefix h00 hκ hs (withGamma B (Set.range ![c])) hr
      (finite_gamma_extension_small hκ B hγ ![c]) k n m
      (fibreFamily B (sumMap T U) (graph_of_mapDefinable B _ (sumMap_definable B T U hT hU))
        (productFamily B f g) c)).val y =
    (pushforward h00 hκ hs B hr hγ k T (graph_of_mapDefinable B T hT) f).val
      (toPaperGamma (c * (U y)⁻¹)) * g.val y := by
  let C := withGamma B (Set.range ![c])
  have hrC : Cardinal.mk C.real < κ := hr
  have hγC : Cardinal.mk C.gamma < κ := finite_gamma_extension_small hκ B hγ ![c]
  let H := fibreFamily B (sumMap T U) (graph_of_mapDefinable B _ (sumMap_definable B T U hT hU))
    (productFamily B f g) c
  have hp := integratePrefix_fibre h00 hκ hs C hrC hγC k n m H y
  let D := withGamma C (Set.range y)
  have hγD : Cardinal.mk D.gamma < κ := finite_gamma_extension_small hκ C hγC y
  have hrD : Cardinal.mk D.real < κ := hr
  let d := c * (U y)⁻¹
  let A := withGamma B (Set.range ![d])
  have hγA : Cardinal.mk A.gamma < κ := finite_gamma_extension_small hκ B hγ ![d]
  have hrA : Cardinal.mk A.real < κ := hr
  let F := fibreFamily B T (graph_of_mapDefinable B T hT) f d
  let Q : familySubgroup D m := ⟨slice H.val y, slice_definable C n m H.val H.property y⟩
  have he (u : Fin m → Values.Gamma (M := M)) : Q.val u = ((g.val y) • F).val u := by
    change H.val (join n m u y) = (g.val y) • F.val u
    rw [fibreFamily_eval, fibreFamily_eval, sumMap_join, productFamily_join]
    have hiff : T u * U y = c ↔ T u = d := eq_mul_inv_iff_mul_eq.symm
    simp only [hiff]
    by_cases ht : T u = d
    · simp only [ht, ite_true, zsmul_eq_mul, Int.cast_id]
      exact mul_comm _ _
    · simp only [ht, ite_false, zsmul_zero]
  have hi := integrateAll_congr h00 hκ hs D A hrD hγD hrA hγA k m Q ((g.val y) • F) he
  calc
    _ = integrateAll h00 hκ hs D hrD hγD k m Q := hp
    _ = integrateAll h00 hκ hs A hrA hγA k m ((g.val y) • F) := hi
    _ = _ := by
      have hv : integrateAll h00 hκ hs A hrA hγA k m F =
          (pushforward h00 hκ hs B hr hγ k T (graph_of_mapDefinable B T hT) f).val (toPaperGamma d) :=
        (pushforward_eval h00 hκ hs B hr hγ k T (graph_of_mapDefinable B T hT) f d).symm
      rw [map_zsmul, hv]
      simp only [zsmul_eq_mul, Int.cast_id, mul_comm]
      rfl

end DiamondIntegral.Section4.GammaSumFibres
