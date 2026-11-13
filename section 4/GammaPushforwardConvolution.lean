import «section 4».GammaSumFibres
import «section 4».GammaReflectedFamilies
import «section 4».GammaPushforwardCongruence

/-! Pushforward of an actual product under the sum of its two Gamma maps
is the actual Euler convolution of the pushforwards. All fibre and Fubini
identities used here are proved in the preceding modules. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPushforwardConvolution
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaSumMap GammaSumFibres GammaIntegerFamilies
open GammaHigherPushforward GammaProductFamilies GammaPrefixIntegration GammaIntegralCongruence
open GammaParameterExtension GammaBaseExtension GammaBlockSlices GammaIteratedIntegral FiniteTupleBlocks
open GammaHigherProjection GammaReflectedFamilies GammaUnaryFamilyBridge GammaPushforwardCongruence EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem pushforward_sum_product (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (T : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) (hU : MapDefinable B U)
    (f : familySubgroup B m) (g : familySubgroup B n) :
    (pushforward h00 hκ hs B hr hγ k (sumMap T U)
      (graph_of_mapDefinable B _ (sumMap_definable B T U hT hU)) (productFamily B f g)).val =
    (pushforward h00 hκ hs B hr hγ k T (graph_of_mapDefinable B T hT) f).val *
      (pushforward h00 hκ hs B hr hγ k U (graph_of_mapDefinable B U hU) g).val := by
  apply eval_injective k
  funext x
  obtain ⟨c, rfl⟩ := toPaperGamma.surjective x
  let PF := (pushforward h00 hκ hs B hr hγ k T (graph_of_mapDefinable B T hT) f).val
  let QF := (pushforward h00 hκ hs B hr hγ k U (graph_of_mapDefinable B U hU) g).val
  change (pushforward h00 hκ hs B hr hγ k (sumMap T U)
    (graph_of_mapDefinable B _ (sumMap_definable B T U hT hU)) (productFamily B f g)).val (toPaperGamma c) =
    (PF * QF) (toPaperGamma c)
  rw [pushforward_eval]
  let C := withGamma B (Set.range ![c])
  have hrC : Cardinal.mk C.real < κ := hr
  have hγC : Cardinal.mk C.gamma < κ := finite_gamma_extension_small hκ B hγ ![c]
  have hΓC : Section2.NontrivialDefinableGamma C := nontrivial_extend B (Set.range ![c]) hΓ
  have hc : GammaDefinableClosureAtBase C c := gammaName_extend B (Set.range ![c]) c (Set.mem_range_self (0 : Fin 1))
  let P := pushforwardFamily h00 hκ hs B hr hγ k T (graph_of_mapDefinable B T hT) f
  let PC := extendFamily B (Set.range ![c]) P
  let gC := extendFamily B (Set.range ![c]) g
  have hUC : MapDefinable C U := gammaRelation_extend B (Set.range ![c]) hU
  let R := reflectFamily C c hc PC
  let V := multiplyFamily C gC (unaryCompose C U (graph_of_mapDefinable C U hUC) R)
  let H := fibreFamily B (sumMap T U) (graph_of_mapDefinable B _ (sumMap_definable B T U hT hU))
    (productFamily B f g) c
  have hprefix : integratePrefix h00 hκ hs C hrC hγC k n m H = V := by
    apply Subtype.ext
    funext y
    have h := prefix_sum_fibre h00 hκ hs B hr hγ k n m T U hT hU f g c y
    have heval : PF (toPaperGamma (c * (U y)⁻¹)) = P.val ![c * (U y)⁻¹] := toEuler_eval h00 B k P _
    change (integratePrefix h00 hκ hs C hrC hγC k n m H).val y =
      g.val y * P.val ![c * (U y)⁻¹]
    exact h.trans (by rw [heval, mul_comm])
  have hfactor := congrArg (fun F => F H) (integrateAll_factor h00 hκ hs C hrC hγC k n m)
  have hproj := integral_projection h00 linear hκ hs C hrC hγC hΓC k U
    (graph_of_mapDefinable C U hUC) gC R
  have hQ : (pushforward h00 hκ hs C hrC hγC k U (graph_of_mapDefinable C U hUC) gC).val = QF :=
    pushforward_congr h00 hκ hs C B hrC hγC hr hγ k U U
      (graph_of_mapDefinable C U hUC) (graph_of_mapDefinable B U hU) gC g (fun _ => rfl) (fun _ => rfl)
  calc
    _ = integrateAll h00 hκ hs C hrC hγC k n (integratePrefix h00 hκ hs C hrC hγC k n m H) := hfactor
    _ = integrateAll h00 hκ hs C hrC hγC k n V := congrArg (integrateAll h00 hκ hs C hrC hγC k n) hprefix
    _ = totalEuler k (pointwiseProduct k QF (toEuler h00 C k R).val) := by
      exact hproj.trans (congrArg (fun q => totalEuler k (pointwiseProduct k q (toEuler h00 C k R).val)) hQ)
    _ = convolutionValue k QF PF (toPaperGamma c) := by
      change totalEuler k (pointwiseProduct k QF (toEuler h00 C k (reflectFamily C c hc PC)).val) = _
      rw [reflectFamily_toEuler, toEuler_extend]
      rfl
    _ = _ := by rw [convolutionValue_eq_product, mul_comm]

end DiamondIntegral.Section4.GammaPushforwardConvolution
