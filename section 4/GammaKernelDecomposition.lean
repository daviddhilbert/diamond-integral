import «section 4».GammaCanonicalExpansion
import «section 4».GammaUnaryProjection
import «section 4».GammaPartialMaps
import «section 4».GammaIteratedIntegral
import «section 4».EulerKernelFubini

/-! Actual point-and-ray kernel data for every definable integer function
on Gamma squared. Boundary functions, coefficient families and unary
projection witnesses are all constructed from proved results. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaKernelDecomposition
open GammaOrderLogic GammaDefinableEuler GammaFamilyIntegration GammaWeightedFamilies GammaGermFamilies
open GammaCanonicalExpansion GammaIteratedIntegral GammaUnaryPushforwardMap EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure KernelDecomposition (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) where
  size : ℕ
  constant : EulerFunction k (PaperGamma (M := M))
  point : Fin size → EulerFunction k (PaperGamma (M := M))
  ray : Fin size → EulerFunction k (PaperGamma (M := M))
  transform : Fin size → PaperGamma (M := M) → PaperGamma (M := M)
  pointData : ∀ i, UnaryProjectionData k (transform i) (point i)
  rayData : ∀ i, UnaryProjectionData k (transform i) (ray i)
  column : ∀ y : Values.Gamma (M := M), fibreFunction h00 B k f hf ![y] =
    kernelColumn k Finset.univ constant point ray transform (toPaperGamma y)

theorem exists_kernelDecomposition (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    Nonempty (KernelDecomposition h00 B k f hf) := by
  obtain ⟨A⟩ := GammaWeightedBoundary.exists_boundaryPartition h00 hκ hs B hr hγ k f hf
  let C := unaryFunction h00 B k (tailFamily h00 B k f hf) (tailFamily_definable h00 B k f hf)
  let p := fun i => unaryFunction h00 B k (pointWeight h00 B k f hf A i) (pointWeight_definable h00 B k f hf A i)
  let q := fun i => unaryFunction h00 B k (rayWeight h00 B k f hf A i) (rayWeight_definable h00 B k f hf A i)
  let T := fun i (y : Values.Gamma (M := M)) => GammaPartialMaps.extendMap (A.domain i) (A.function i) 1 ![y]
  have hT (i : Fin A.size) : GammaDefinable B
      {z : Fin 2 → Values.Gamma (M := M) | T i (z 0) = z 1} := by
    have h := GammaPartialMaps.extendMap_definable B _ (A.domain_definable i) _ (A.graph_definable i)
      1 (GammaGroupNames.one_definable_base B)
    let π : Fin 2 → Fin 2 := ![1, 0]
    have ht := GammaRelationLogic.preimage_definable_base B _ h π
    convert ht using 1
    ext z
    have he : (fun j : Fin 1 => z (π j.succ)) = ![z 0] := by
      funext j
      fin_cases j; rfl
    change GammaPartialMaps.extendMap (A.domain i) (A.function i) 1 ![z 0] = z 1 ↔
      GammaPartialMaps.extendMap (A.domain i) (A.function i) 1 (fun j => z (π j.succ)) = z (π 0)
    rw [he]
    rfl
  choose P hPI hPt hPp using (fun i => GammaUnaryProjection.exists_unary_projection h00 linear B hΓ k (T i) (hT i) (p i))
  choose Q hQI hQt hQp using (fun i => GammaUnaryProjection.exists_unary_projection h00 linear B hΓ k (T i) (hT i) (q i))
  let t := fun i => paperMap (T i)
  let PD := fun i => UnaryProjectionData.ofProperties k (t i) (p i) (P i) (hPI i) (hPt i) (hPp i)
  let QD := fun i => UnaryProjectionData.ofProperties k (t i) (q i) (Q i) (hQI i) (hQt i) (hQp i)
  refine ⟨⟨A.size, C, p, q, t, PD, QD, ?_⟩⟩
  intro y
  have hC : C (toPaperGamma y) = tailFamily h00 B k f hf ![y] := unaryFunction_eval h00 B k _ _ y
  have hp (i : Fin A.size) : p i (toPaperGamma y) = pointWeight h00 B k f hf A i ![y] :=
    unaryFunction_eval h00 B k _ _ y
  have hq (i : Fin A.size) : q i (toPaperGamma y) = rayWeight h00 B k f hf A i ![y] :=
    unaryFunction_eval h00 B k _ _ y
  have ht (i : Fin A.size) (hy : ![y] ∈ A.domain i) :
      t i (toPaperGamma y) = toPaperGamma (A.function i ![y]) := by
    change toPaperGamma (GammaPartialMaps.extendMap (A.domain i) (A.function i) 1 ![y]) = _
    rw [GammaPartialMaps.extendMap, ite_eq_left hy]
  have hpoint (i : Fin A.size) :
      pointWeight h00 B k f hf A i ![y] • point k (toPaperGamma (A.function i ![y])) =
        p i (toPaperGamma y) • point k (t i (toPaperGamma y)) := by
    rw [hp]
    by_cases hy : ![y] ∈ A.domain i
    · rw [ht i hy]
    · have hw : pointWeight h00 B k f hf A i ![y] = 0 := by
        simp only [pointWeight, GammaPartialEvaluation.restrictedValue, hy, ite_false]
      rw [hw, zero_zsmul, zero_zsmul]
  have hray (i : Fin A.size) :
      rayWeight h00 B k f hf A i ![y] • ray k (toPaperGamma (A.function i ![y])) =
        q i (toPaperGamma y) • ray k (t i (toPaperGamma y)) := by
    rw [hq]
    by_cases hy : ![y] ∈ A.domain i
    · rw [ht i hy]
    · have hw : rayWeight h00 B k f hf A i ![y] = 0 := by
        simp only [rayWeight, GammaPartialEvaluation.restrictedValue, hy, ite_false]
      rw [hw, zero_zsmul, zero_zsmul]
  rw [fibre_expansion h00 B k f hf A ![y] ]
  unfold kernelColumn
  rw [hC]
  exact congrArg₂ (fun a b => tailFamily h00 B k f hf ![y] • line k + a + b)
    (Finset.sum_congr rfl (fun i _ => hpoint i)) (Finset.sum_congr rfl (fun i _ => hray i))

end DiamondIntegral.Section4.GammaKernelDecomposition
