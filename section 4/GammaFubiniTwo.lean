import «section 4».GammaKernelDecomposition

/-! Two-coordinate Fubini for actual finite-range original-base definable
integer functions on Gamma squared. The canonical kernel decomposition
and every unary projection witness are constructed, not assumed.
The authorized Gamma-linearity background is an explicit argument. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFubiniTwo
open GammaDefinableEuler GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies
open GammaIteratedIntegral GammaKernelDecomposition EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def swapFamily (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) :
    (Fin 2 → Values.Gamma (M := M)) → ℤ := fun z => f (z ∘ (![1, 0] : Fin 2 → Fin 2))

theorem swapFamily_definable (B : Base (M := M))
    (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    IntegerFamilyDefinable B (swapFamily f) := reindex_definable B f hf ![1, 0]

theorem vertical_inner (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (K : KernelDecomposition h00 B k f hf) (y : Values.Gamma (M := M)) :
    integralFirst h00 B k f hf ![y] =
      kernelVertical k Finset.univ K.constant K.point K.ray (toPaperGamma y) := by
  change totalEuler k (fibreFunction h00 B k f hf ![y]) = _
  rw [K.column y]
  exact kernelColumn_integral k Finset.univ K.constant K.point K.ray K.transform (toPaperGamma y)

theorem swapped_fibre (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (K : KernelDecomposition h00 B k f hf) (x : Values.Gamma (M := M)) :
    fibreFunction h00 B k (swapFamily f) (swapFamily_definable B f hf) ![x] =
      kernelRow k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData (toPaperGamma x) := by
  apply eval_injective k
  funext t
  obtain ⟨y, rfl⟩ := toPaperGamma.surjective t
  change fibreFunction h00 B k (swapFamily f) (swapFamily_definable B f hf) ![x] (toPaperGamma y) = _
  calc
    fibreFunction h00 B k (swapFamily f) (swapFamily_definable B f hf) ![x] (toPaperGamma y) =
        swapFamily f (Fin.cons y ![x]) := fibreFunction_eval h00 B k _ _ ![x] y
    _ = f (Fin.cons x ![y]) := by
      unfold swapFamily
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = fibreFunction h00 B k f hf ![y] (toPaperGamma x) := (fibreFunction_eval h00 B k f hf ![y] x).symm
    _ = kernelColumn k Finset.univ K.constant K.point K.ray K.transform (toPaperGamma y) (toPaperGamma x) :=
      congrArg (fun F : EulerFunction k (PaperGamma (M := M)) => F (toPaperGamma x)) (K.column y)
    _ = kernelRow k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData
        (toPaperGamma x) (toPaperGamma y) :=
      (kernelRow_eval k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData
        (toPaperGamma x) (toPaperGamma y)).symm

theorem horizontal_inner (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (K : KernelDecomposition h00 B k f hf) (x : Values.Gamma (M := M)) :
    integralFirst h00 B k (swapFamily f) (swapFamily_definable B f hf) ![x] =
      kernelHorizontal k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData (toPaperGamma x) := by
  change totalEuler k (fibreFunction h00 B k (swapFamily f) (swapFamily_definable B f hf) ![x]) = _
  rw [swapped_fibre h00 B k f hf K x]
  exact kernelRow_integral k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData (toPaperGamma x)

theorem fubini_two (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (f : (Fin 2 → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    integrateAll h00 hκ hs B hr hγ k 2 ⟨f, hf⟩ =
      integrateAll h00 hκ hs B hr hγ k 2 ⟨swapFamily f, swapFamily_definable B f hf⟩ := by
  obtain ⟨K⟩ := exists_kernelDecomposition h00 linear hκ hs B hr hγ hΓ k f hf
  let fv := integrateFirst h00 hκ hs B hr hγ k 1 ⟨f, hf⟩
  let fh := integrateFirst h00 hκ hs B hr hγ k 1 ⟨swapFamily f, swapFamily_definable B f hf⟩
  have hV := integrateAll_unary_from_euler h00 hκ hs B hr hγ k fv
    (kernelVertical k Finset.univ K.constant K.point K.ray) (vertical_inner h00 B k f hf K)
  have hH := integrateAll_unary_from_euler h00 hκ hs B hr hγ k fh
    (kernelHorizontal k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData)
    (horizontal_inner h00 B k f hf K)
  calc
    integrateAll h00 hκ hs B hr hγ k 2 ⟨f, hf⟩ = integrateAll h00 hκ hs B hr hγ k 1 fv := rfl
    _ = totalEuler k (kernelVertical k Finset.univ K.constant K.point K.ray) := hV
    _ = totalEuler k (kernelHorizontal k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData) :=
      kernel_fubini k Finset.univ K.constant K.point K.ray K.transform K.pointData K.rayData
    _ = integrateAll h00 hκ hs B hr hγ k 1 fh := hH.symm
    _ = integrateAll h00 hκ hs B hr hγ k 2 ⟨swapFamily f, swapFamily_definable B f hf⟩ := rfl

end DiamondIntegral.Section4.GammaFubiniTwo
