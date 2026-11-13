import «section 4».GammaBoundedRVProfiles
import «section 4».RVRadiusIdeal
import «section 4».RESOrdinaryPoints
import Mathlib.RingTheory.TensorProduct.Maps

/-! Product comparison and evaluation on the tensor product over integers.
This is not yet the manuscript tensor product over finite Gamma objects:
finite-Gamma balancing, its kernel and global RV descent remain open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBoundedTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Source (B : Base (M := M)) :=
  RESChartRing.Ring B ⊗[ℤ] GammaBoundedRVPresentation.ChartRing B

def comparison (B : Base (M := M)) : Source B →ₐ[ℤ] RVBoundedRing.Ring B :=
  Algebra.TensorProduct.lift (RVBoundedMaps.ofRES B).toIntAlgHom (GammaBoundedRVMaps.sharp B).toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem comparison_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    comparison B (x ⊗ₜ[ℤ] y) = RVBoundedMaps.ofRES B x * GammaBoundedRVMaps.sharp B y := rfl

def evaluation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    Source B →ₐ[ℤ] RESOrdinaryReduction.ReducedRing B :=
  Algebra.TensorProduct.lift (RESOrdinaryReduction.forget B).toIntAlgHom
    (GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom.toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem evaluation_tmul (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[ℤ] y) =
      RESOrdinaryReduction.forget B x *
        GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k y := rfl

theorem evaluation_independent_kind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k = evaluation hc h00 linear hκ hs B hr hγ hΓ l := by
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [evaluation_tmul, evaluation_tmul]
  exact congrArg (RESOrdinaryReduction.forget B x * ·)
    (RingHom.congr_fun (GammaBoundedRVProfiles.evaluation_independent_kind hc h00 linear hκ hs B hr hγ hΓ k l) y)

end DiamondIntegral.Section4.RVBoundedTensor
