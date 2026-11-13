import «section 3».MeasuredNativeTensorCharts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k r n : ℕ}

theorem gammaGroundMeasuredTensor_pure_native_normal_form {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (X : GammaGroundMeasuredRESObject hc B r) (A : GammaGroundMeasuredGammaObject hc B n)
    (hdegree : r+n = k) :
    ∃ l : List (GammaGroundMeasuredNativeTensorChart hc B k),
      gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass A =
          (l.map GammaGroundMeasuredNativeTensorChart.value).sum ∧
      ∀ Z ∈ l, Z.underlying.gammaDegree = n := by
  obtain ⟨p,hp,hpdegree⟩ := gammaGroundMeasuredTensor_pure_normalized_pieces hκ hs h00 hsmall hγsmall X A
  let Z : {t // t ∈ p} → GammaGroundMeasuredNativeTensorChart hc B k := fun t =>
    GammaGroundMeasuredNativeTensorChart.ofPiece h00 t.val
      (by obtain ⟨hr,hn⟩ := hpdegree t.val t.property; omega)
  refine ⟨p.attach.map Z,?_,?_⟩
  · rw [hp,List.map_map]
    apply congrArg List.sum
    have hz : (fun t : {t // t ∈ p} => (Z t).value) = fun t => t.val.value := by
      funext t
      exact GammaGroundMeasuredNativeTensorChart.ofPiece_value h00 t.val _
    change (p.map GammaGroundNormalizedMeasuredTensorPiece.value) = p.attach.map (fun t => (Z t).value)
    rw [hz,List.attach_map_val]
  · intro W hW
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hW
    exact (hpdegree t.val t.property).2
end DiamondIntegral.Section3
