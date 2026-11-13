import «section 3».MeasuredNativeTensorCharts
import «section 3».MeasuredNativeRESPartitions
import «section 3».MeasuredNativeGammaPartitions
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r n k : ℕ}
namespace GammaGroundTensorBox
variable {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B n}

def measuredValue (E : GammaGroundTensorBox X G)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) : GammaGroundMeasuredPositiveTensor hc B :=
  gammaGroundMeasuredRESDirectSumClass (X.restrict E.residue E.residue_subset).measured
    ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight E.gamma f hf)

def toMeasuredNativeChart (E : GammaGroundTensorBox X G) (hdegree : r+n = k)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) : GammaGroundMeasuredNativeTensorChart hc B k :=
  ⟨E.toNativeChart hdegree,f,hf⟩

@[simp] theorem toMeasuredNativeChart_value (E : GammaGroundTensorBox X G) (hdegree : r+n = k)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    (E.toMeasuredNativeChart hdegree f hf).value = E.measuredValue f hf := rfl

/-- Empty product factors contribute zero with every retained weight. -/
theorem measuredValue_eq_zero_of_not_nonempty (E : GammaGroundTensorBox X G)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (h : ¬ (E.residue.carrier.Nonempty ∧ E.gamma.carrier.Nonempty)) : E.measuredValue f hf = 0 := by
  by_cases hA : E.residue.carrier.Nonempty
  · have hG : E.gamma.carrier = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun γ hγ => h ⟨hA,⟨γ,hγ⟩⟩)
    have he : E.gamma = GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) :=
      gammaGroundDefSet_eq_of_carrier_eq hG
    unfold measuredValue
    rw [he,gammaGroundMeasuredGammaSemiringClass_single_empty,TensorProduct.tmul_zero]
  · have he : E.residue.carrier = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun a ha => hA ⟨a,ha⟩)
    unfold measuredValue
    rw [(X.restrict E.residue E.residue_subset).measured_class_of_empty he,TensorProduct.zero_tmul]
end GammaGroundTensorBox
end DiamondIntegral.Section3
