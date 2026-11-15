import «section 5».Completed18LocalLift
import «section 5».Completed18RVSpecialRelation
import «section 5».Completed18NativePositiveKernel

/-! Exact kernel on the local positive semirings, with [18]'s two-order
input discharged by completed proofs and its elementary relation identified. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {κ : Cardinal}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

theorem completed18LocalLift_kernel (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
    (hγ : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ∈B.gamma) (hδ1 : 1<δ)
    (hB : VFGammaGeneratedBase B) :
    gammaGroundRVSpecialCongruence hc B=RingCon.ker (completed18LocalLift hκ.le hs h00 hr hB) := by
  ext x y
  rw [completed18RVSpecial_iff,completed18NativePositiveLift_kernel hκ hs h00 hr FBase hγ δ hδ hδ1 hB]
  change gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB (completed18RVPositiveEquiv x)=
    gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB (completed18RVPositiveEquiv y) ↔
      nativeVFPositiveGround (gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB (completed18RVPositiveEquiv x))=
      nativeVFPositiveGround (gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB (completed18RVPositiveEquiv y))
  exact (completed18VFPositiveEquiv (hc := hc) (B := B)).symm.injective.eq_iff.symm

end DiamondIntegral.Section5
