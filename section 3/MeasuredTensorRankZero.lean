import «section 3».MeasuredNativeRESPartitions
import «section 3».MeasuredNativeTensorCharts
import «section 3».TensorFiniteFactorAbsorption
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

/-- At free Gamma arity zero, the actual finite measured Gamma object
and all of its weight are absorbed into measured RES by positive balancing. -/
theorem gammaGroundMeasuredNativeTensor_rank_zero_absorption
    (Z : GammaGroundMeasuredNativeTensorChart hc B k) (hZ : Z.underlying.gammaDegree = 0) :
    ∃ a : GammaGroundMeasuredRESDirectSum hc B,
      Z.value = a ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        (1 : GammaGroundMeasuredGammaPositiveSemiring hc B) := by
  rcases Z with ⟨⟨r,n,hdegree,X,G⟩,f,hf⟩
  change n = 0 at hZ
  subst n
  let A := gammaGroundMeasuredGammaSingleWeight G f hf
  let F : GammaGroundMeasuredFiniteGammaObject hc B 0 := ⟨A,A.underlying.degree_zero_finite⟩
  refine ⟨gammaGroundMeasuredRESDirectSumClass (X.measured.product F.resLift),?_⟩
  change gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass A = _
  have h := gammaGroundMeasuredTensor_finite_factor_absorption X.measured F (GammaGroundMeasuredGammaObject.unit hc B)
  simpa only [gammaGroundMeasuredGammaSemiringClass_unit,mul_one] using h

theorem gammaGroundMeasuredNativeTensorList_rank_zero_absorption
    (l : List (GammaGroundMeasuredNativeTensorChart hc B k))
    (hl : ∀ Z ∈ l, Z.underlying.gammaDegree = 0) :
    ∃ a : GammaGroundMeasuredRESDirectSum hc B,
      (l.map GammaGroundMeasuredNativeTensorChart.value).sum =
        a ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          (1 : GammaGroundMeasuredGammaPositiveSemiring hc B) := by
  induction l with
  | nil => exact ⟨0,(TensorProduct.zero_tmul _ _).symm⟩
  | cons Z l ih =>
    obtain ⟨a,ha⟩ := gammaGroundMeasuredNativeTensor_rank_zero_absorption Z (hl Z (List.mem_cons_self ..))
    obtain ⟨b,hb⟩ := ih (fun W hW => hl W (List.mem_cons_of_mem Z hW))
    refine ⟨a+b,?_⟩
    change Z.value+(l.map GammaGroundMeasuredNativeTensorChart.value).sum = _
    rw [ha,hb,TensorProduct.add_tmul]

theorem gammaGroundMeasuredNativeTensor_rank_zero_kernel_trivial
    (l q : List (GammaGroundMeasuredNativeTensorChart hc B k))
    (hl : ∀ Z ∈ l, Z.underlying.gammaDegree ≤ 0) (hq : ∀ Z ∈ q, Z.underlying.gammaDegree ≤ 0)
    (h : gammaGroundMeasuredTensorMap ((l.map GammaGroundMeasuredNativeTensorChart.value).sum) =
      gammaGroundMeasuredTensorMap ((q.map GammaGroundMeasuredNativeTensorChart.value).sum)) :
    (l.map GammaGroundMeasuredNativeTensorChart.value).sum = (q.map GammaGroundMeasuredNativeTensorChart.value).sum := by
  obtain ⟨a,ha⟩ := gammaGroundMeasuredNativeTensorList_rank_zero_absorption l (fun Z hZ => Nat.eq_zero_of_le_zero (hl Z hZ))
  obtain ⟨b,hb⟩ := gammaGroundMeasuredNativeTensorList_rank_zero_absorption q (fun Z hZ => Nat.eq_zero_of_le_zero (hq Z hZ))
  rw [ha,hb] at h
  have he : gammaGroundMeasuredRESToRVSemiring a = gammaGroundMeasuredRESToRVSemiring b := by
    simpa only [gammaGroundMeasuredTensorMap_tmul,map_one,mul_one] using h
  have hab := gammaGroundMeasuredRESToRVSemiring_injective he
  rw [ha,hb,hab]
end DiamondIntegral.Section3
