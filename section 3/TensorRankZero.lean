import «section 3».TensorPieceNormalForm
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

/-- The RES factor already embeds positively in the tensor, as witnessed
by its actual positive embedding in RV. -/
theorem gammaGroundUnmeasuredTensor_RES_injective :
    Function.Injective (fun a : GammaGroundRESDirectSum hc B =>
      a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] (1 : GammaGroundGammaPositiveSemiring hc B)) := by
  intro a b h
  apply gammaGroundRESToRVSemiring_injective
  have he := congrArg (gammaGroundUnmeasuredTensorMap (hc := hc) (ground := B)) h
  simpa only [gammaGroundUnmeasuredTensorMap_tmul,map_one,mul_one] using he

/-- Rank-zero native Gamma factors are actual finite Gamma objects and
are absorbed by positive balancing with their full grading retained. -/
theorem gammaGroundTensorPiece_rank_zero_absorption (t : GammaGroundUnmeasuredTensorPiece hc B)
    (ht : t.gammaDegree = 0) :
    ∃ a : GammaGroundRESDirectSum hc B,
      t.value = a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] (1 : GammaGroundGammaPositiveSemiring hc B) := by
  rcases t with ⟨r,n,X,G⟩
  change n = 0 at ht
  subst n
  have hG : G.carrier.Finite := by
    apply Set.Subsingleton.finite
    intro a _ b _
    change Fin 0 → Values.Gamma (M := M) at a b
    exact Subsingleton.elim a b
  let F : GammaGroundFiniteGammaObject hc B 0 := ⟨GammaGroundGammaObject.single G,fun _ => hG⟩
  refine ⟨gammaGroundRESDirectSumClass (X.product F.resLift),?_⟩
  have h := gammaGroundUnmeasuredTensor_finite_factor_absorption X F (GammaGroundGammaObject.unit hc B)
  simpa only [GammaGroundUnmeasuredTensorPiece.value,GammaGroundUnmeasuredTensorPiece.asTerm,
    GammaGroundUnmeasuredTensorTerm.value,gammaGroundGammaSemiringClass_unit,mul_one] using h

theorem gammaGroundTensorList_rank_zero_absorption (l : List (GammaGroundUnmeasuredTensorPiece hc B))
    (hl : ∀ t ∈ l, t.gammaDegree = 0) :
    ∃ a : GammaGroundRESDirectSum hc B,
      (l.map GammaGroundUnmeasuredTensorPiece.value).sum =
        a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] (1 : GammaGroundGammaPositiveSemiring hc B) := by
  induction l with
  | nil => exact ⟨0,(TensorProduct.zero_tmul _ _).symm⟩
  | cons t l ih =>
    obtain ⟨a,ha⟩ := gammaGroundTensorPiece_rank_zero_absorption t (hl t (List.mem_cons_self ..))
    obtain ⟨b,hb⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem t hu))
    refine ⟨a+b,?_⟩
    change t.value+(l.map GammaGroundUnmeasuredTensorPiece.value).sum = _
    rw [ha,hb,TensorProduct.add_tmul]

/-- The rank induction starts with equality in the positive tensor itself
when every remaining free Gamma arity is zero. -/
theorem gammaGroundTensor_rank_zero_kernel_trivial
    (l q : List (GammaGroundUnmeasuredTensorPiece hc B))
    (hl : ∀ t ∈ l, t.gammaDegree = 0) (hq : ∀ t ∈ q, t.gammaDegree = 0)
    (h : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundUnmeasuredTensorPiece.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundUnmeasuredTensorPiece.value).sum)) :
    (l.map GammaGroundUnmeasuredTensorPiece.value).sum = (q.map GammaGroundUnmeasuredTensorPiece.value).sum := by
  obtain ⟨a,ha⟩ := gammaGroundTensorList_rank_zero_absorption l hl
  obtain ⟨b,hb⟩ := gammaGroundTensorList_rank_zero_absorption q hq
  rw [ha,hb] at h
  have he : gammaGroundRESToRVSemiring a = gammaGroundRESToRVSemiring b := by
    simpa only [gammaGroundUnmeasuredTensorMap_tmul,map_one,mul_one] using h
  have hab := gammaGroundRESToRVSemiring_injective he
  rw [ha,hb,hab]
end DiamondIntegral.Section3
