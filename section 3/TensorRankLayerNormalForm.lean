import «section 3».NativeTensorListAtlas
import «section 3».TensorRankZero
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m : ℕ}

def GammaGroundNativeTensorChart.asPiece (Z : GammaGroundNativeTensorChart hc B k) : GammaGroundUnmeasuredTensorPiece hc B :=
  ⟨Z.residueDegree,Z.gammaDegree,Z.residue.object,Z.gamma⟩

@[simp] theorem GammaGroundNativeTensorChart.asPiece_value (Z : GammaGroundNativeTensorChart hc B k) :
    Z.asPiece.value = Z.value := rfl

theorem gammaGroundNativeTensor_rank_zero_kernel_trivial
    (l q : List (GammaGroundNativeTensorChart hc B k))
    (hl : ∀ Z ∈ l, Z.gammaDegree ≤ 0) (hq : ∀ Z ∈ q, Z.gammaDegree ≤ 0)
    (h : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundNativeTensorChart.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundNativeTensorChart.value).sum)) :
    (l.map GammaGroundNativeTensorChart.value).sum = (q.map GammaGroundNativeTensorChart.value).sum := by
  have hl' : ∀ t ∈ l.map GammaGroundNativeTensorChart.asPiece, t.gammaDegree = 0 := by
    intro t ht
    obtain ⟨Z,hZ,rfl⟩ := List.mem_map.mp ht
    exact Nat.eq_zero_of_le_zero (hl Z hZ)
  have hq' : ∀ t ∈ q.map GammaGroundNativeTensorChart.asPiece, t.gammaDegree = 0 := by
    intro t ht
    obtain ⟨Z,hZ,rfl⟩ := List.mem_map.mp ht
    exact Nat.eq_zero_of_le_zero (hq Z hZ)
  have h' : gammaGroundUnmeasuredTensorMap
      (((l.map GammaGroundNativeTensorChart.asPiece).map GammaGroundUnmeasuredTensorPiece.value).sum) =
      gammaGroundUnmeasuredTensorMap
      (((q.map GammaGroundNativeTensorChart.asPiece).map GammaGroundUnmeasuredTensorPiece.value).sum) := by
    simpa only [List.map_map,Function.comp_def,GammaGroundNativeTensorChart.asPiece_value] using h
  simpa only [List.map_map,Function.comp_def,GammaGroundNativeTensorChart.asPiece_value] using gammaGroundTensor_rank_zero_kernel_trivial _ _ hl' hq' h'

/-- At maximal free arity m, total degree k fixes the RES label to k-m.
This changes only the presentation of the existing object data. -/
theorem gammaGroundNativeTensorChart_top_normalize (Z : GammaGroundNativeTensorChart hc B k)
    (h : Z.gammaDegree = m) :
    ∃ X : GammaGroundRESUnitChart hc B (k-m), ∃ G : GammaGroundGammaPiece hc B m,
      Z.value = gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) := by
  rcases Z with ⟨r,n,hdegree,X,G⟩
  change n = m at h
  subst n
  have hr : r = k-m := by omega
  subst r
  exact ⟨X,G,rfl⟩

/-- Maximal-rank products have a common RES degree. The remaining native
charts already have strictly smaller free Gamma arity. -/
structure GammaGroundTensorRankLayer (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (k m : ℕ) where
  within_degree : m ≤ k
  topCount : ℕ
  residue : Fin topCount → GammaGroundRESUnitChart hc B (k-m)
  gamma : Fin topCount → GammaGroundGammaPiece hc B m
  lower : List (GammaGroundNativeTensorChart hc B k)
  lower_rank : ∀ Z ∈ lower, Z.gammaDegree < m

namespace GammaGroundTensorRankLayer

def value (L : GammaGroundTensorRankLayer hc B k m) : GammaGroundUnmeasuredPositiveTensor hc B :=
  (∑ i, gammaGroundRESDirectSumClass (L.residue i).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (L.gamma i))) +
      (L.lower.map GammaGroundNativeTensorChart.value).sum

def topChart (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.topCount) : GammaGroundNativeTensorChart hc B k :=
  ⟨k-m,m,Nat.sub_add_cancel L.within_degree,L.residue i,L.gamma i⟩

def charts (L : GammaGroundTensorRankLayer hc B k m) : List (GammaGroundNativeTensorChart hc B k) :=
  List.ofFn L.topChart ++ L.lower

theorem value_charts (L : GammaGroundTensorRankLayer hc B k m) :
    L.value = (L.charts.map GammaGroundNativeTensorChart.value).sum := by
  rw [charts,List.map_append,List.sum_append,List.map_ofFn,List.sum_ofFn]
  rfl

theorem charts_rank_bound (L : GammaGroundTensorRankLayer hc B k m) : ∀ Z ∈ L.charts, Z.gammaDegree ≤ m := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hZ
    exact Nat.le_refl m
  · exact Nat.le_of_lt (L.lower_rank Z hZ)
end GammaGroundTensorRankLayer

/-- Split a homogeneous positive normal form into its maximal Gamma
rank layer and a strictly lower-rank remainder, using positive sums. -/
theorem gammaGroundNativeTensor_rank_layer_normal_form
    (l : List (GammaGroundNativeTensorChart hc B k)) (hbound : m ≤ k)
    (hl : ∀ Z ∈ l, Z.gammaDegree ≤ m) :
    ∃ L : GammaGroundTensorRankLayer hc B k m,
      (l.map GammaGroundNativeTensorChart.value).sum = L.value := by
  induction l with
  | nil =>
    refine ⟨⟨hbound,0,Fin.elim0,Fin.elim0,[],by intro Z hZ; exact False.elim (List.not_mem_nil hZ)⟩,?_⟩
    simp [GammaGroundTensorRankLayer.value]
  | cons Z l ih =>
    obtain ⟨L,hL⟩ := ih (fun W hW => hl W (List.mem_cons_of_mem Z hW))
    by_cases hZ : Z.gammaDegree = m
    · obtain ⟨X,G,hvalue⟩ := gammaGroundNativeTensorChart_top_normalize Z hZ
      let R : GammaGroundTensorRankLayer hc B k m :=
        ⟨hbound,L.topCount+1,Fin.cases X L.residue,Fin.cases G L.gamma,L.lower,L.lower_rank⟩
      refine ⟨R,?_⟩
      change Z.value+(l.map GammaGroundNativeTensorChart.value).sum = _
      rw [hvalue,hL]
      dsimp only [R,GammaGroundTensorRankLayer.value]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero,Fin.cases_succ]
      exact (add_assoc _ _ _).symm
    · have hlt : Z.gammaDegree < m := by have hle := hl Z (List.mem_cons_self ..); omega
      let R : GammaGroundTensorRankLayer hc B k m :=
        ⟨hbound,L.topCount,L.residue,L.gamma,Z::L.lower,by
          intro W hW
          rcases List.mem_cons.mp hW with rfl | hW
          · exact hlt
          · exact L.lower_rank W hW⟩
      refine ⟨R,?_⟩
      change Z.value+(l.map GammaGroundNativeTensorChart.value).sum = _
      rw [hL]
      exact add_left_comm _ _ _
end DiamondIntegral.Section3
